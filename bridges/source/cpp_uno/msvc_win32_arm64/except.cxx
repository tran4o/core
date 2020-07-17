/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */
/*
 * This file is part of the LibreOffice project.
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * This file incorporates work covered by the following license notice:
 *
 *   Licensed to the Apache Software Foundation (ASF) under one or more
 *   contributor license agreements. See the NOTICE file distributed
 *   with this work for additional information regarding copyright
 *   ownership. The ASF licenses this file to you under the Apache
 *   License, Version 2.0 (the "License"); you may not use this file
 *   except in compliance with the License. You may obtain a copy of
 *   the License at http://www.apache.org/licenses/LICENSE-2.0 .
 */

#include <sal/config.h>

#include <memory>

#include <malloc.h>
#include <new.h>
#include <typeinfo>
#include <signal.h>

#include <rtl/alloc.h>
#include <rtl/strbuf.hxx>
#include <rtl/ustrbuf.hxx>
#include <sal/log.hxx>

#include <com/sun/star/uno/Any.hxx>
#include <msvc/arm64.hxx>
#include <except.hxx>

#pragma pack(push, 8)

using namespace ::com::sun::star;

static void * __cdecl copyConstruct(
    void * pExcThis,
    void * pSource,
    typelib_TypeDescription * pTD ) throw ()
{
    ::uno_copyData(pExcThis, pSource, pTD, uno::cpp_acquire);
    return pExcThis;
}

static void * __cdecl destruct(
    void * pExcThis,
    typelib_TypeDescription * pTD ) throw ()
{
    ::uno_destructData(pExcThis, pTD, uno::cpp_release);
    return pExcThis;
}

const int codeSnippetSize = 40;

static void GenerateConstructorTrampoline(
    unsigned char * code,
    typelib_TypeDescription * pTD ) throw ()
{
    unsigned char *p = code;

    // mov r8, pTD
    *p++ = 0x49; *p++ = 0xB8;
    *reinterpret_cast<void **>(p) = pTD; p += 8;

    // mov r11, copyConstruct
    *p++ = 0x49; *p++ = 0xBB;
    *reinterpret_cast<void **>(p) = reinterpret_cast<void *>(&copyConstruct); p += 8;

    // jmp r11
    *p++ = 0x41; *p++ = 0xFF; *p++ = 0xE3;

    assert( p < code + codeSnippetSize );
}

static void GenerateDestructorTrampoline(
    unsigned char * code,
    typelib_TypeDescription * pTD ) throw ()
{
    unsigned char *p = code;

    // mov rdx, pTD
    *p++ = 0x48; *p++ = 0xBA;
    *reinterpret_cast<void **>(p) = pTD; p += 8;

    // mov r11, destruct
    *p++ = 0x49; *p++ = 0xBB;
    *reinterpret_cast<void **>(p) = reinterpret_cast<void *>(&destruct); p += 8;

    // jmp r11
    *p++ = 0x41; *p++ = 0xFF; *p++ = 0xE3;

    assert( p < code + codeSnippetSize );
}

ExceptionType::ExceptionType(unsigned char * pCode, sal_uInt64 pCodeBase,
                             typelib_TypeDescription * pTD) throw ()
    : _n0(0)
    , _n1(0)
    , _n2(-1)
    , _n3(0)
    , _n4(pTD->nSize)
    , exc_type_info(nullptr, "")
{
    // As _n0 is always initialized to zero, that means the
    // hasvirtbase flag (see the ONTL catchabletype struct) is
    // off, and thus the copyctor is of the ctor_ptr kind.

    int len;
    type_info* pRTTI = RTTInfos::get(pTD->pTypeName, &len);

    memcpy(static_cast<void*>(&exc_type_info), static_cast<void*>(pRTTI), len);
    _pTypeInfo = static_cast<sal_uInt32>(reinterpret_cast<sal_uInt64>(&exc_type_info) - pCodeBase);
    GenerateConstructorTrampoline(pCode, pTD);

    assert(pCodeBase <= reinterpret_cast<sal_uInt64>(pCode)
           && (reinterpret_cast<sal_uInt64>(pCode) - pCodeBase < 0x100000000));
    _pCopyCtor = static_cast<sal_uInt32>(reinterpret_cast<sal_uInt64>(pCode) - pCodeBase);
}

/* Rewrite of 32-Bit-Code to work under 64 Bit:
* To use the 32 Bit offset values in the ExceptionType we have to
* allocate a single allocation block and use it for all code and date
* all offsets inside this area are guaranteed to be in 32 bit address range.
* So we have to calc total memory allocation size for D-tor, C-Tors,
* ExceptionType and type_info. ExceptionType is allocated via placement new
* to locate everything inside our mem block.
* There is one caveat: Struct type_info is kept in
* a map and was referenced from class ExceptionType. Therefore type_info now
* is also member of ExceptionType and can be referenced via 32 bit offset.
*/

RaiseInfo::RaiseInfo(typelib_TypeDescription * pTD)throw ()
    : _n0(0)
    , _n2(0)
    , _pTD(pTD)
{
    typelib_CompoundTypeDescription * pCompTD;

    // Count how many trampolines we need
    int codeSize = codeSnippetSize;

    // Info count
    int nLen = 0;
    for (pCompTD = reinterpret_cast<typelib_CompoundTypeDescription*>(pTD);
        pCompTD; pCompTD = pCompTD->pBaseTypeDescription)
    {
        ++nLen;
        codeSize += codeSnippetSize;
    }

    // Array with size (4) and all _pTypeInfo (4*nLen)
    int typeInfoArraySize = 4 + 4 * nLen;

    // 2.Pass: Get the total needed memory for class ExceptionType
    // (with embedded type_info) and keep the sizes for each instance
    // is stored in allocated int array
    auto exceptionTypeSizeArray = std::make_unique<int[]>(nLen);

    nLen = 0;
    for (pCompTD = reinterpret_cast<typelib_CompoundTypeDescription*>(pTD);
        pCompTD; pCompTD = pCompTD->pBaseTypeDescription)
    {
        int typeInfoLen;
        RTTInfos::get(pCompTD->aBase.pTypeName, &typeInfoLen);
        // Mem has to be on 4-byte Boundary
        if (typeInfoLen % 4 != 0)
        {
            int n = typeInfoLen / 4;
            n++;
            typeInfoLen = n*4;
        }
        exceptionTypeSizeArray[nLen++] = typeInfoLen + sizeof(ExceptionType);
    }

    // Total ExceptionType related mem
    int excTypeAddLen = 0;
    for (int i = 0; i < nLen; i++)
    {
        excTypeAddLen += exceptionTypeSizeArray[i];
    }

    // Allocate mem for code and all dynamic data in one chunk to guarantee
    // 32 bit offsets
    const int totalSize = codeSize + typeInfoArraySize + excTypeAddLen;
    unsigned char * pCode = _code =
        static_cast<unsigned char *>(std::malloc(totalSize));
    int pCodeOffset = 0;

    // New base of types array, starts after Trampoline D-Tor / C-Tors
    DWORD * types = reinterpret_cast<DWORD *>(pCode + codeSize);

    // New base of ExceptionType array, starts after types array
    unsigned char *etMem = pCode + codeSize + typeInfoArraySize;
    int etMemOffset = 0;

    _codeBase = reinterpret_cast<sal_uInt64>(pCode)
        & ~static_cast<sal_uInt64>(ExceptionInfos::allocationGranularity - 1);

    DWORD old_protect;
    bool success =
        VirtualProtect(pCode, codeSize, PAGE_EXECUTE_READWRITE, &old_protect);
    (void) success;
    assert(success && "VirtualProtect() failed!");

    ::typelib_typedescription_acquire(pTD);

    // Fill pCode with D-Tor code
    GenerateDestructorTrampoline(pCode, pTD);
    _pDtor = static_cast<sal_Int32>(reinterpret_cast<sal_uInt64>(pCode) - _codeBase);
    pCodeOffset += codeSnippetSize;

    // Info count accompanied by type info ptrs: type, base type, base base type, ...
    // Keep offset of types_array
    _types = static_cast<sal_Int32>(
        reinterpret_cast<sal_uInt64>(types)-_codeBase);
    // Fill types: (nLen, _offset to ExceptionType1, ...ExceptionType2, ...)
    types[0] = nLen;

    int nPos = 1;
    for (pCompTD = reinterpret_cast<typelib_CompoundTypeDescription*>(pTD);
        pCompTD; pCompTD = pCompTD->pBaseTypeDescription)
    {
        // Create instance in mem block with placement new
        ExceptionType * et = new(etMem + etMemOffset)ExceptionType(
            pCode + pCodeOffset, _codeBase, reinterpret_cast<typelib_TypeDescription *>(pCompTD));

        // Next trampoline entry offset
        pCodeOffset += codeSnippetSize;
        // Next ExceptionType placement offset
        etMemOffset += exceptionTypeSizeArray[nPos - 1];

        // Keep offset of addresses of ET for D-Tor call in ~RaiseInfo
        types[nPos++]
            = static_cast<DWORD>(reinterpret_cast<sal_uInt64>(et)-_codeBase);
    }
    // Final check: end of address calculation must be end of mem
    assert(etMem + etMemOffset == pCode + totalSize);
}

#pragma pack(pop)

/* vim:set shiftwidth=4 softtabstop=4 expandtab: */
