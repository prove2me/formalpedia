-- Prove2me | Definitions.Def_Arm64_ISA_Decode
-- name    : Arm64_ISA_Decode
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:02:19.04829+00:00
-- url     : https://prove2.me/theorems/6212900f-99df-40df-aff2-e49041305006
-- title:
--   Arm64.Trusted.ISA.Decode — AArch64 32-Bit Machine Instruction Decoder
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/Decode.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Decode.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/Decode.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Decode.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/Decode.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also 14 interpolated strings written out as their elaboration `toString … ++ …`, because prove2.me rejects interpolated strings.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Syntax

/-!
# `Arm64.Trusted.ISA.Decode`: AArch64 32-Bit Machine Instruction Decoder

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**:
  - `Arm64.decode`: partial decoder `BitVec 32 → Option Instr` mapping 32-bit little-endian
    A64 instruction words to the `Instr` AST in `Arm64.Trusted.ISA.Syntax` (or `none` for
    unallocated, architecturally `UNDEFINED`, or unmodeled encodings).
  - `Arm64.decodeBitMasks` / `decodeBitMasksValid` / `decodeBitMasksVal`: ARM's `DecodeBitMasks`
    logical-immediate bitmask decoder (`N:imms:immr` → `Option (BitVec 64)`).
  - `Arm64.describeUnsupportedWord` / `describeUnsupportedAt`: diagnostic classifier for
    unsupported 32-bit encodings.
- **Trust & Assumptions**: Part of the TCB (`Arm64/Trusted/`). Validated against the untrusted
  instruction encoder (`Arm64/Testing/Harness/Encode.lean`) and against Sail (`armv9.4-a`) and
  Unicorn (`UC_ARCH_ARM64`) in lockstep differential testing (`run-trusted-tests`).
- **When to read**: Read when adding or auditing instruction bit-patterns or architectural
  `UNDEFINED` / `CONSTRAINED UNPREDICTABLE` decode guards.
-/

@[expose] public section

namespace Arm64

/-!
## Bitmask Immediate Decoding (`DecodeBitMasks`)
-/

/-- Compute the `levels` bitmask (`esize - 1`, i.e. `1`, `3`, `7`, `15`, `31`, or `63`)
    from `(immN, imms)` by finding the highest clear bit of `immN : ~~~imms`.
    Corresponds to `HighestSetBit(immN:NOT(imms))` in ARM's `DecodeBitMasks` pseudocode:
    returns `0` when `len < 1` (i.e. `immN = 0` and `imms = 0b11111x`, which is `UNDEFINED`). -/
def decodeBitMasksLevels (immN : Bool) (imms : BitVec 6) : BitVec 6 :=
  if immN then 63#6
  else if !(imms.getLsbD 5) then 31#6
  else if !(imms.getLsbD 4) then 15#6
  else if !(imms.getLsbD 3) then 7#6
  else if !(imms.getLsbD 2) then 3#6
  else if !(imms.getLsbD 1) then 1#6
  else 0#6

/-- Validity predicate for `(immN, imms, immr)` in A64 logical-immediate instructions:
    1. `levels != 0` (`len >= 1` in `HighestSetBit(immN:NOT(imms))`);
    2. `S != levels` (the all-ones element `S = esize - 1` is reserved);
    3. `(immr &&& ~~~levels) == 0` (canonical rotation `immr < esize`, so each encodable
       64-bit bitmask has a unique `(immN, imms, immr)` representation). -/
def decodeBitMasksValid (immN : Bool) (imms immr : BitVec 6) : Bool :=
  let levels := decodeBitMasksLevels immN imms
  let s := imms &&& levels
  s != levels && (immr &&& ~~~levels) == 0#6

/-- Mask construction half of ARM's `DecodeBitMasks`, assuming `decodeBitMasksValid`.

    Builds `S + 1` consecutive ones inside an `esize`-bit element (`esize = levels + 1`),
    rotates that element right by `R`, and then replicates it across all 64 bits by the
    usual doubling chain (`2 -> 4 -> 8 -> 16 -> 32 -> 64`). The result is the `WMask` of the
    ARM pseudocode; `TMask` is not needed because A64 logical immediates only use `WMask`.

    The value returned for an invalid `(immN, imms, immr)` is unspecified; callers should
    go through `decodeBitMasks`. -/
def decodeBitMasksVal (immN : Bool) (imms immr : BitVec 6) : BitVec 64 :=
  let levels := decodeBitMasksLevels immN imms
  let s : BitVec 6 := imms &&& levels
  let r : BitVec 6 := immr &&& levels
  let elemOnes : BitVec 64 := (2#64 <<< s.zeroExtend 64) - 1#64
  let elemMask : BitVec 64 := (2#64 <<< levels.zeroExtend 64) - 1#64
  let elemRotated : BitVec 64 :=
    if r == 0#6 then elemOnes
    else
      let shlAmt : BitVec 6 := (levels - r) + 1#6
      ((elemOnes >>> r.zeroExtend 64) ||| (elemOnes <<< shlAmt.zeroExtend 64)) &&& elemMask
  let r2  := if levels.ule 1#6  then elemRotated ||| (elemRotated <<< 2#64)  else elemRotated
  let r4  := if levels.ule 3#6  then r2  ||| (r2  <<< 4#64)  else r2
  let r8  := if levels.ule 7#6  then r4  ||| (r4  <<< 8#64)  else r4
  let r16 := if levels.ule 15#6 then r8  ||| (r8  <<< 16#64) else r8
  if levels.ule 31#6 then r16 ||| (r16 <<< 32#64) else r16

/-- ARM's `DecodeBitMasks` as a partial function: decode a logical-immediate encoding
    `(N, imms, immr)` into the 64-bit replicated bitmask it denotes, or `none` if the
    encoding is `UNDEFINED`. Inverse of `Arm64.encodeBitMasks`. -/
def decodeBitMasks (immN : Bool) (imms immr : BitVec 6) : Option (BitVec 64) :=
  if decodeBitMasksValid immN imms immr then
    some (decodeBitMasksVal immN imms immr)
  else
    none

/-!
## Load/Store Sub-Decoders
-/

/-- Construct a general-purpose single-register load/store `Instr` (`Instr.ldr` or `Instr.str`)
    from `sizeBits` (`bits[31:30]`), `opc` (`bits[23:22]`), target register `rt`, and `addr : AddrMode`. -/
def mkLoadStoreInst (sizeBits opc : Nat) (rt : Reg) (addr : AddrMode) : Option Instr :=
  match sizeBits, opc with
  | 0, 0 => some (.str .B8 rt addr)
  | 0, 1 => some (.ldr .W32 .B8 false rt addr)
  | 0, 2 => some (.ldr .W64 .B8 true rt addr)
  | 0, 3 => some (.ldr .W32 .B8 true rt addr)
  | 1, 0 => some (.str .H16 rt addr)
  | 1, 1 => some (.ldr .W32 .H16 false rt addr)
  | 1, 2 => some (.ldr .W64 .H16 true rt addr)
  | 1, 3 => some (.ldr .W32 .H16 true rt addr)
  | 2, 0 => some (.str .W32 rt addr)
  | 2, 1 => some (.ldr .W32 .W32 false rt addr)
  | 2, 2 => some (.ldr .W64 .W32 true rt addr)
  | 3, 0 => some (.str .X64 rt addr)
  | 3, 1 => some (.ldr .W64 .X64 false rt addr)
  | _, _ => none

/-- Decode `(sizeBits, opc)` for a SIMD/FP single-register load/store into `(isLoad, sz, scale)`. -/
def decodeSimdLoadStoreType (sizeBits opc : Nat) : Option (Bool × SimdMemSize × Nat) :=
  match sizeBits, opc with
  | 0, 0 => some (false, .B8,   0)
  | 0, 1 => some (true,  .B8,   0)
  | 0, 2 => some (false, .Q128, 4)
  | 0, 3 => some (true,  .Q128, 4)
  | 1, 0 => some (false, .H16,  1)
  | 1, 1 => some (true,  .H16,  1)
  | 2, 0 => some (false, .S32,  2)
  | 2, 1 => some (true,  .S32,  2)
  | 3, 0 => some (false, .D64,  3)
  | 3, 1 => some (true,  .D64,  3)
  | _, _ => none

/-!
## Main 32-Bit Instruction Decoder (`decode`)
-/

/-- Decode a 32-bit little-endian AArch64 machine word into `Option Instr`. -/
def decode (w : BitVec 32) : Option Instr :=
  let sf := w.getLsbD 31
  let width : RegWidth := RegWidth.ofBool sf

  -- 1. NOP (0xd503201f)
  if w == 0xd503201f#32 then
    some .nop

  -- 2. Exception Generation: SVC #imm16 (0xd4000001 | imm16 << 5) / BRK #imm16 (0xd4200000 | imm16 << 5)
  else if (w &&& 0xffe0001f#32) == 0xd4000001#32 then
    some (.system false (w.extractLsb' 5 16))
  else if (w &&& 0xffe0001f#32) == 0xd4200000#32 then
    some (.system true (w.extractLsb' 5 16))

  -- 2b. Non-NOP `HINT #imm` (`11010101000000110010:CRm:op2:11111`, `CRm:op2 != 0`).
  else if (w &&& 0xfffff01f#32) == 0xd503201f#32 then
    some (.hint (w.extractLsb' 5 7))

  -- 2c. Permanently undefined `UDF #imm16` (`0x0000xxxx`), except the all-zero word
  -- `UDF #0`, which stays undecodable: zero-filled extern-stub slots and padding rely on
  -- `decode 0 = none` (both outcomes stop execution, so this loses no behaviour).
  else if (w &&& 0xffff0000#32) == 0x00000000#32 && w != 0#32 then
    some (.udf (w.extractLsb' 0 16))

  -- 2d. `DC ZVA, Xt` (`0xd50b7420 | Rt`).
  else if (w &&& 0xffffffe0#32) == 0xd50b7420#32 then
    some (.dcZva (Reg.fromZRBits (w.extractLsb' 0 5)))

  -- 3. PC-rel. addressing: ADR / ADRP (bits[28:24] == 10000)
  else if (w &&& 0x1f000000#32) == 0x10000000#32 then
    let page := w.getLsbD 31
    let immlo : BitVec 2 := w.extractLsb' 29 2
    let immhi : BitVec 19 := w.extractLsb' 5 19
    let imm21 : BitVec 21 := immhi ++ immlo
    let offset : BitVec 64 :=
      if page then (imm21.signExtend 64) <<< 12
      else imm21.signExtend 64
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.adr page rd offset)

  -- 4. Add/subtract (immediate): bits[28:23] == 100010
  else if (w &&& 0x1f800000#32) == 0x11000000#32 then
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let sh := w.getLsbD 22
    let imm12 : BitVec 12 := w.extractLsb' 10 12
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rdBits := w.extractLsb' 0 5
    let rd := if op.setsFlags then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
    some (.addSubImm width op rd rn imm12 sh)

  -- 5. Logical (immediate): bits[28:23] == 100100
  else if (w &&& 0x1f800000#32) == 0x12000000#32 then
    let opc := w.extractLsb' 29 2
    let immN := w.getLsbD 22
    let immr : BitVec 6 := w.extractLsb' 16 6
    let imms : BitVec 6 := w.extractLsb' 10 6
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rdBits := w.extractLsb' 0 5
    if !sf && immN then
      none
    else
      match decodeBitMasks immN imms immr with
      | none => none
      | some mask =>
        let op := LogicalOp.ofBits opc false
        let rd := if opc == 3#2 then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
        some (.logicalImm width op rd rn mask)

  -- 6. Move wide (immediate): bits[28:23] == 100101
  else if (w &&& 0x1f800000#32) == 0x12800000#32 then
    let opc := (w.extractLsb' 29 2).toNat
    let hwBits := (w.extractLsb' 21 2).toNat
    let imm16 : BitVec 16 := w.extractLsb' 5 16
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if !sf && hwBits >= 2 then
      none
    else
      let hw := hwBits * 16
      match opc with
      | 0 => some (.moveWide width .MOVN rd imm16 hw)
      | 2 => some (.moveWide width .MOVZ rd imm16 hw)
      | 3 => some (.moveWide width .MOVK rd imm16 hw)
      | _ => none

  -- 7. Bitfield: bits[28:23] == 100110
  else if (w &&& 0x1f800000#32) == 0x13000000#32 then
    let opc := (w.extractLsb' 29 2).toNat
    let nBit := w.getLsbD 22
    let immr := (w.extractLsb' 16 6).toNat
    let imms := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if sf != nBit then
      none
    else if !sf && (immr >= 32 || imms >= 32) then
      none
    else
      match opc with
      | 0 => some (.bitfield width .SBFM rd rn immr imms)
      | 1 => some (.bitfield width .BFM  rd rn immr imms)
      | 2 => some (.bitfield width .UBFM rd rn immr imms)
      | _ => none

  -- 8. Extract: bits[30:23] == 00100111 and bit[21] == 0
  else if (w &&& 0x7f800000#32) == 0x13800000#32 then
    let nBit := w.getLsbD 22
    let o0 := w.getLsbD 21
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let imms := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if sf != nBit || o0 || (!sf && imms >= 32) then
      none
    else
      some (.extr width rd rn rm imms)

  -- 9. Unconditional branch (immediate): B / BL (bits[30:26] == 00101)
  else if (w &&& 0x7c000000#32) == 0x14000000#32 then
    let isBl := w.getLsbD 31
    let imm26 : BitVec 26 := w.extractLsb' 0 26
    let offset : BitVec 64 := (imm26.signExtend 64) <<< 2
    if isBl then
      some (.bl offset)
    else
      some (.b offset)

  -- 10. Compare and branch (immediate): CBZ / CBNZ (bits[30:25] == 011010)
  else if (w &&& 0x7e000000#32) == 0x34000000#32 then
    let isNonZero := w.getLsbD 24
    let imm19 : BitVec 19 := w.extractLsb' 5 19
    let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.cbz width isNonZero rt offset)

  -- 11. Test and branch (immediate): TBZ / TBNZ (bits[30:25] == 011011)
  else if (w &&& 0x7e000000#32) == 0x36000000#32 then
    let b5 := w.getLsbD 31
    let isNonZero := w.getLsbD 24
    let b40 := (w.extractLsb' 19 5).toNat
    let bitPos := (if b5 then 32 else 0) + b40
    let imm14 : BitVec 14 := w.extractLsb' 5 14
    let offset : BitVec 64 := (imm14.signExtend 64) <<< 2
    let tbzW : RegWidth := if b5 then .W64 else .W32
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.tbz tbzW isNonZero rt bitPos offset)

  -- 12. Conditional branch (immediate): B.cond (bits[31:24] == 01010100, bit[4] == 0)
  else if (w &&& 0xff000010#32) == 0x54000000#32 then
    let imm19 : BitVec 19 := w.extractLsb' 5 19
    let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
    let cond := CondCode.ofBits (w.extractLsb' 0 4)
    some (.bCond cond offset)

  -- 13. Unconditional branch (register): BR / BLR / RET
  else if (w &&& 0xff9ffc1f#32) == 0xd61f0000#32 then
    let opc := (w.extractLsb' 21 2).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    match opc with
    | 0 => some (.br rn)
    | 1 => some (.blr rn)
    | 2 => some (.ret rn)
    | _ => none

  -- 14. Logical (shifted register): bits[28:24] == 01010
  else if (w &&& 0x1f000000#32) == 0x0a000000#32 then
    let opc := w.extractLsb' 29 2
    let shift := ShiftType.ofBits (w.extractLsb' 22 2)
    let nBit := w.getLsbD 21
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let imm6 := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    if !sf && imm6 >= 32 then
      none
    else
      some (.logicalShift width (LogicalOp.ofBits opc nBit) rd rn rm shift imm6)

  -- 15. Add/subtract (shifted register): bits[28:24] == 01011, bit[21] == 0
  else if (w &&& 0x1f200000#32) == 0x0b000000#32 then
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let shiftBits := w.extractLsb' 22 2
    if shiftBits == 3#2 then
      none -- ROR is reserved in Add/Sub shifted register
    else
      let shift := ShiftType.ofBits shiftBits
      let rm := Reg.fromZRBits (w.extractLsb' 16 5)
      let imm6 := (w.extractLsb' 10 6).toNat
      let rn := Reg.fromZRBits (w.extractLsb' 5 5)
      let rd := Reg.fromZRBits (w.extractLsb' 0 5)
      if !sf && imm6 >= 32 then
        none
      else
        some (.addSubShift width op rd rn rm shift imm6)

  -- 16. Add/subtract (extended register): bits[28:21] == 01011001, bits[23:22] == 00
  else if (w &&& 0x1fe00000#32) == 0x0b200000#32 then
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let optBits := w.extractLsb' 13 3
    let imm3 := (w.extractLsb' 10 3).toNat
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rdBits := w.extractLsb' 0 5
    if imm3 > 4 then
      none
    else
      let ext := ExtendType.ofBits optBits
      let rd := if op.setsFlags then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
      some (.addSubExt width op rd rn rm ext imm3)

  -- 17. Add/subtract (with carry): ADC / ADCS / SBC / SBCS (bits[28:21] == 11010000, bits[15:10] == 000000)
  else if (w &&& 0x1fe0fc00#32) == 0x1a000000#32 then
    let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.addSubCarry width op rd rn rm)

  -- 18. Conditional compare (register / immediate): CCMP / CCMN
  --     bits[29:21] == 111010010, bit[10] == 0, bit[4] == 0
  else if (w &&& 0x3fe00410#32) == 0x3a400000#32 then
    let isSub := w.getLsbD 30
    let isImm := w.getLsbD 11
    let rmOrImm := w.extractLsb' 16 5
    let cond := CondCode.ofBits (w.extractLsb' 12 4)
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let nzcv := w.extractLsb' 0 4
    if isImm then
      some (.condCompareImm width isSub rn rmOrImm nzcv cond)
    else
      some (.condCompareReg width isSub rn (Reg.fromZRBits rmOrImm) nzcv cond)

  -- 19. Conditional select: CSEL / CSINC / CSINV / CSNEG (bits[29:21] == 011010100, bit[11] == 0)
  else if (w &&& 0x3fe00800#32) == 0x1a800000#32 then
    let op := CondSelectOp.ofBits (w.getLsbD 30) (w.getLsbD 10)
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let cond := CondCode.ofBits (w.extractLsb' 12 4)
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.condSelect width op rd rn rm cond)

  -- 20. Data-processing (1 source): RBIT, REV16, REV32, REV, CLZ, CLS
  --     bits[30:21] == 1011010110, bits[20:16] == 00000
  else if (w &&& 0x7fff0000#32) == 0x5ac00000#32 then
    let opcode := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    match opcode with
    | 0 => some (.dataProc1 width .RBIT rd rn)
    | 1 => some (.dataProc1 width .REV16 rd rn)
    | 2 =>
      if sf then some (.dataProc1 .W64 .REV32 rd rn)
      else some (.dataProc1 .W32 .REV rd rn)
    | 3 =>
      if sf then some (.dataProc1 .W64 .REV rd rn)
      else none
    | 4 => some (.dataProc1 width .CLZ rd rn)
    | 5 => some (.dataProc1 width .CLS rd rn)
    | _ => none

  -- 20b. `CRC32{B,H,W,X}` / `CRC32C{B,H,W,X}` (`sf:0011010110:Rm:010:C:sz:Rn:Rd`).
  -- `sf = 1` requires `sz = 11` (`CRC32{C}X`); `sf = 0` requires `sz != 11`.
  else if (w &&& 0x7fe0e000#32) == 0x1ac04000#32 then
    let szBits := w.extractLsb' 10 2
    if sf != (szBits == 3#2) then none
    else
      some (.crc32 (w.getLsbD 12) (MemWidth.ofBits szBits)
        (Reg.fromZRBits (w.extractLsb' 0 5)) (Reg.fromZRBits (w.extractLsb' 5 5))
        (Reg.fromZRBits (w.extractLsb' 16 5)))

  -- 21. Data-processing (2 source): UDIV, SDIV, LSLV, LSRV, ASRV, RORV
  --     bits[30:21] == 0011010110
  else if (w &&& 0x7fe00000#32) == 0x1ac00000#32 then
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let opcode := (w.extractLsb' 10 6).toNat
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    match opcode with
    | 2  => some (.dataProc2 width .UDIV rd rn rm)
    | 3  => some (.dataProc2 width .SDIV rd rn rm)
    | 8  => some (.dataProc2 width .LSLV rd rn rm)
    | 9  => some (.dataProc2 width .LSRV rd rn rm)
    | 10 => some (.dataProc2 width .ASRV rd rn rm)
    | 11 => some (.dataProc2 width .RORV rd rn rm)
    | _  => none

  -- 22. Data-processing (3 source): MADD, MSUB, SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH
  --     bits[30:24] == 0011011
  else if (w &&& 0x7f000000#32) == 0x1b000000#32 then
    let op31 := (w.extractLsb' 21 3).toNat
    let o0 := w.getLsbD 15
    let rm := Reg.fromZRBits (w.extractLsb' 16 5)
    let raBits := w.extractLsb' 10 5
    let ra := Reg.fromZRBits raBits
    let rn := Reg.fromZRBits (w.extractLsb' 5 5)
    let rd := Reg.fromZRBits (w.extractLsb' 0 5)
    match sf, op31, o0 with
    | _, 0, false    => some (.dataProc3 width .MADD rd rn rm ra)
    | _, 0, true     => some (.dataProc3 width .MSUB rd rn rm ra)
    | true, 1, false => some (.dataProc3 .W64 .SMADDL rd rn rm ra)
    | true, 1, true  => some (.dataProc3 .W64 .SMSUBL rd rn rm ra)
    | true, 2, false => if raBits == 0b11111#5 then some (.dataProc3 .W64 .SMULH rd rn rm .xzr) else none
    | true, 5, false => some (.dataProc3 .W64 .UMADDL rd rn rm ra)
    | true, 5, true  => some (.dataProc3 .W64 .UMSUBL rd rn rm ra)
    | true, 6, false => if raBits == 0b11111#5 then some (.dataProc3 .W64 .UMULH rd rn rm .xzr) else none
    | _, _, _        => none

  -- 22b. Load/Store No-Allocate Pair `LDNP`/`STNP` (`opc:101:0:000:L:imm7:Rt2:Rn:Rt`, `opc ∈ {00, 10}`).
  -- Sequentially identical to signed-offset `LDP`/`STP`; `LDNP` with `Rt == Rt2` is rejected.
  else if (w &&& 0x7f800000#32) == 0x28000000#32 then
    let is64 := w.getLsbD 31
    let scale : Nat := if is64 then 3 else 2
    let sz : MemWidth := if is64 then .X64 else .W32
    let imm7 : BitVec 7 := w.extractLsb' 15 7
    let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
    let t2Bits := w.extractLsb' 10 5
    let nBits := w.extractLsb' 5 5
    let tBits := w.extractLsb' 0 5
    let rn := Reg.fromSPBits nBits
    let rt := Reg.fromZRBits tBits
    let rt2 := Reg.fromZRBits t2Bits
    if w.getLsbD 22 then
      if tBits == t2Bits then none
      else some (.ldnp sz rn rt rt2 offset)
    else
      some (.stnp sz rn rt rt2 offset)

  -- 23. Load/store register pair: LDP / LDPSW / STP (bits[29:25] == 10100)
  else if (w &&& 0x3e000000#32) == 0x28000000#32 then
    let opc := (w.extractLsb' 30 2).toNat
    let modeBits := (w.extractLsb' 23 2).toNat
    let isLoad := w.getLsbD 22
    let imm7 : BitVec 7 := w.extractLsb' 15 7
    let rt2Bits := w.extractLsb' 10 5
    let rnBits := w.extractLsb' 5 5
    let rt1Bits := w.extractLsb' 0 5
    let scale : Nat := if opc == 2 then 3 else 2
    let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
    let rn := Reg.fromSPBits rnBits
    let rt1 := Reg.fromZRBits rt1Bits
    let rt2 := Reg.fromZRBits rt2Bits
    let addr? : Option AddrMode :=
      match modeBits with
      | 1 => some (.PostIndex rn offset)
      | 2 => some (.Offset rn offset)
      | 3 => some (.PreIndex rn offset)
      | _ => none
    -- Reject architectural `CONSTRAINED UNPREDICTABLE` register overlaps so our deterministic
    -- model only accepts architecturally well-defined pair instructions:
    -- 1. Writeback base overlap (`wback && (t == n || t2 == n) && n != 31`);
    -- 2. Identical load targets (`L == 1 && t == t2`).
    let wbOverlap := (modeBits == 1 || modeBits == 3) && rnBits != 31#5 && (rt1Bits == rnBits || rt2Bits == rnBits)
    let loadPairOverlap := isLoad && rt1Bits == rt2Bits
    match addr? with
    | none => none
    | some addr =>
      if wbOverlap || loadPairOverlap then
        none
      else
        match opc, isLoad with
        | 0, true  => some (.ldp .W32 false rt1 rt2 addr)
        | 0, false => some (.stp .W32 rt1 rt2 addr)
        | 1, true  => some (.ldp .W64 true  rt1 rt2 addr)
        | 2, true  => some (.ldp .W64 false rt1 rt2 addr)
        | 2, false => some (.stp .W64 rt1 rt2 addr)
        | _, _     => none

  -- 23b. Prefetch memory (unsigned immediate) `PRFM <prfop>, [Xn|SP, #pimm]` (`11:111:0:01:10:imm12:Rn:Rt`).
  else if (w &&& 0xffc00000#32) == 0xf9800000#32 then
    let imm12 : BitVec 12 := w.extractLsb' 10 12
    let offset : BitVec 64 := (imm12.zeroExtend 64) <<< 3
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    some (.prfm (w.extractLsb' 0 5) (.Offset rn offset))

  -- 23c. Prefetch memory (unscaled `PRFUM` `11:111:0:00:10:0:imm9:00:Rn:Rt` and register offset
  -- `PRFM` `11:111:0:00:10:1:Rm:option:S:10:Rn:Rt`).
  else if (w &&& 0xffe00c00#32) == 0xf8800000#32 then
    let imm9 : BitVec 9 := w.extractLsb' 12 9
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    some (.prfm (w.extractLsb' 0 5) (.UnscaledOffset rn (imm9.signExtend 64)))
  else if (w &&& 0xffe00c00#32) == 0xf8a00800#32 then
    let extBits := w.extractLsb' 13 3
    if !extBits.getLsbD 1 then none
    else
      let rm := Reg.fromZRBits (w.extractLsb' 16 5)
      let ext := ExtendType.ofBits extBits
      let amount := if w.getLsbD 12 then 3 else 0
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      some (.prfm (w.extractLsb' 0 5) (.RegOffset rn rm ext amount))

  -- 23d. LSE Atomic memory operations (`LD<op>{A}{L}{B,H}`, `ST<op>{L}{B,H}`, `SWP{A}{L}{B,H}`:
  -- `size:111:0:00:A:R:1:Rs:o3:opc:00:Rn:Rt`, where `o3 == 0` is RMW and `o3:opc == 1000` is `SWP`),
  -- and Load-Acquire RCpc register `LDAPR{B,H}` (`size:111:0:00:1:0:1:11111:1100:00:Rn:Rt`).
  else if (w &&& 0x3f200c00#32) == 0x38200000#32 then
    let sz := MemWidth.ofBits (w.extractLsb' 30 2)
    let acq := w.getLsbD 23
    let rel := w.getLsbD 22
    let rsBits := w.extractLsb' 16 5
    let o3 := w.getLsbD 15
    let opc := w.extractLsb' 12 3
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    if !o3 then
      some (.atomicRmw (AtomicOp.ofBits opc) sz acq rel (Reg.fromZRBits rsBits) rn rt)
    else if opc == 0#3 then
      some (.atomicRmw .SWP sz acq rel (Reg.fromZRBits rsBits) rn rt)
    else if opc == 4#3 && acq && !rel && rsBits == 31#5 then
      some (.ldapr sz rn rt)
    else
      none

  -- 23e. Load-Acquire / Store-Release RCpc unscaled immediate `STLUR*` / `LDAPUR*` / `LDAPURS*`
  -- (`size:011001:opc:0:imm9:00:Rn:Rt`). Reject `size == 11 && opc<1> == 1` and `size == 10 && opc == 11`.
  else if (w &&& 0x3f200c00#32) == 0x19000000#32 then
    let sizeBits := w.extractLsb' 30 2
    let opc := w.extractLsb' 22 2
    if (sizeBits == 3#2 && opc.getLsbD 1) || (sizeBits == 2#2 && opc == 3#2) then none
    else
      let imm9 : BitVec 9 := w.extractLsb' 12 9
      some (.ldapurStlur (MemWidth.ofBits sizeBits) opc (Reg.fromSPBits (w.extractLsb' 5 5))
        (Reg.fromZRBits (w.extractLsb' 0 5)) (imm9.signExtend 64))

  -- 24. Load/store register (unsigned immediate): bits[29:24] == 111001
  else if (w &&& 0x3f000000#32) == 0x39000000#32 then
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    let imm12 : BitVec 12 := w.extractLsb' 10 12
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    let offset : BitVec 64 := (imm12.zeroExtend 64) <<< sizeBits
    mkLoadStoreInst sizeBits opc rt (.Offset rn offset)

  -- 25. Load/store register (unscaled `LDUR`/`STUR`, pre-index, post-index, register offset):
  --     bits[29:24] == 111000
  else if (w &&& 0x3f000000#32) == 0x38000000#32 then
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    let rnBits := w.extractLsb' 5 5
    let rtBits := w.extractLsb' 0 5
    let rn := Reg.fromSPBits rnBits
    let rt := Reg.fromZRBits rtBits
    if !(w.getLsbD 21) then
      let imm9 : BitVec 9 := w.extractLsb' 12 9
      let offset : BitVec 64 := imm9.signExtend 64
      let mode2 := (w.extractLsb' 10 2).toNat
      -- Reject architectural `CONSTRAINED UNPREDICTABLE` base-register writeback overlap
      -- (`wback && n == t && n != 31`) on pre-indexed (`mode2 == 3`) and post-indexed (`mode2 == 1`)
      -- loads and stores.
      let wbOverlap := (mode2 == 1 || mode2 == 3) && rnBits != 31#5 && rtBits == rnBits
      if wbOverlap then
        none
      else
        match mode2 with
        | 0 => mkLoadStoreInst sizeBits opc rt (.UnscaledOffset rn offset)
        | 1 => mkLoadStoreInst sizeBits opc rt (.PostIndex rn offset)
        | 3 => mkLoadStoreInst sizeBits opc rt (.PreIndex rn offset)
        | _ => none
    else if (w.extractLsb' 10 2) == 2#2 then
      -- Register offset: bit[21] == 1, bits[11:10] == 10
      let rm := Reg.fromZRBits (w.extractLsb' 16 5)
      let extBits := w.extractLsb' 13 3
      let ext := ExtendType.ofBits extBits
      let sBit := w.getLsbD 12
      -- Reject reserved `option<1> = 0` (`000`, `001`, `100`, `101`), and canonicalize 8-bit
      -- (`sizeBits = 0`, `LDRB`/`LDRSB`/`STRB`) to `S = 0` so `amount = 0` has a unique
      -- encoding (`encode_of_decode`); redundant `S = 1` (`#0` shift) fails closed (`none`).
      if !extBits.getLsbD 1 || (sizeBits == 0 && sBit) then
        none
      else
        let amount := if sBit then sizeBits else 0
        mkLoadStoreInst sizeBits opc rt (.RegOffset rn rm ext amount)
    else
      none

  -- 25b. Load register (literal): LDR / LDRSW / PRFM (bits[29:24] == 011000)
  else if (w &&& 0x3f000000#32) == 0x18000000#32 then
    let opc := (w.extractLsb' 30 2).toNat
    let imm19 : BitVec 19 := w.extractLsb' 5 19
    let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    match opc with
    | 0 => some (.ldrLit .W32 false rt offset)
    | 1 => some (.ldrLit .W64 false rt offset)
    | 2 => some (.ldrLit .W64 true  rt offset)
    | _ => some (.prfmLit (w.extractLsb' 0 5) offset)

  -- 25c. SIMD/FP PC-relative literal load `LDR St/Dt/Qt, label` (`opc:011:1:00:imm19:Rt`, `opc != 11`).
  else if (w &&& 0x3f000000#32) == 0x1c000000#32 then
    let imm19 : BitVec 19 := w.extractLsb' 5 19
    let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
    let vt : BitVec 5 := w.extractLsb' 0 5
    match (w.extractLsb' 30 2).toNat with
    | 0 => some (.ldrSimdLit .S32 vt offset)
    | 1 => some (.ldrSimdLit .D64 vt offset)
    | 2 => some (.ldrSimdLit .Q128 vt offset)
    | _ => none

  -- 26a. Load-Acquire / Store-Release register (`LDAR`, `LDARB`, `LDARH`, `STLR`, `STLRB`, `STLRH`):
  --      `size[31:30] : 001000 : o2=1 : L[22] : o1=0 : Rs=11111 : o0=1 : Rt2=11111 : Rn : Rt`
  else if (w &&& 0x3fbffc00#32) == 0x089ffc00#32 then
    let sz := MemWidth.ofBits (w.extractLsb' 30 2)
    let isLoad := w.getLsbD 22
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.ldarStlr sz isLoad rn rt)

  -- 26b. Load-Exclusive register (`LDXR`, `LDXRB`, `LDXRH`, `LDAXR`, `LDAXRB`, `LDAXRH`):
  --      `size[31:30] : 001000 : o2=0 : L=1 : o1=0 : Rs=11111 : o0[15] : Rt2=11111 : Rn : Rt`
  else if (w &&& 0x3fff7c00#32) == 0x085f7c00#32 then
    let sz := MemWidth.ofBits (w.extractLsb' 30 2)
    let acq := w.getLsbD 15
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.ldxr sz acq rn rt)

  -- 26c. Store-Exclusive register (`STXR`, `STXRB`, `STXRH`, `STLXR`, `STLXRB`, `STLXRH`):
  --      `size[31:30] : 001000 : o2=0 : L=0 : o1=0 : Rs[20:16] : o0[15] : Rt2=11111 : Rn : Rt`
  --      Reject architectural `CONSTRAINED UNPREDICTABLE` register overlaps (`s == t` and
  --      `s == n && n != 31`).
  else if (w &&& 0x3fe07c00#32) == 0x08007c00#32 then
    let rsBits := w.extractLsb' 16 5
    let rnBits := w.extractLsb' 5 5
    let rtBits := w.extractLsb' 0 5
    if rsBits == rtBits || (rsBits == rnBits && rnBits != 31#5) then
      none
    else
      let sz := MemWidth.ofBits (w.extractLsb' 30 2)
      let rel := w.getLsbD 15
      let rs := Reg.fromZRBits rsBits
      let rn := Reg.fromSPBits rnBits
      let rt := Reg.fromZRBits rtBits
      some (.stxr sz rel rs rn rt)

  -- 26d. Load-Exclusive pair `LDXP`/`LDAXP` (`1:sz:001000:0:L=1:1:11111:o0:Rt2:Rn:Rt`).
  -- `Rt == Rt2` is `CONSTRAINED UNPREDICTABLE` (rejected).
  else if (w &&& 0xbfff0000#32) == 0x887f0000#32 then
    let sz : MemWidth := if w.getLsbD 30 then .X64 else .W32
    let acq := w.getLsbD 15
    let t2Bits := w.extractLsb' 10 5
    let tBits := w.extractLsb' 0 5
    if tBits == t2Bits then none
    else some (.ldxp sz acq (Reg.fromSPBits (w.extractLsb' 5 5)) (Reg.fromZRBits tBits) (Reg.fromZRBits t2Bits))

  -- 26e. Store-Exclusive pair `STXP`/`STLXP` (`1:sz:001000:L=0:1:Rs:o0:Rt2:Rn:Rt`).
  -- Overlaps `s ∈ {t, t2}` and `s == n && n != 31` are rejected.
  else if (w &&& 0xbfe00000#32) == 0x88200000#32 then
    let sBits := w.extractLsb' 16 5
    let t2Bits := w.extractLsb' 10 5
    let nBits := w.extractLsb' 5 5
    let tBits := w.extractLsb' 0 5
    if sBits == tBits || sBits == t2Bits || (sBits == nBits && nBits != 31#5) then none
    else
      let sz : MemWidth := if w.getLsbD 30 then .X64 else .W32
      some (.stxp sz (w.getLsbD 15) (Reg.fromZRBits sBits) (Reg.fromSPBits nBits)
        (Reg.fromZRBits tBits) (Reg.fromZRBits t2Bits))

  -- 26f. Compare-and-swap `CAS{A}{L}{B,H}` (`size:001000:1:L:1:Rs:o0:11111:Rn:Rt`).
  else if (w &&& 0x3fa07c00#32) == 0x08a07c00#32 then
    let sz := MemWidth.ofBits (w.extractLsb' 30 2)
    some (.cas sz (w.getLsbD 22) (w.getLsbD 15) (Reg.fromZRBits (w.extractLsb' 16 5))
      (Reg.fromSPBits (w.extractLsb' 5 5)) (Reg.fromZRBits (w.extractLsb' 0 5)))

  -- 26g. Compare-and-swap pair `CASP{A}{L}` (`0:sz:001000:0:L:1:Rs:o0:11111:Rn:Rt`).
  -- `Rs`/`Rt` must be even (odd is UNDEFINED per the ASL, rejected); pairs are `(s, s+1)`, `(t, t+1)`.
  else if (w &&& 0xbfa07c00#32) == 0x08207c00#32 then
    let sBits := w.extractLsb' 16 5
    let tBits := w.extractLsb' 0 5
    if sBits.getLsbD 0 || tBits.getLsbD 0 then none
    else
      let sz : MemWidth := if w.getLsbD 30 then .X64 else .W32
      some (.casp sz (w.getLsbD 22) (w.getLsbD 15) (Reg.fromZRBits sBits) (Reg.fromZRBits (sBits + 1#5))
        (Reg.fromSPBits (w.extractLsb' 5 5)) (Reg.fromZRBits tBits) (Reg.fromZRBits (tBits + 1#5)))

  -- 27. System Register Move (`MRS`, `MSR`)
  else if (w &&& 0xffd00000#32) == 0xd5100000#32 then
    let isRead := w.getLsbD 21
    let sysreg : BitVec 15 := w.extractLsb' 5 15
    let rt := Reg.fromZRBits (w.extractLsb' 0 5)
    some (.sysReg isRead sysreg rt)

  -- 28. Memory Barrier (`DMB`, `DSB`, `ISB`, `CLREX`)
  else if (w &&& 0xfffff01f#32) == 0xd503301f#32 then
    let crm : BitVec 4 := w.extractLsb' 8 4
    let op2 : BitVec 3 := w.extractLsb' 5 3
    if op2 == 2#3 || op2 == 4#3 || op2 == 5#3 || op2 == 6#3 then
      some (.barrier crm op2)
    else
      none

  -- 28b. SIMD/FP Load/Store No-Allocate Pair (`LDNP`, `STNP` S/D/Q, `opc:101:1:000:L:imm7:Rt2:Rn:Rt`).
  -- Sequentially identical to signed-offset `LDP`/`STP`; `LDNP` with `Vt1 == Vt2` is rejected.
  else if (w &&& 0x3f800000#32) == 0x2c000000#32 then
    let sz? : Option (SimdMemSize × Nat) :=
      match (w.extractLsb' 30 2).toNat with
      | 0 => some (.S32, 2)
      | 1 => some (.D64, 3)
      | 2 => some (.Q128, 4)
      | _ => none
    match sz? with
    | none => none
    | some (sz, scale) =>
      let imm7 : BitVec 7 := w.extractLsb' 15 7
      let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
      let vt2 : BitVec 5 := w.extractLsb' 10 5
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt1 : BitVec 5 := w.extractLsb' 0 5
      if w.getLsbD 22 then
        if vt1 == vt2 then none else some (.ldnpSimd sz vt1 vt2 rn offset)
      else some (.stnpSimd sz vt1 vt2 rn offset)

  -- 29. SIMD/FP Load/Store Pair (`LDP`, `STP` S/D/Q)
  else if (w &&& 0x3e000000#32) == 0x2c000000#32 then
    let opc := (w.extractLsb' 30 2).toNat
    let modeBits := (w.extractLsb' 23 2).toNat
    let isLoad := w.getLsbD 22
    let sz? : Option (SimdMemSize × Nat) :=
      match opc with
      | 0 => some (.S32, 2)
      | 1 => some (.D64, 3)
      | 2 => some (.Q128, 4)
      | _ => none
    match sz? with
    | none => none
    | some (sz, scale) =>
      let imm7 : BitVec 7 := w.extractLsb' 15 7
      let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
      let vt2 : BitVec 5 := w.extractLsb' 10 5
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt1 : BitVec 5 := w.extractLsb' 0 5
      let addr? : Option AddrMode :=
        match modeBits with
        | 1 => some (.PostIndex rn offset)
        | 2 => some (.Offset rn offset)
        | 3 => some (.PreIndex rn offset)
        | _ => none
      match addr? with
      | some addr =>
        if isLoad then
          if vt1 == vt2 then none else some (.ldpSimd sz vt1 vt2 addr)
        else some (.stpSimd sz vt1 vt2 addr)
      | none => none

  -- 30. SIMD/FP Load/Store Register (Unsigned Immediate)
  else if (w &&& 0x3f000000#32) == 0x3d000000#32 then
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    match decodeSimdLoadStoreType sizeBits opc with
    | some (isLoad, sz, scale) =>
      let imm12 : BitVec 12 := w.extractLsb' 10 12
      let offset : BitVec 64 := (imm12.zeroExtend 64) <<< scale
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt : BitVec 5 := w.extractLsb' 0 5
      let addr := AddrMode.Offset rn offset
      if isLoad then some (.ldrSimd sz vt addr)
      else some (.strSimd sz vt addr)
    | none => none

  -- 31. SIMD/FP Load/Store Register (Unscaled `LDUR`/`STUR`, Pre-Index, Post-Index, Register Offset)
  else if (w &&& 0x3f000000#32) == 0x3c000000#32 then
    let sizeBits := (w.extractLsb' 30 2).toNat
    let opc := (w.extractLsb' 22 2).toNat
    match decodeSimdLoadStoreType sizeBits opc with
    | some (isLoad, sz, scale) =>
      let rn := Reg.fromSPBits (w.extractLsb' 5 5)
      let vt : BitVec 5 := w.extractLsb' 0 5
      let addr? : Option AddrMode :=
        if !(w.getLsbD 21) then
          let imm9 : BitVec 9 := w.extractLsb' 12 9
          let offset : BitVec 64 := imm9.signExtend 64
          match (w.extractLsb' 10 2).toNat with
          | 0 => some (.UnscaledOffset rn offset)
          | 1 => some (.PostIndex rn offset)
          | 3 => some (.PreIndex rn offset)
          | _ => none
        else if (w.extractLsb' 10 2) == 2#2 then
          let rm := Reg.fromZRBits (w.extractLsb' 16 5)
          let extBits := w.extractLsb' 13 3
          let ext := ExtendType.ofBits extBits
          let sBit := w.getLsbD 12
          -- Reject reserved `option<1> = 0`, and canonicalize 8-bit (`scale = 0`, `LDR_BL_ldst_regoff` /
          -- `STR_BL_ldst_regoff`) to `S = 0` so `amount = 0` has a unique encoding (`encode_of_decode`);
          -- redundant `S = 1` (`#0` shift) fails closed (`none`).
          if !extBits.getLsbD 1 || (scale == 0 && sBit) then
            none
          else
            let amount := if sBit then scale else 0
            some (.RegOffset rn rm ext amount)
        else
          none
      match addr? with
      | some addr =>
        if isLoad then some (.ldrSimd sz vt addr)
        else some (.strSimd sz vt addr)
      | none => none
    | none => none

  -- 31b. SIMD `LD1`–`LD4` / `ST1`–`ST4` (multiple structures):
  -- no offset `0:Q:0011000:L:000000:opcode:size:Rn:Rt`, post-index `0:Q:0011001:L:0:Rm:opcode:size:Rn:Rt`
  -- (`opcode` 0111 → LD1/ST1 1 reg, 1010 → 2, 0110 → 3, 0010 → 4;
  --  1000 → LD2/ST2, 0100 → LD3/ST3, 0000 → LD4/ST4 with `!(size == 11 && !Q)`).
  else if (w &&& 0xbfbf0000#32) == 0x0c000000#32 || (w &&& 0xbfa00000#32) == 0x0c800000#32 then
    let isLoad := w.getLsbD 22
    let q := w.getLsbD 30
    let size := w.extractLsb' 10 2
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let postIdx := w.getLsbD 23
    let rm := w.extractLsb' 16 5
    let vt := w.extractLsb' 0 5
    match (w.extractLsb' 12 4).toNat with
    | 7  => some (.simdLdSt1Multi isLoad q size 1 rn postIdx rm vt)
    | 10 => some (.simdLdSt1Multi isLoad q size 2 rn postIdx rm vt)
    | 6  => some (.simdLdSt1Multi isLoad q size 3 rn postIdx rm vt)
    | 2  => some (.simdLdSt1Multi isLoad q size 4 rn postIdx rm vt)
    | 8  => if size == 3#2 && !q then none else some (.simdLdStMulti isLoad q size 2 rn postIdx rm vt)
    | 4  => if size == 3#2 && !q then none else some (.simdLdStMulti isLoad q size 3 rn postIdx rm vt)
    | 0  => if size == 3#2 && !q then none else some (.simdLdStMulti isLoad q size 4 rn postIdx rm vt)
    | _  => none

  -- 31c. SIMD `LD1R { Vt.<T> }, [Xn|SP]{, post}` (`0:Q:0011010:1:0:00000:110:0:size:Rn:Rt` /
  -- post-index `0:Q:0011011:1:0:Rm:110:0:size:Rn:Rt`).
  else if (w &&& 0xbffff000#32) == 0x0d40c000#32 || (w &&& 0xbfe0f000#32) == 0x0dc0c000#32 then
    some (.simdLd1r (w.getLsbD 30) (w.extractLsb' 10 2) (Reg.fromSPBits (w.extractLsb' 5 5))
      (w.getLsbD 23) (w.extractLsb' 16 5) (w.extractLsb' 0 5))

  -- 32. SIMD `ST1` Single Structure (Post-Index)
  else if (w &&& 0xbfe00000#32) == 0x0d800000#32 then
    let q := w.getLsbD 30
    let rm : BitVec 5 := w.extractLsb' 16 5
    let opcode : BitVec 3 := w.extractLsb' 13 3
    let sBit := w.getLsbD 12
    let size : BitVec 2 := w.extractLsb' 10 2
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let vt : BitVec 5 := w.extractLsb' 0 5
    some (.st1SinglePost q rm opcode sBit size rn vt)

  -- 32b. SIMD `LD1` Single Structure (no-offset / post-index) and `ST1` Single Structure (no-offset)
  -- (`0:Q:0011010:L:0:00000:opcode:S:size:Rn:Rt` or `0:Q:0011011:1:0:Rm:opcode:S:size:Rn:Rt`).
  else if (w &&& 0xbfbf0000#32) == 0x0d000000#32 || (w &&& 0xbfe00000#32) == 0x0dc00000#32 then
    let q := w.getLsbD 30
    let postIdx := w.getLsbD 23
    let isLoad := w.getLsbD 22
    let rm : BitVec 5 := w.extractLsb' 16 5
    let opcode : BitVec 3 := w.extractLsb' 13 3
    let sBit := w.getLsbD 12
    let size : BitVec 2 := w.extractLsb' 10 2
    let rn := Reg.fromSPBits (w.extractLsb' 5 5)
    let vt : BitVec 5 := w.extractLsb' 0 5
    if validSimdLdSt1Single opcode sBit size then
      some (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt)
    else none

  -- 33. AES Cryptographic Operations (`AESE`, `AESD`, `AESMC`, `AESIMC`)
  else if (w &&& 0xffffcc00#32) == 0x4e284800#32 then
    let op := AesOp.ofBits (w.extractLsb' 12 2)
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.aes op rd rn)

  -- 34. `FMOV` (GPR <-> SIMD/FP Scalar)
  else if (w &&& 0x7f20fc00#32) == 0x1e200000#32 then
    let sfBit := w.getLsbD 31
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let rmode : BitVec 2 := w.extractLsb' 19 2
    let opcode : BitVec 3 := w.extractLsb' 16 3
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fmovGprVec sfBit ftype rmode opcode rn rd)

  -- 35. SIMD Modified Immediate (`MOVI`/`MVNI`) and SIMD Shift by Immediate (`SHL`, `USHLL`, `USHLL2`)
  else if (w &&& 0x9f800400#32) == 0x0f000400#32 then
    let q := w.getLsbD 30
    let op := w.getLsbD 29
    let immh : BitVec 4 := w.extractLsb' 19 4
    let immb : BitVec 3 := w.extractLsb' 16 3
    let opcode : BitVec 5 := w.extractLsb' 11 5
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdImmShift q op immh immb opcode rn rd)

  -- 35b. SIMD table lookup `TBL`/`TBX` (`0:Q:001110:00:0:Rm:0:len:op:00:Rn:Rd`).
  else if (w &&& 0xbfe08c00#32) == 0x0e000000#32 then
    some (.simdTbl (w.getLsbD 30) (w.extractLsb' 16 5) (w.extractLsb' 13 2) (w.getLsbD 12)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5))

  -- 35c. SIMD scalar pairwise `ADDP Dd, Vn.2D` (`01:0:11110:11:11000:11011:10:Rn:Rd`).
  else if (w &&& 0xfffffc00#32) == 0x5ef1b800#32 then
    some (.simdAddpScalar (w.extractLsb' 5 5) (w.extractLsb' 0 5))

  -- 35d. SIMD scalar duplicate element `DUP <V><d>, <Vn>.<T>[<index>]` (`01:0:11110:000:imm5:0:0000:1:Rn:Rd`).
  else if (w &&& 0xffe0fc00#32) == 0x5e000400#32 then
    let imm5 : BitVec 5 := w.extractLsb' 16 5
    if imm5.extractLsb' 0 4 != 0#4 then
      some (.simdDupScalar imm5 (w.extractLsb' 5 5) (w.extractLsb' 0 5))
    else none

  -- 36. SIMD Copy / Duplicate / Insert / Extract (`DUP`, `INS`, `UMOV`, `MOV`)
  else if (w &&& 0x9fe08400#32) == 0x0e000400#32 then
    let q := w.getLsbD 30
    let op := w.getLsbD 29
    let imm5 : BitVec 5 := w.extractLsb' 16 5
    let imm4 : BitVec 4 := w.extractLsb' 11 4
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdInsDup q op imm5 imm4 rn rd)

  -- 37. SIMD Three Same (`EOR`, `ORR`, `ADD`, `SUB`, `CMEQ`, `USHL`, etc.)
  else if (w &&& 0x9f200400#32) == 0x0e200400#32 then
    let q := w.getLsbD 30
    let u := w.getLsbD 29
    let size : BitVec 2 := w.extractLsb' 22 2
    let rm : BitVec 5 := w.extractLsb' 16 5
    let opcode : BitVec 5 := w.extractLsb' 11 5
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdThreeSame q u size rm opcode rn rd)

  -- 38. SIMD Two-Reg Misc (`REV64`, `REV32`, `CMLT #0`, `CMGE #0`, etc.)
  else if (w &&& 0x9f3e0c00#32) == 0x0e200800#32 then
    let q := w.getLsbD 30
    let u := w.getLsbD 29
    let size : BitVec 2 := w.extractLsb' 22 2
    let opcode : BitVec 5 := w.extractLsb' 12 5
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdTwoRegMisc q u size opcode rn rd)

  -- 39. SIMD Across Lanes (`UMAXV`, `ADDV`, etc.)
  else if (w &&& 0x9f3e0c00#32) == 0x0e300800#32 then
    let q := w.getLsbD 30
    let u := w.getLsbD 29
    let size : BitVec 2 := w.extractLsb' 22 2
    let opcode : BitVec 5 := w.extractLsb' 12 5
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdAcrossLanes q u size opcode rn rd)

  -- 40. SIMD Permute (`UZP1`, `TRN1`, `ZIP1`, `UZP2`, `TRN2`, `ZIP2`)
  else if (w &&& 0xbf208c00#32) == 0x0e000800#32 then
    let q := w.getLsbD 30
    let size : BitVec 2 := w.extractLsb' 22 2
    let rm : BitVec 5 := w.extractLsb' 16 5
    let opcode : BitVec 3 := w.extractLsb' 12 3
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdPermute q size rm opcode rn rd)

  -- 41. SIMD Extract (`EXT`)
  else if (w &&& 0xbfe08400#32) == 0x2e000000#32 then
    let q := w.getLsbD 30
    let rm : BitVec 5 := w.extractLsb' 16 5
    let imm4 : BitVec 4 := w.extractLsb' 11 4
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.simdExt q rm imm4 rn rd)

  -- 41b. SIMD Polynomial Multiply Long `PMULL`/`PMULL2` (`0:Q:0:01110:size:1:Rm:1110:00:Rn:Rd`,
  -- `size = 00` for `8H <- 8B/16B`, `size = 11` for `1Q <- 1D/2D`; `size ∈ {01, 10}` is UNDEFINED).
  else if (w &&& 0xbf20fc00#32) == 0x0e20e000#32 then
    let size : BitVec 2 := w.extractLsb' 22 2
    if size == 0#2 || size == 3#2 then
      let q := w.getLsbD 30
      let rm : BitVec 5 := w.extractLsb' 16 5
      let rn : BitVec 5 := w.extractLsb' 5 5
      let rd : BitVec 5 := w.extractLsb' 0 5
      some (.simdPmull q (size == 3#2) rm rn rd)
    else none

  -- 41b2. SIMD Three Different (`SADDL`/`UADDL`, `SADDW`/`UADDW`, `SSUBL`/`USUBL`, `SSUBW`/`USUBW`,
  -- `ADDHN`/`RADDHN`, `SABAL`/`UABAL`, `SUBHN`/`RSUBHN`, `SABDL`/`UABDL`, `SMLAL`/`UMLAL`,
  -- `SMLSL`/`UMLSL`, `SMULL`/`UMULL`, and `*2` variants: `0:Q:U:01110:size:1:Rm:opcode:00:Rn:Rd`).
  else if (w &&& 0x9f200c00#32) == 0x0e200000#32 then
    let size : BitVec 2 := w.extractLsb' 22 2
    let opcode : BitVec 4 := w.extractLsb' 12 4
    if validSimdThreeDiff size opcode then
      let q := w.getLsbD 30
      let u := w.getLsbD 29
      let rm : BitVec 5 := w.extractLsb' 16 5
      let rn : BitVec 5 := w.extractLsb' 5 5
      let rd : BitVec 5 := w.extractLsb' 0 5
      some (.simdThreeDiff q u size rm opcode rn rd)
    else none

  -- 41c. `FEAT_SHA1`/`FEAT_SHA256` 2-register SHA (`SHA1H`, `SHA1SU1`, `SHA256SU0`)
  -- (`01011110:00101000:0:opcode:10:Rn:Rd`, `opcode ∈ {00000, 00001, 00010}`).
  else if (w &&& 0xfffe0c00#32) == 0x5e280800#32 then
    let opcode : BitVec 5 := w.extractLsb' 12 5
    if opcode == 0#5 || opcode == 1#5 || opcode == 2#5 then
      let rn : BitVec 5 := w.extractLsb' 5 5
      let rd : BitVec 5 := w.extractLsb' 0 5
      some (.cryptoSha2Reg opcode rn rd)
    else none

  -- 41d. `FEAT_SHA1`/`FEAT_SHA256` 3-register SHA (`SHA1C`, `SHA1P`, `SHA1M`, `SHA1SU0`,
  -- `SHA256H`, `SHA256H2`, `SHA256SU1`: `01011110:000:Rm:0:opcode:00:Rn:Rd`, `opcode != 111`).
  else if (w &&& 0xffe08c00#32) == 0x5e000000#32 then
    let opcode : BitVec 3 := w.extractLsb' 12 3
    if opcode != 7#3 then
      let rm : BitVec 5 := w.extractLsb' 16 5
      let rn : BitVec 5 := w.extractLsb' 5 5
      let rd : BitVec 5 := w.extractLsb' 0 5
      some (.cryptoSha3Reg opcode rm rn rd)
    else none

  -- 41e. `FEAT_SHA512` 2-register schedule update 0 (`SHA512SU0`: `11001110:11000000:100000:Rn:Rd`).
  else if (w &&& 0xfffffc00#32) == 0xcec08000#32 then
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.cryptoSha512Reg2 rn rd)

  -- 41f. `FEAT_SHA512`/`FEAT_SHA3` 3-register (`SHA512H`, `SHA512H2`, `SHA512SU1`, `RAX1`:
  -- `11001110:011:Rm:1:000:opcode:Rn:Rd`).
  else if (w &&& 0xffe0f000#32) == 0xce608000#32 then
    let rm : BitVec 5 := w.extractLsb' 16 5
    let opcode : BitVec 2 := w.extractLsb' 10 2
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.cryptoSha512Reg3 opcode rm rn rd)

  -- 41g. `FEAT_SHA3` 4-register bitwise (`EOR3`, `BCAX`: `11001110:00:isBcax:Rm:0:Ra:Rn:Rd`).
  else if (w &&& 0xffc08000#32) == 0xce000000#32 then
    let isBcax := w.getLsbD 21
    let rm : BitVec 5 := w.extractLsb' 16 5
    let ra : BitVec 5 := w.extractLsb' 10 5
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.cryptoSha3FourReg isBcax rm ra rn rd)

  -- 41h. `FEAT_SHA3` Exclusive-OR and Rotate (`XAR`: `11001110:100:Rm:imm6:Rn:Rd`).
  else if (w &&& 0xffe00000#32) == 0xce800000#32 then
    let rm : BitVec 5 := w.extractLsb' 16 5
    let imm6 : BitVec 6 := w.extractLsb' 10 6
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.cryptoXar rm imm6 rn rd)

  -- 42. Scalar Floating-Point Data-Processing (1 source)
  else if (w &&& 0xff207c00#32) == 0x1e204000#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let opcode : BitVec 6 := w.extractLsb' 15 6
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fpDataProc1 ftype opcode rn rd)

  -- 43. Scalar Floating-Point Data-Processing (2 source)
  else if (w &&& 0xff200c00#32) == 0x1e200800#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let rm : BitVec 5 := w.extractLsb' 16 5
    let opcode : BitVec 4 := w.extractLsb' 12 4
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fpDataProc2 ftype rm opcode rn rd)

  -- 44. Scalar Floating-Point Compare (`FCMP`, `FCMPE`)
  else if (w &&& 0xff203c00#32) == 0x1e202000#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let rm : BitVec 5 := w.extractLsb' 16 5
    let op : BitVec 2 := w.extractLsb' 14 2
    let rn : BitVec 5 := w.extractLsb' 5 5
    let opcode2 : BitVec 5 := w.extractLsb' 0 5
    some (.fpCompare ftype rm op rn opcode2)

  -- 45. Scalar Floating-Point Immediate (`FMOV Sd/Dd, #imm8`)
  else if (w &&& 0xff201fe0#32) == 0x1e201000#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let imm8 : BitVec 8 := w.extractLsb' 13 8
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fpImm ftype imm8 rd)

  -- 46. Scalar Floating-Point Conditional Compare (`FCCMP`, `FCCMPE`)
  else if (w &&& 0xff200c00#32) == 0x1e200400#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let rm : BitVec 5 := w.extractLsb' 16 5
    let cond : BitVec 4 := w.extractLsb' 12 4
    let rn : BitVec 5 := w.extractLsb' 5 5
    let op := w.getLsbD 4
    let nzcv : BitVec 4 := w.extractLsb' 0 4
    some (.fpCondCompare ftype rm cond rn op nzcv)

  -- 47. Scalar Floating-Point Conditional Select (`FCSEL`)
  else if (w &&& 0xff200c00#32) == 0x1e200c00#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let rm : BitVec 5 := w.extractLsb' 16 5
    let cond : BitVec 4 := w.extractLsb' 12 4
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fpCondSelect ftype rm cond rn rd)

  -- 48. Scalar Floating-Point Data-Processing (3 source: `FMADD`, `FMSUB`, `FNMADD`, `FNMSUB`)
  else if (w &&& 0xff000000#32) == 0x1f000000#32 then
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let o1 := w.getLsbD 21
    let rm : BitVec 5 := w.extractLsb' 16 5
    let o0 := w.getLsbD 15
    let ra : BitVec 5 := w.extractLsb' 10 5
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fpDataProc3 ftype o1 rm o0 ra rn rd)

  -- 49. Scalar Floating-Point / Fixed-Point Conversion (`SCVTF`, `UCVTF`, `FCVTZS`, `FCVTZU` fixed-point)
  else if (w &&& 0x7f200000#32) == 0x1e000000#32 then
    let sfBit := w.getLsbD 31
    let ftype : BitVec 2 := w.extractLsb' 22 2
    let rmode : BitVec 2 := w.extractLsb' 19 2
    let opcode : BitVec 3 := w.extractLsb' 16 3
    let scale : BitVec 6 := w.extractLsb' 10 6
    let rn : BitVec 5 := w.extractLsb' 5 5
    let rd : BitVec 5 := w.extractLsb' 0 5
    some (.fpFixedConv sfBit ftype rmode opcode scale rn rd)

  else
    none

/-- Format a 32-bit instruction word as an 8-digit lowercase hex string (`0x........`). -/
def hexWord32 (w : BitVec 32) : String :=
  let hexDigit (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))
  let digits : List Char := (List.range 8).map fun i =>
    let shift := (7 - i) * 4
    hexDigit (((w >>> shift).truncate 4).toNat)
  "0x" ++ String.ofList digits

/-- Format a 64-bit address as a lowercase hex string (`0x...`). -/
def hexAddr64 (a : BitVec 64) : String :=
  let n := a.toNat
  if n == 0 then "0x0"
  else
    let hexDigit (d : Nat) : Char :=
      if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + (d - 10))
    let rec go (fuel : Nat) (v : Nat) (acc : List Char) : List Char :=
      match fuel with
      | 0 => acc
      | fuel' + 1 =>
        if v == 0 then acc
        else go fuel' (v / 16) (hexDigit (v % 16) :: acc)
    "0x" ++ String.ofList (go 16 n [])

/-- Classify a 32-bit instruction word that failed `decodeInst`, naming the AdvSIMD/FP/SVE encoding
class, field values, and best-known mnemonic family when recognizable, and noting that it is not
modeled in `Arm64/Trusted/ISA` (or architecturally UNDEFINED). -/
def describeUnsupportedWord (w : BitVec 32) : String :=
  let insnHex := hexWord32 w
  -- 1. AdvSIMD three-different (`0:Q:U:01110:size:1:Rm:opcode:00:Rn:Rd`)
  if (w &&& 0x9f200c00#32) == 0x0e200000#32 then
    let q := if w.getLsbD 30 then 1 else 0
    let u := w.getLsbD 29
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 12 4).toNat
    let mnem :=
      match opcode with
      | 0  => if u then "UADDL/UADDL2" else "SADDL/SADDL2"
      | 1  => if u then "UADDW/UADDW2" else "SADDW/SADDW2"
      | 2  => if u then "USUBL/USUBL2" else "SSUBL/SSUBL2"
      | 3  => if u then "USUBW/USUBW2" else "SSUBW/SSUBW2"
      | 4  => if u then "RADDHN/RADDHN2" else "ADDHN/ADDHN2"
      | 5  => if u then "UABAL/UABAL2" else "SABAL/SABAL2"
      | 6  => if u then "RSUBHN/RSUBHN2" else "SUBHN/SUBHN2"
      | 7  => if u then "UABDL/UABDL2" else "SABDL/SABDL2"
      | 8  => if u then "UMLAL/UMLAL2" else "SMLAL/SMLAL2"
      | 9  => "SQDMLAL/SQDMLAL2"
      | 10 => if u then "UMLSL/UMLSL2" else "SMLSL/SMLSL2"
      | 11 => "SQDMLSL/SQDMLSL2"
      | 12 => if u then "UMULL/UMULL2" else "SMULL/SMULL2"
      | 13 => "SQDMULL/SQDMULL2"
      | 14 => "PMULL/PMULL2"
      | _  => "three-different"
    (toString "unsupported AdvSIMD encoding class three-different " ++ toString (mnem) ++ toString " (insn " ++ toString (insnHex) ++ toString ", q=" ++ toString (q) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — not modeled in Arm64/Trusted/ISA" : String)
  -- 2. AdvSIMD vector by-element (`0:Q:U:01111:size:L:M:Rm:opcode:H:0:Rn:Rd`)
  else if (w &&& 0x9f000400#32) == 0x0f000000#32 then
    let q := if w.getLsbD 30 then 1 else 0
    let u := if w.getLsbD 29 then 1 else 0
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 12 4).toNat
    (toString "unsupported AdvSIMD encoding class vector-by-element (insn " ++ toString (insnHex) ++ toString ", q=" ++ toString (q) ++ toString " u=" ++ toString (u) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — not modeled in Arm64/Trusted/ISA" : String)
  -- 3. AdvSIMD scalar three-same (`01:U:11110:size:1:Rm:opcode:1:Rn:Rd`)
  else if (w &&& 0xdf200400#32) == 0x5e200400#32 then
    let u := w.getLsbD 29
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 11 5).toNat
    let mnem :=
      match opcode with
      | 1  => if u then "UQADD" else "SQADD"
      | 5  => if u then "UQSUB" else "SQSUB"
      | 6  => if u then "CMHI" else "CMGT"
      | 7  => if u then "CMHS" else "CMGE"
      | 8  => if u then "USHL" else "SSHL"
      | 9  => if u then "UQSHL" else "SQSHL"
      | 16 => if u then "SUB" else "ADD"
      | 17 => if u then "CMEQ" else "CMTST"
      | _  => "scalar-three-same"
    (toString "unsupported AdvSIMD encoding class scalar-three-same " ++ toString (mnem) ++ toString " (insn " ++ toString (insnHex) ++ toString ", u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 4. AdvSIMD scalar two-reg misc (`01:U:11110:size:10000:opcode:10:Rn:Rd`)
  else if (w &&& 0xdf3e0c00#32) == 0x5e200800#32 then
    let u := if w.getLsbD 29 then 1 else 0
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 12 5).toNat
    (toString "unsupported AdvSIMD encoding class scalar-two-reg-misc (insn " ++ toString (insnHex) ++ toString ", u=" ++ toString (u) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 5. AdvSIMD scalar pairwise (`01:U:11110:size:11000:opcode:10:Rn:Rd`)
  else if (w &&& 0xdf3e0c00#32) == 0x5e300800#32 then
    let u := if w.getLsbD 29 then 1 else 0
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 12 5).toNat
    (toString "unsupported AdvSIMD encoding class scalar-pairwise (insn " ++ toString (insnHex) ++ toString ", u=" ++ toString (u) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 6. AdvSIMD scalar shift by immediate (`01:U:111110:immh:immb:opcode:1:Rn:Rd`)
  else if (w &&& 0xdf800400#32) == 0x5f000400#32 then
    let u := if w.getLsbD 29 then 1 else 0
    let immh := (w.extractLsb' 19 4).toNat
    let immb := (w.extractLsb' 16 3).toNat
    let opcode := (w.extractLsb' 11 5).toNat
    (toString "unsupported AdvSIMD encoding class scalar-shift-imm (insn " ++ toString (insnHex) ++ toString ", u=" ++ toString (u) ++ toString " immh=" ++ toString (immh) ++ toString " immb=" ++ toString (immb) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 7. AdvSIMD scalar three-different (`01:U:11110:size:1:Rm:opcode:00:Rn:Rd`)
  else if (w &&& 0xdf200c00#32) == 0x5e200000#32 then
    let u := if w.getLsbD 29 then 1 else 0
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 12 4).toNat
    (toString "unsupported AdvSIMD encoding class scalar-three-different (insn " ++ toString (insnHex) ++ toString ", u=" ++ toString (u) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 8. AdvSIMD scalar by-element (`01:U:11111:size:L:M:Rm:opcode:H:0:Rn:Rd`)
  else if (w &&& 0xdf000400#32) == 0x5f000000#32 then
    let u := if w.getLsbD 29 then 1 else 0
    let size := (w.extractLsb' 22 2).toNat
    let opcode := (w.extractLsb' 12 4).toNat
    (toString "unsupported AdvSIMD encoding class scalar-by-element (insn " ++ toString (insnHex) ++ toString ", u=" ++ toString (u) ++ toString " size=" ++ toString (size) ++ toString " opcode=" ++ toString (opcode) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 9. AdvSIMD scalar copy (`01:op:11110000:imm5:0:imm4:1:Rn:Rd`)
  else if (w &&& 0xdfe08400#32) == 0x5e000400#32 then
    let op := if w.getLsbD 29 then 1 else 0
    let imm5 := (w.extractLsb' 16 5).toNat
    let imm4 := (w.extractLsb' 11 4).toNat
    (toString "unsupported AdvSIMD encoding class scalar-copy (insn " ++ toString (insnHex) ++ toString ", op=" ++ toString (op) ++ toString " imm5=" ++ toString (imm5) ++ toString " imm4=" ++ toString (imm4) ++ toString ") — scalar SIMD not modeled in Arm64/Trusted/ISA" : String)
  -- 10. AdvSIMD multi-structure LD2-LD4 / ST2-ST4 (`0:Q:001100:p:L:0:Rm:opcode:size:Rn:Rt`)
  else if (w &&& 0xbfbf0000#32) == 0x0c000000#32 || (w &&& 0xbfa00000#32) == 0x0c800000#32 then
    let q := if w.getLsbD 30 then 1 else 0
    let isLoad := w.getLsbD 22
    let opcode := (w.extractLsb' 12 4).toNat
    let size := (w.extractLsb' 10 2).toNat
    let mnem :=
      match opcode with
      | 8 => if isLoad then "LD2" else "ST2"
      | 4 => if isLoad then "LD3" else "ST3"
      | 0 => if isLoad then "LD4" else "ST4"
      | _ => if isLoad then "LD2-LD4" else "ST2-ST4"
    (toString "unsupported AdvSIMD encoding class multi-structure " ++ toString (mnem) ++ toString " (insn " ++ toString (insnHex) ++ toString ", q=" ++ toString (q) ++ toString " L=" ++ toString (if isLoad then 1 else 0) ++ toString " opcode=" ++ toString (opcode) ++ toString " size=" ++ toString (size) ++ toString ") — multi-structure LD2-LD4/ST2-ST4 not modeled in Arm64/Trusted/ISA" : String)
  -- 11. AdvSIMD single-structure LD1-LD4 / ST1-ST4 (`0:Q:001101:p:L:R:Rm:opcode:S:size:Rn:Rt`)
  else if (w &&& 0xbf800000#32) == 0x0d000000#32 then
    let q := if w.getLsbD 30 then 1 else 0
    let isLoad := if w.getLsbD 22 then 1 else 0
    let rBit := if w.getLsbD 21 then 1 else 0
    let opcode := (w.extractLsb' 13 3).toNat
    let size := (w.extractLsb' 10 2).toNat
    (toString "unsupported AdvSIMD encoding class single-structure LD1-LD4/ST1-ST4 (insn " ++ toString (insnHex) ++ toString ", q=" ++ toString (q) ++ toString " L=" ++ toString (isLoad) ++ toString " R=" ++ toString (rBit) ++ toString " opcode=" ++ toString (opcode) ++ toString " size=" ++ toString (size) ++ toString ") — not modeled in Arm64/Trusted/ISA" : String)
  -- 12. SVE (`op0 = 0010`)
  else if (w &&& 0x1e000000#32) == 0x04000000#32 then
    (toString "unsupported SVE instruction (insn " ++ toString (insnHex) ++ toString ") — SVE not modeled in Arm64/Trusted/ISA" : String)
  else
    (toString "unsupported instruction encoding (insn " ++ toString (insnHex) ++ toString ") — not modeled in Arm64/Trusted/ISA" : String)

/-- Format a descriptive unsupported/undecodable error at `addr` for raw 32-bit word `w`. -/
def describeUnsupportedAt (addr : BitVec 64) (w : BitVec 32) : String :=
  (toString "at " ++ toString (hexAddr64 addr) ++ toString ": " ++ toString (describeUnsupportedWord w) : String)

end Arm64


