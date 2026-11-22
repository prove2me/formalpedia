-- Prove2me | Definitions.Def_Arm64_ISA_Eval
-- name    : Arm64_ISA_Eval
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:04:01.168442+00:00
-- url     : https://prove2.me/theorems/a1c9f585-8e0e-45ab-9a5e-b1eb98248635
-- title:
--   Arm64.Trusted.ISA.Eval — ARM64 Instruction Evaluation Semantics
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/Eval.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Eval.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/Eval.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Eval.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/Eval.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also 45 interpolated strings written out as their elaboration `toString … ++ …`, because prove2.me rejects interpolated strings.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Syntax
public import Definitions.Def_Arm64_ISA_Memory
public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_ISA_Float

/-!
# ARM64 Instruction Evaluation Semantics (`Arm64.Eval`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Architectural execution semantics for single AArch64 A64
  instructions (`execInstWithSvc`, `noSyscalls`; `execInst` re-exported in `Arm64.Trusted.ISA.Semantics`),
  arithmetic/flag helpers (`AddWithCarry32`, `AddWithCarry64`, `ConditionHolds`), addressing and
  bitfield evaluators (`evalAddrMode`, `evalBitfield`), and AES round primitives (`aesSBoxTable`,
  `aesInvSBoxTable`, `evalAesOp`). Modeled Linux `svc #0` syscall families live in
  `Arm64/Trusted/Syscalls/`.
- **When to read**: Use `lean-sig outline Arm64/Trusted/ISA/Eval.lean` or `ProofLib/Eval.lean` / `WP.lean`
  during proofs (`wp_steps` reduces `execInst` automatically); read specific lines here only
  when auditing or extending instruction execution semantics.
-/

@[expose] public section

namespace Arm64


/-- 32-bit `AddWithCarry`: returns `(result, PState)` with exact architectural `NZCV` flags. -/
def AddWithCarry32 (x y : BitVec 32) (carryIn : Bool) : BitVec 32 × PState :=
  let cin : BitVec 33 := if carryIn then 1#33 else 0#33
  let usum : BitVec 33 := cin + (y.zeroExtend 33 + x.zeroExtend 33)
  let ssum : BitVec 33 := cin + (y.signExtend 33 + x.signExtend 33)
  let res : BitVec 32 := usum.truncate 32
  let n := res.msb
  let z := res == 0#32
  let c := usum.msb
  let v := ssum.msb != res.msb
  (res, { n, z, c, v })

/-- 64-bit `AddWithCarry`: returns `(result, PState)` with exact architectural `NZCV` flags. -/
def AddWithCarry64 (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × PState :=
  let cin : BitVec 65 := if carryIn then 1#65 else 0#65
  let usum : BitVec 65 := cin + (y.zeroExtend 65 + x.zeroExtend 65)
  let ssum : BitVec 65 := cin + (y.signExtend 65 + x.signExtend 65)
  let res : BitVec 64 := usum.truncate 64
  let n := res.msb
  let z := res == 0#64
  let c := usum.msb
  let v := ssum.msb != res.msb
  (res, { n, z, c, v })

/-- Evaluate whether a condition code `cond` holds in processor state `ps` (`ConditionHolds` in ARM ASL). -/
def ConditionHolds (cond : CondCode) (ps : PState) : Bool :=
  match cond with
  | .EQ => ps.z
  | .NE => !ps.z
  | .CS => ps.c
  | .CC => !ps.c
  | .MI => ps.n
  | .PL => !ps.n
  | .VS => ps.v
  | .VC => !ps.v
  | .HI => ps.c && !ps.z
  | .LS => !(ps.c && !ps.z)
  | .GE => ps.n == ps.v
  | .LT => ps.n != ps.v
  | .GT => !ps.z && (ps.n == ps.v)
  | .LE => !(!ps.z && (ps.n == ps.v))
  | .AL => true
  | .NV => true

/-- Shift a 32-bit value by `amount` (`0..31`). -/
def shift32 (val : BitVec 32) (op : ShiftType) (amount : Nat) : BitVec 32 :=
  let amt := amount % 32
  match op with
  | .LSL => val <<< amt
  | .LSR => val >>> amt
  | .ASR => val.sshiftRight amt
  | .ROR => val.rotateRight amt

/-- Shift a 64-bit value by `amount` (`0..63`). -/
def shift64 (val : BitVec 64) (op : ShiftType) (amount : Nat) : BitVec 64 :=
  let amt := amount % 64
  match op with
  | .LSL => val <<< amt
  | .LSR => val >>> amt
  | .ASR => val.sshiftRight amt
  | .ROR => val.rotateRight amt

/-- Shift a register value at width `w`. -/
def shiftVal (w : Width) (val : BitVec 64) (op : ShiftType) (amount : Nat) : BitVec 64 :=
  match w with
  | .W32 => (shift32 (val.truncate 32) op amount).zeroExtend 64
  | .W64 => shift64 val op amount

/-- Sign- or zero-extend a value according to `ExtendType` and shift left by `amount`. -/
def extendVal (w : Width) (val : BitVec 64) (ext : ExtendType) (amount : Nat) : BitVec 64 :=
  let ext64 : BitVec 64 :=
    match ext with
    | .UXTB => (val.truncate 8).zeroExtend 64
    | .UXTH => (val.truncate 16).zeroExtend 64
    | .UXTW => (val.truncate 32).zeroExtend 64
    | .UXTX => val
    | .SXTB => (val.truncate 8).signExtend 64
    | .SXTH => (val.truncate 16).signExtend 64
    | .SXTW => (val.truncate 32).signExtend 64
    | .SXTX => val
  let shifted := ext64 <<< amount
  match w with
  | .W32 => (shifted.truncate 32).zeroExtend 64
  | .W64 => shifted

/-- Evaluate an `AddSubOp` (`ADD`, `ADDS`, `SUB`, `SUBS`) on operands `x, y` at width `w`. -/
def evalAddSub (w : Width) (op : AddSubOp) (x y : BitVec 64) (carryIn : Option Bool := none) : BitVec 64 × Option PState :=
  let isSub := match op with | .SUB | .SUBS => true | .ADD | .ADDS => false
  let setFlags := match op with | .ADDS | .SUBS => true | .ADD | .SUB => false
  let cIn := match carryIn with | some c => c | none => isSub
  match w with
  | .W32 =>
    let x32 := x.truncate 32
    let y32 := if isSub then ~~~(y.truncate 32) else y.truncate 32
    let (res32, ps) := AddWithCarry32 x32 y32 cIn
    (res32.zeroExtend 64, if setFlags then some ps else none)
  | .W64 =>
    let y64 := if isSub then ~~~y else y
    let (res64, ps) := AddWithCarry64 x y64 cIn
    (res64, if setFlags then some ps else none)

/-- Evaluate a `LogicalOp` (`AND`, `BIC`, `ORR`, `ORN`, `EOR`, `EON`, `ANDS`, `BICS`) at width `w`. -/
def evalLogical (w : Width) (op : LogicalOp) (x y : BitVec 64) (psOld : PState) : BitVec 64 × Option PState :=
  let yMod := match op with
    | .BIC | .ORN | .EON | .BICS => ~~~y
    | _ => y
  let raw := match op with
    | .AND | .BIC | .ANDS | .BICS => x &&& yMod
    | .ORR | .ORN => x ||| yMod
    | .EOR | .EON => x ^^^ yMod
  let setFlags := match op with | .ANDS | .BICS => true | _ => false
  match w with
  | .W32 =>
    let res32 := raw.truncate 32
    let ps : PState := { n := res32.msb, z := res32 == 0#32, c := false, v := false }
    let _ := psOld
    (res32.zeroExtend 64, if setFlags then some ps else none)
  | .W64 =>
    let ps : PState := { n := raw.msb, z := raw == 0#64, c := false, v := false }
    (raw, if setFlags then some ps else none)

/-- Evaluate `SBFM`, `BFM`, `UBFM` bitfield move instruction at width `w`. -/
def evalBitfield (w : Width) (op : BitfieldOp) (dst src : BitVec 64) (immr imms : Nat) : BitVec 64 :=
  let N : Nat := match w with | .W32 => 32 | .W64 => 64
  let srcW : BitVec 64 := match w with | .W32 => (src.truncate 32).zeroExtend 64 | .W64 => src
  let dstW : BitVec 64 := match w with | .W32 => (dst.truncate 32).zeroExtend 64 | .W64 => dst
  let immr := immr % N
  let imms := imms % N
  -- Fast path for standard LSR, ASR, LSL encodings so symbolic execution stays compact
  if op == .UBFM && imms + 1 == N then
    let res := srcW >>> immr
    match w with | .W32 => (res.truncate 32).zeroExtend 64 | .W64 => res
  else if op == .SBFM && imms + 1 == N then
    let res := match w with
      | .W32 => ((src.truncate 32).sshiftRight immr).zeroExtend 64
      | .W64 => src.sshiftRight immr
    res
  else if op == .UBFM && immr > imms && imms + 1 == immr then
    let shift := N - immr
    let res := srcW <<< shift
    match w with | .W32 => (res.truncate 32).zeroExtend 64 | .W64 => res
  else
    let res64 : BitVec 64 :=
      if imms >= immr then
        let len := imms - immr + 1
        let fieldMask : BitVec 64 := BitVec.ofNat 64 (Nat.shiftLeft 1 len - 1)
        let extracted := (srcW >>> immr) &&& fieldMask
        match op with
        | .UBFM => extracted
        | .SBFM =>
          let signFill : BitVec 64 := if srcW.getLsbD imms then 0xffffffffffffffff#64 else 0#64
          extracted ||| (signFill &&& ~~~fieldMask)
        | .BFM  => (dstW &&& ~~~fieldMask) ||| extracted
      else
        let len := imms + 1
        let pos := N - immr
        let lowMask : BitVec 64 := BitVec.ofNat 64 (Nat.shiftLeft 1 len - 1)
        let fieldMask : BitVec 64 := lowMask <<< pos
        let positioned := (srcW &&& lowMask) <<< pos
        match op with
        | .UBFM => positioned
        | .SBFM =>
          let signFill : BitVec 64 := if srcW.getLsbD imms then 0xffffffffffffffff#64 else 0#64
          let topMask : BitVec 64 := if pos + len >= 64 then 0#64 else ~~~(BitVec.ofNat 64 (Nat.shiftLeft 1 (pos + len) - 1))
          positioned ||| (signFill &&& topMask)
        | .BFM  => (dstW &&& ~~~fieldMask) ||| positioned
    match w with
    | .W32 => (res64.truncate 32).zeroExtend 64
    | .W64 => res64

/-- Count leading zeros in an `n`-bit bitvector. -/
def countLeadingZeros {n : Nat} (bv : BitVec n) : Nat :=
  let rec loop (k : Nat) : Nat :=
    match k with
    | 0 => n
    | k' + 1 =>
      if bv.getLsbD k' then n - 1 - k'
      else loop k'
  loop n

/-- Count leading sign bits (number of bits following MSB that equal MSB) in an `n`-bit bitvector. -/
def countLeadingSigns {n : Nat} (bv : BitVec n) : Nat :=
  if n <= 1 then 0
  else
    let sign := bv.msb
    let rec loop (k : Nat) : Nat :=
      match k with
      | 0 => n - 1
      | k' + 1 =>
        if bv.getLsbD k' != sign then (n - 1) - 1 - k'
        else loop k'
    loop (n - 1)

/-- Reverse all bits in an `n`-bit bitvector. -/
def reverseBits {n : Nat} (bv : BitVec n) : BitVec n :=
  Id.run do
    let mut acc : BitVec n := 0
    for i in [0:n] do
      if bv.getLsbD i then
        acc := acc ||| (BitVec.ofNat n 1 <<< (n - 1 - i))
    return acc

/-- Reverse bytes within each 16-bit halfword of a 64-bit value (`REV16`). -/
def rev16_64 (v : BitVec 64) : BitVec 64 :=
  let b0 := v.extractLsb' 0 8
  let b1 := v.extractLsb' 8 8
  let b2 := v.extractLsb' 16 8
  let b3 := v.extractLsb' 24 8
  let b4 := v.extractLsb' 32 8
  let b5 := v.extractLsb' 40 8
  let b6 := v.extractLsb' 48 8
  let b7 := v.extractLsb' 56 8
  b6 ++ b7 ++ b4 ++ b5 ++ b2 ++ b3 ++ b0 ++ b1

/-- Reverse bytes within each 32-bit word of a 64-bit value (`REV32`). -/
def rev32_64 (v : BitVec 64) : BitVec 64 :=
  let b0 := v.extractLsb' 0 8
  let b1 := v.extractLsb' 8 8
  let b2 := v.extractLsb' 16 8
  let b3 := v.extractLsb' 24 8
  let b4 := v.extractLsb' 32 8
  let b5 := v.extractLsb' 40 8
  let b6 := v.extractLsb' 48 8
  let b7 := v.extractLsb' 56 8
  b4 ++ b5 ++ b6 ++ b7 ++ b0 ++ b1 ++ b2 ++ b3

/-- Reverse all 8 bytes of a 64-bit value (`REV` / `REV64`). -/
def rev64 (v : BitVec 64) : BitVec 64 :=
  let b0 := v.extractLsb' 0 8
  let b1 := v.extractLsb' 8 8
  let b2 := v.extractLsb' 16 8
  let b3 := v.extractLsb' 24 8
  let b4 := v.extractLsb' 32 8
  let b5 := v.extractLsb' 40 8
  let b6 := v.extractLsb' 48 8
  let b7 := v.extractLsb' 56 8
  b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7

/-- Extract the base register of an `AddrMode`. -/
@[inline] def AddrMode.baseReg : AddrMode → Reg
  | .Offset base _ | .UnscaledOffset base _ | .PreIndex base _
  | .PostIndex base _ | .RegOffset base _ _ _ => base

-- https://developer.arm.com/documentation/ddi0487/latest/-Part-D-The-AArch64-System-Level-Architecture/-Chapter-D1-The-AArch64-System-Level-Programmers--Model/-D1-4-Exceptions/-D1-4-10-Program-Counter-and-stack-pointer-alignment
/-- Architectural `CheckSPAlignment()` check for a base register `r`:
    if `r = .sp`, then `s.spAligned` (`(s.sp &&& 0b1111#64) == 0#64`) must hold.
    Structured ASL: `arm-asl-extract query CheckSPAlignment` (`shared_pseudocode.xml`).
    See [ARM Architecture Reference Manual Section D1.4.10](https://developer.arm.com/documentation/ddi0487/latest/%2DPart-D-The-AArch64-System-Level-Architecture/%2DChapter-D1-The-AArch64-System-Level-Programmers--Model/%2DD1-4-Exceptions/%2DD1-4-10-Program-Counter-and-stack-pointer-alignment). -/
@[inline] def checkRegSPAligned (s : State) (r : Reg) : Bool :=
  match r with
  | .sp => s.spAligned
  | _ => true

/-- Architectural `CheckSPAlignment()` check for an `AddrMode`:
    if `addr.baseReg = .sp`, then `s.spAligned` must hold. -/
@[inline] def checkAddrSPAligned (s : State) (addr : AddrMode) : Bool :=
  checkRegSPAligned s addr.baseReg

-- https://developer.arm.com/documentation/ddi0487/latest/-Part-B-The-AArch64-Application-Level-Architecture/-Chapter-B2-The-AArch64-Application-Level-Memory-Model/-B2-8-Alignment-support/-B2-8-2-Alignment-of-data-accesses
/-- Architectural natural-alignment check for `MemWidth` (`IsAligned(address, size)` in ARMv8-A):
    required by load-acquire (`LDAR*`), store-release (`STLR*`), and load/store-exclusive
    (`LDXR*`/`LDAXR*`/`STXR*`/`STLXR*`) instructions even when `SCTLR_EL1.A == 0`.
    See [ARM Architecture Reference Manual Section B2.8.2: Alignment of data accesses](https://developer.arm.com/documentation/ddi0487/latest/%2DPart-B-The-AArch64-Application-Level-Architecture/%2DChapter-B2-The-AArch64-Application-Level-Memory-Model/%2DB2-8-Alignment-support/%2DB2-8-2-Alignment-of-data-accesses). -/
@[inline] def MemWidth.isAligned (sz : MemWidth) (ea : BitVec 64) : Bool :=
  match sz with
  | .B8  => true
  | .H16 => (ea &&& 0b1#64) == 0#64
  | .W32 => (ea &&& 0b11#64) == 0#64
  | .X64 => (ea &&& 0b111#64) == 0#64

/-- Compute effective memory address and optional post-access base register value for `AddrMode`. -/
def evalAddrMode (s : State) (addr : AddrMode) : BitVec 64 × Option (Reg × BitVec 64) :=
  match addr with
  | .Offset base off =>
    (s.readReg64 base + off, none)
  | .UnscaledOffset base off =>
    (s.readReg64 base + off, none)
  | .PreIndex base off =>
    let ea := s.readReg64 base + off
    (ea, some (base, ea))
  | .PostIndex base off =>
    let baseVal := s.readReg64 base
    (baseVal, some (base, baseVal + off))
  | .RegOffset base index ext amount =>
    let baseVal := s.readReg64 base
    let idxVal := extendVal .W64 (s.readReg64 index) ext amount
    (baseVal + idxVal, none)

/-!
## SIMD & AES Helper Operations
-/

/-- Extract an `esize`-bit lane at `idx` from a 128-bit vector. -/
def getSimdLane (v : BitVec 128) (esize : Nat) (idx : Nat) : BitVec 128 :=
  (v >>> (idx * esize)) &&& ((1#128 <<< esize) - 1#128)

/-- Apply a unary lane-wise function across `numLanes` lanes of `esize` bits. -/
def mapSimdLanes (q : Bool) (esize : Nat) (v : BitVec 128) (f : BitVec 128 → BitVec 128) : BitVec 128 :=
  let totalBits := if q then 128 else 64
  let numLanes := totalBits / esize
  let mask : BitVec 128 := (1#128 <<< esize) - 1#128
  Id.run do
    let mut acc : BitVec 128 := 0#128
    for i in [0:numLanes] do
      let lane := (v >>> (i * esize)) &&& mask
      let outLane := (f lane) &&& mask
      acc := acc ||| (outLane <<< (i * esize))
    return acc

/-- Apply a binary lane-wise function across `numLanes` lanes of `esize` bits. -/
def zipSimdLanes (q : Bool) (esize : Nat) (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) : BitVec 128 :=
  let totalBits := if q then 128 else 64
  let numLanes := totalBits / esize
  let mask : BitVec 128 := (1#128 <<< esize) - 1#128
  Id.run do
    let mut acc : BitVec 128 := 0#128
    for i in [0:numLanes] do
      let a := (vn >>> (i * esize)) &&& mask
      let b := (vm >>> (i * esize)) &&& mask
      let outLane := (f a b) &&& mask
      acc := acc ||| (outLane <<< (i * esize))
    return acc

/-- FIPS-197 AES Forward S-Box (256 bytes). -/
def aesSBoxTable : Array UInt8 := #[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]

/-- FIPS-197 AES Inverse S-Box (256 bytes). -/
def aesInvSBoxTable : Array UInt8 := #[
  0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
  0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
  0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
  0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
  0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
  0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
  0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
  0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
  0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
  0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
  0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
  0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
  0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
  0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
  0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
  0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
]

/-- Multiply in GF(2^8) modulo `x^8 + x^4 + x^3 + x + 1`. -/
def gfMul (a b : UInt8) : UInt8 := Id.run do
  let mut p : UInt8 := 0
  let mut x : UInt8 := a
  let mut y : UInt8 := b
  for _ in [0:8] do
    if (y &&& 1) != 0 then
      p := p ^^^ x
    let hi := (x &&& 0x80) != 0
    x := x <<< 1
    if hi then
      x := x ^^^ 0x1b
    y := y >>> 1
  return p

/-- Evaluate ARMv8 `AESE`, `AESD`, `AESMC`, `AESIMC` on 128-bit blocks. -/
def evalAesOp (op : AesOp) (vd vn : BitVec 128) : BitVec 128 := Id.run do
  let getByte (v : BitVec 128) (i : Nat) : UInt8 :=
    UInt8.ofNat ((v >>> (i * 8)).truncate 8).toNat
  let packBytes (bs : Array UInt8) : BitVec 128 := Id.run do
    let mut acc : BitVec 128 := 0#128
    for i in [0:16] do
      let b : BitVec 128 := BitVec.ofNat 128 bs[i]!.toNat
      acc := acc ||| (b <<< (i * 8))
    return acc
  match op with
  | .AESE =>
    let x := vd ^^^ vn
    let perm : Array Nat := #[0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11]
    let mut out : Array UInt8 := Array.mkEmpty 16
    for i in [0:16] do
      let b := getByte x perm[i]!
      out := out.push (aesSBoxTable[b.toNat]!)
    return packBytes out
  | .AESD =>
    let x := vd ^^^ vn
    let perm : Array Nat := #[0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3]
    let mut out : Array UInt8 := Array.mkEmpty 16
    for i in [0:16] do
      let b := getByte x perm[i]!
      out := out.push (aesInvSBoxTable[b.toNat]!)
    return packBytes out
  | .AESMC =>
    let mut out : Array UInt8 := Array.mkEmpty 16
    for c in [0:4] do
      let s0 := getByte vn (4 * c)
      let s1 := getByte vn (4 * c + 1)
      let s2 := getByte vn (4 * c + 2)
      let s3 := getByte vn (4 * c + 3)
      out := out.push (gfMul 2 s0 ^^^ gfMul 3 s1 ^^^ s2 ^^^ s3)
      out := out.push (s0 ^^^ gfMul 2 s1 ^^^ gfMul 3 s2 ^^^ s3)
      out := out.push (s0 ^^^ s1 ^^^ gfMul 2 s2 ^^^ gfMul 3 s3)
      out := out.push (gfMul 3 s0 ^^^ s1 ^^^ s2 ^^^ gfMul 2 s3)
    return packBytes out
  | .AESIMC =>
    let mut out : Array UInt8 := Array.mkEmpty 16
    for c in [0:4] do
      let s0 := getByte vn (4 * c)
      let s1 := getByte vn (4 * c + 1)
      let s2 := getByte vn (4 * c + 2)
      let s3 := getByte vn (4 * c + 3)
      out := out.push (gfMul 0x0e s0 ^^^ gfMul 0x0b s1 ^^^ gfMul 0x0d s2 ^^^ gfMul 0x09 s3)
      out := out.push (gfMul 0x09 s0 ^^^ gfMul 0x0e s1 ^^^ gfMul 0x0b s2 ^^^ gfMul 0x0d s3)
      out := out.push (gfMul 0x0d s0 ^^^ gfMul 0x09 s1 ^^^ gfMul 0x0e s2 ^^^ gfMul 0x0b s3)
      out := out.push (gfMul 0x0b s0 ^^^ gfMul 0x0d s1 ^^^ gfMul 0x09 s2 ^^^ gfMul 0x0e s3)
    return packBytes out

/-- Expand an 8-bit ARMv8 floating-point immediate (`VFPExpandImm`) to IEEE-754 binary32. -/
def vfpExpandImm32 (imm8 : BitVec 8) : BitVec 32 :=
  let sign : BitVec 1 := imm8.extractLsb' 7 1
  let notB6 : BitVec 1 := ~~~(imm8.extractLsb' 6 1)
  let repB6 : BitVec 5 := if imm8.getLsbD 6 then 0b11111#5 else 0b00000#5
  let rest : BitVec 6 := imm8.extractLsb' 0 6
  sign ++ notB6 ++ repB6 ++ rest ++ 0#19

/-- Expand an 8-bit ARMv8 floating-point immediate (`VFPExpandImm`) to IEEE-754 binary64. -/
def vfpExpandImm64 (imm8 : BitVec 8) : BitVec 64 :=
  let sign : BitVec 1 := imm8.extractLsb' 7 1
  let notB6 : BitVec 1 := ~~~(imm8.extractLsb' 6 1)
  let repB6 : BitVec 8 := if imm8.getLsbD 6 then 0xff#8 else 0x00#8
  let rest : BitVec 6 := imm8.extractLsb' 0 6
  sign ++ notB6 ++ repB6 ++ rest ++ 0#48

/-!
## Instruction Execution Helpers
-/

/-- Execute an add/subtract (immediate) operation (`ADD`, `ADDS`, `SUB`, `SUBS`). -/
@[simp, reducible] def execAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12) (shift12 : Bool) (s : State) : State :=
  let x := s.readReg w rn
  let imm : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
  let (res, optPs) := evalAddSub w op x imm none
  let s1 := s.writeReg w rd res
  let s2 := match optPs with | some ps => s1.setPState ps | none => s1
  s2.advancePC

/-- Execute an add/subtract (extended register) operation (`ADD`, `ADDS`, `SUB`, `SUBS`). -/
@[simp, reducible] def execAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType) (amount : Nat) (s : State) : State :=
  let x := s.readReg w rn
  let y := extendVal w (s.readReg64 rm) ext amount
  let (res, optPs) := evalAddSub w op x y none
  let s1 := s.writeReg w rd res
  let s2 := match optPs with | some ps => s1.setPState ps | none => s1
  s2.advancePC

/-- Execute an add/subtract (shifted register) operation (`ADD`, `ADDS`, `SUB`, `SUBS`). -/
@[simp, reducible] def execAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) (s : State) : State :=
  let x := s.readReg w rn
  let y := shiftVal w (s.readReg w rm) shift amount
  let (res, optPs) := evalAddSub w op x y none
  let s1 := s.writeReg w rd res
  let s2 := match optPs with | some ps => s1.setPState ps | none => s1
  s2.advancePC

/-- Execute an `ADC` / `ADCS` / `SBC` / `SBCS` operation. -/
@[simp, reducible] def execAddSubCarry (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : State) : State :=
  let x := s.readReg w rn
  let y := s.readReg w rm
  let (res, optPs) := evalAddSub w op x y (some s.pstate.c)
  let s1 := s.writeReg w rd res
  let s2 := match optPs with | some ps => s1.setPState ps | none => s1
  s2.advancePC

/-- Execute a logical (immediate) operation (`AND`, `ORR`, `EOR`, `ANDS`). -/
@[simp, reducible] def execLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) (s : State) : State :=
  let x := s.readReg w rn
  let (res, optPs) := evalLogical w op x mask s.pstate
  let s1 := s.writeReg w rd res
  let s2 := match optPs with | some ps => s1.setPState ps | none => s1
  s2.advancePC

/-- Execute a logical (shifted register) operation (`AND`, `BIC`, `ORR`, `ORN`, `EOR`, `EON`, `ANDS`, `BICS`). -/
@[simp, reducible] def execLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) (s : State) : State :=
  let x := s.readReg w rn
  let y := shiftVal w (s.readReg w rm) shift amount
  let (res, optPs) := evalLogical w op x y s.pstate
  let s1 := s.writeReg w rd res
  let s2 := match optPs with | some ps => s1.setPState ps | none => s1
  s2.advancePC

/-- Execute a move wide (`MOVZ`, `MOVN`, `MOVK`) operation. -/
@[simp, reducible] def execMoveWide (w : Width) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16) (hw : Nat) (s : State) : State :=
  let shifted : BitVec 64 := (imm16.zeroExtend 64) <<< hw
  let res : BitVec 64 :=
    match op with
    | .MOVZ => shifted
    | .MOVN => ~~~shifted
    | .MOVK =>
      let old := s.readReg w rd
      let clearMask := ~~~(0xffff#64 <<< hw)
      (old &&& clearMask) ||| shifted
  (s.writeReg w rd res).advancePC

/-- Execute a bitfield move (`SBFM`, `BFM`, `UBFM`) operation. -/
@[simp, reducible] def execBitfield (w : Width) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat) (s : State) : State :=
  let dst := s.readReg w rd
  let src := s.readReg w rn
  let res := evalBitfield w op dst src immr imms
  (s.writeReg w rd res).advancePC

/-- Execute a conditional select (`CSEL`, `CSINC`, `CSINV`, `CSNEG`) operation. -/
@[simp, reducible] def execCondSelect (w : Width) (op : CondSelectOp) (rd rn rm : Reg) (cond : CondCode) (s : State) : State :=
  let holds := ConditionHolds cond s.pstate
  let res : BitVec 64 :=
    if holds then
      s.readReg w rn
    else
      let mVal := s.readReg w rm
      match op with
      | .CSEL  => mVal
      | .CSINC => mVal + 1#64
      | .CSINV => ~~~mVal
      | .CSNEG => 0#64 - mVal
  (s.writeReg w rd res).advancePC

/-- Execute a conditional compare (`CCMP`, `CCMN`) operation. -/
@[simp, reducible] def execCondCompare (w : Width) (isSub : Bool) (isImm : Bool)
    (rn : Reg) (rhs : BitVec 64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : State) : State :=
  if ConditionHolds cond s.pstate then
    let x := s.readReg w rn
    let y := if isImm then rhs else s.readReg w rm
    let op : AddSubOp := if isSub then .SUBS else .ADDS
    let (_, optPs) := evalAddSub w op x y none
    let s1 := match optPs with | some ps => s.setPState ps | none => s
    s1.advancePC
  else
    (s.setPState (PState.ofBits4 nzcv)).advancePC

/-- Execute a 1-source data processing (`RBIT`, `REV16`, `REV32`, `REV`, `CLZ`, `CLS`) operation. -/
@[simp, reducible] def execDataProc1 (w : Width) (op : DataProc1Op) (rd rn : Reg) (s : State) : State :=
  let v := s.readReg w rn
  let res : BitVec 64 :=
    match w, op with
    | .W32, .RBIT  => (reverseBits (v.truncate 32)).zeroExtend 64
    | .W64, .RBIT  => reverseBits v
    | .W32, .REV16 => ((rev16_64 v).truncate 32).zeroExtend 64
    | .W64, .REV16 => rev16_64 v
    | .W32, .REV32 => ((rev32_64 v).truncate 32).zeroExtend 64
    | .W64, .REV32 => rev32_64 v
    | .W32, .REV   => ((rev32_64 v).truncate 32).zeroExtend 64
    | .W64, .REV   => rev64 v
    | .W32, .CLZ   => BitVec.ofNat 64 (countLeadingZeros (v.truncate 32))
    | .W64, .CLZ   => BitVec.ofNat 64 (countLeadingZeros v)
    | .W32, .CLS   => BitVec.ofNat 64 (countLeadingSigns (v.truncate 32))
    | .W64, .CLS   => BitVec.ofNat 64 (countLeadingSigns v)
  (s.writeReg w rd res).advancePC

/-- Execute a 2-source data processing (`UDIV`, `SDIV`, `LSLV`, `LSRV`, `ASRV`, `RORV`) operation. -/
@[simp, reducible] def execDataProc2 (w : Width) (op : DataProc2Op) (rd rn rm : Reg) (s : State) : State :=
  let x := s.readReg w rn
  let y := s.readReg w rm
  let res : BitVec 64 :=
    match w, op with
    | .W32, .UDIV =>
      let x32 := x.truncate 32
      let y32 := y.truncate 32
      (if y32 == 0#32 then 0#32 else x32 / y32).zeroExtend 64
    | .W64, .UDIV =>
      if y == 0#64 then 0#64 else x / y
    | .W32, .SDIV =>
      let x32 := x.truncate 32
      let y32 := y.truncate 32
      (if y32 == 0#32 then 0#32 else BitVec.sdiv x32 y32).zeroExtend 64
    | .W64, .SDIV =>
      if y == 0#64 then 0#64 else BitVec.sdiv x y
    | .W32, .LSLV => (shift32 (x.truncate 32) .LSL (y.truncate 32).toNat).zeroExtend 64
    | .W64, .LSLV => shift64 x .LSL y.toNat
    | .W32, .LSRV => (shift32 (x.truncate 32) .LSR (y.truncate 32).toNat).zeroExtend 64
    | .W64, .LSRV => shift64 x .LSR y.toNat
    | .W32, .ASRV => (shift32 (x.truncate 32) .ASR (y.truncate 32).toNat).zeroExtend 64
    | .W64, .ASRV => shift64 x .ASR y.toNat
    | .W32, .RORV => (shift32 (x.truncate 32) .ROR (y.truncate 32).toNat).zeroExtend 64
    | .W64, .RORV => shift64 x .ROR y.toNat
  (s.writeReg w rd res).advancePC

/-- Execute a 3-source multiply-accumulate (`MADD`, `MSUB`, `SMADDL`, `SMSUBL`, `SMULH`, `UMADDL`, `UMSUBL`, `UMULH`) operation. -/
@[simp, reducible] def execDataProc3 (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg) (s : State) : State :=
  let res : BitVec 64 :=
    match op with
    | .MADD =>
      match w with
      | .W32 => ((s.readReg32 ra) + (s.readReg32 rn) * (s.readReg32 rm)).zeroExtend 64
      | .W64 => (s.readReg64 ra) + (s.readReg64 rn) * (s.readReg64 rm)
    | .MSUB =>
      match w with
      | .W32 => ((s.readReg32 ra) - (s.readReg32 rn) * (s.readReg32 rm)).zeroExtend 64
      | .W64 => (s.readReg64 ra) - (s.readReg64 rn) * (s.readReg64 rm)
    | .SMADDL =>
      let n64 := (s.readReg32 rn).signExtend 64
      let m64 := (s.readReg32 rm).signExtend 64
      (s.readReg64 ra) + n64 * m64
    | .SMSUBL =>
      let n64 := (s.readReg32 rn).signExtend 64
      let m64 := (s.readReg32 rm).signExtend 64
      (s.readReg64 ra) - n64 * m64
    | .UMADDL =>
      let n64 := (s.readReg32 rn).zeroExtend 64
      let m64 := (s.readReg32 rm).zeroExtend 64
      (s.readReg64 ra) + n64 * m64
    | .UMSUBL =>
      let n64 := (s.readReg32 rn).zeroExtend 64
      let m64 := (s.readReg32 rm).zeroExtend 64
      (s.readReg64 ra) - n64 * m64
    | .SMULH =>
      let n128 := (s.readReg64 rn).signExtend 128
      let m128 := (s.readReg64 rm).signExtend 128
      ((n128 * m128) >>> 64).truncate 64
    | .UMULH =>
      let n128 := (s.readReg64 rn).zeroExtend 128
      let m128 := (s.readReg64 rm).zeroExtend 128
      ((n128 * m128) >>> 64).truncate 64
  (s.writeReg w rd res).advancePC

/-- Execute a single-register load (`LDR`, `LDUR`, `LDRB`, `LDURB`, `LDRSB`, `LDURSB`, `LDRH`, `LDURH`, `LDRSH`, `LDURSH`, `LDRSW`, `LDURSW`). -/
@[simp, reducible] def execLdr (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    if !s.mem.canRead ea size.bytes then
      s.setStatus (.Exception "permission fault")
    else
    let val := s.mem.readSized size signed ea
    let s1 := match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s
    (s1.writeReg w rt val).advancePC

/-- Execute a PC-relative literal load (`LDR (literal)`, `LDRSW (literal)`). -/
@[simp, reducible] def execLdrLit (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (offset : BitVec 64) (s : State) : State :=
  let ea := s.pc + offset
  if !s.mem.canRead ea size.bytes then
    s.setStatus (.Exception "permission fault")
  else
  let val := s.mem.readSized size signed ea
  (s.writeReg w rt val).advancePC

/-- Execute a single-register store (`STR`, `STUR`, `STRB`, `STURB`, `STRH`, `STURH`). -/
@[simp, reducible] def execStr (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    if !s.mem.canWrite ea size.bytes then
      s.setStatus (.Exception "permission fault")
    else
    let val := s.readReg64 rt
    let s1 := s.setMem (s.mem.writeSized size ea val)
    let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
    s2.advancePC

/-- Execute a register-pair load (`LDP`, `LDPSW`). Each element's range is checked separately. -/
@[simp, reducible] def execLdp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    let stepBytes : BitVec 64 := if signed then 4#64 else match w with | .W32 => 4#64 | .W64 => 8#64
    let sz : MemWidth := if signed then .W32 else match w with | .W32 => .W32 | .W64 => .X64
    if !(s.mem.canRead ea sz.bytes && s.mem.canRead (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
    let v1 := s.mem.readSized sz signed ea
    let v2 := s.mem.readSized sz signed (ea + stepBytes)
    let outW : Width := if signed then .W64 else w
    let s1 := match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s
    let s2 := s1.writeReg outW rt1 v1
    let s3 := s2.writeReg outW rt2 v2
    s3.advancePC

/-- Execute a register-pair store (`STP`). Each element's range is checked separately. -/
@[simp, reducible] def execStp (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    let stepBytes : BitVec 64 := match w with | .W32 => 4#64 | .W64 => 8#64
    let sz : MemWidth := match w with | .W32 => .W32 | .W64 => .X64
    if !(s.mem.canWrite ea sz.bytes && s.mem.canWrite (ea + stepBytes) sz.bytes) then
      s.setStatus (.Exception "permission fault")
    else
    let v1 := s.readReg64 rt1
    let v2 := s.readReg64 rt2
    let m1 := s.mem.writeSized sz ea v1
    let m2 := m1.writeSized sz (ea + stepBytes) v2
    let s1 := s.setMem m2
    let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
    s2.advancePC

/-- LSE atomic `new := op(old, rs)` at access width `sz` (inputs/result masked to `sz`; signed
    min/max compare the `sz`-bit two's-complement values). ASL `MemAtomic` / `AArch64.MemAtomic`. -/
def evalAtomicOp (op : AtomicOp) (sz : MemWidth) (old rs : BitVec 64) : BitVec 64 :=
  let bits := sz.bytes * 8
  let mask : BitVec 64 := if bits ≥ 64 then BitVec.allOnes 64 else (1#64 <<< bits) - 1#64
  let a := old &&& mask
  let b := rs &&& mask
  let signBit : BitVec 64 := 1#64 <<< (bits - 1)
  let sLt (x y : BitVec 64) : Bool := BitVec.ult (x ^^^ signBit) (y ^^^ signBit)
  let res : BitVec 64 :=
    match op with
    | .ADD  => a + b
    | .CLR  => a &&& ~~~b
    | .EOR  => a ^^^ b
    | .SET  => a ||| b
    | .SMAX => if sLt a b then b else a
    | .SMIN => if sLt b a then b else a
    | .UMAX => if BitVec.ult a b then b else a
    | .UMIN => if BitVec.ult b a then b else a
    | .SWP  => b
  res &&& mask

/-- ASL `Poly32Mod2(data<n-1:0>, poly)` (polynomial division over GF(2)), with `data` held in
    the low `n ≤ 96` bits of a 96-bit vector. -/
def poly32Mod2 (n : Nat) (data : BitVec 96) (poly : BitVec 32) : BitVec 32 := Id.run do
  let mut d := data
  for j in [0:n - 32] do
    let i := n - 1 - j
    if d.getLsbD i then
      d := d ^^^ ((poly.zeroExtend 96) <<< (i - 32))
  return d.truncate 32

/-- `CRC32{B,H,W,X}` (`c = false`, poly `0x04C11DB7`) / `CRC32C*` (`c = true`, poly `0x1EDC6F41`):
    ASL `BitReverse(Poly32Mod2(BitReverse(acc):Zeros(size) EOR BitReverse(val<size-1:0>):Zeros(32), poly))`. -/
def evalCrc32 (c : Bool) (sz : MemWidth) (acc : BitVec 32) (val : BitVec 64) : BitVec 32 :=
  let size := sz.bytes * 8
  let poly : BitVec 32 := if c then 0x1EDC6F41#32 else 0x04C11DB7#32
  let tempacc : BitVec 96 := ((reverseBits acc).zeroExtend 96) <<< size
  let revVal : BitVec 64 := (reverseBits val) >>> (64 - size)
  let tempval : BitVec 96 := (revVal.zeroExtend 96) <<< 32
  reverseBits (poly32Mod2 (size + 32) (tempacc ^^^ tempval) poly)

/-- ASL `PolynomialMult(op1<esize-1:0>, op2<esize-1:0>)` (carry-less polynomial multiplication
    over GF(2)), returning the `2 * esize`-bit product zero-extended to 128 bits (`esize ≤ 64`). -/
def polyMul (esize : Nat) (op1 op2 : BitVec 64) : BitVec 128 :=
  let ext2 : BitVec 128 := op2.zeroExtend 128
  (List.range esize).foldl (fun res i =>
    if op1.getLsbD i then res ^^^ (ext2 <<< i) else res) 0#128

/-- Evaluate `PMULL` (`q = false`) / `PMULL2` (`q = true`) on 128-bit source vectors `vn`, `vm`
    (`is64 = false` for `8H <- 8B/16B` with `esize = 8`; `is64 = true` for `1Q <- 1D/2D` with
    `esize = 64`). ASL `A64.simd_dp.asimddiff.PMULL_asimddiff_L`. -/
def evalPmull (q is64 : Bool) (vn vm : BitVec 128) : BitVec 128 :=
  let op1 : BitVec 64 := if q then vn.extractLsb' 64 64 else vn.truncate 64
  let op2 : BitVec 64 := if q then vm.extractLsb' 64 64 else vm.truncate 64
  if is64 then
    polyMul 64 op1 op2
  else
    (List.range 8).foldl (fun acc e =>
      let e1 : BitVec 64 := (op1 >>> (e * 8)) &&& 0xff#64
      let e2 : BitVec 64 := (op2 >>> (e * 8)) &&& 0xff#64
      acc ||| (polyMul 8 e1 e2 <<< (e * 16))) 0#128

/-- ASL `SHAchoose(x, y, z)` (`shared/functions/crypto/SHAchoose`): `((y EOR z) AND x) EOR z`. -/
def shaChoose32 (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z

/-- ASL `SHAparity(x, y, z)` (`shared/functions/crypto/SHAparity`): `x EOR y EOR z`. -/
def shaParity32 (x y z : BitVec 32) : BitVec 32 := x ^^^ y ^^^ z

/-- ASL `SHAmajority{32}(x, y, z)` (`shared/functions/crypto/SHAmajority`). -/
def shaMajority32 (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)

/-- ASL `SHAmajority{64}(x, y, z)` (`shared/functions/crypto/SHAmajority`). -/
def shaMajority64 (x y z : BitVec 64) : BitVec 64 := (x &&& y) ||| ((x ||| y) &&& z)

/-- ASL `SHA256hashSIGMA0(x)` (`shared/functions/crypto/SHA256hashSIGMA0`). -/
def sha256Sigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- ASL `SHA256hashSIGMA1(x)` (`shared/functions/crypto/SHA256hashSIGMA1`). -/
def sha256Sigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- ASL `SHA256hash(x_in, y_in, w, part1)` (`shared/functions/crypto/SHA256hash`). -/
def sha256Hash (xIn yIn w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let (xOut, yOut) := (List.range 4).foldl (fun (xy : BitVec 128 × BitVec 128) e =>
    let x := xy.1
    let y := xy.2
    let x0 := x.extractLsb' 0 32
    let x1 := x.extractLsb' 32 32
    let x2 := x.extractLsb' 64 32
    let x3 := x.extractLsb' 96 32
    let y0 := y.extractLsb' 0 32
    let y1 := y.extractLsb' 32 32
    let y2 := y.extractLsb' 64 32
    let y3 := y.extractLsb' 96 32
    let chs := shaChoose32 y0 y1 y2
    let maj := shaMajority32 x0 x1 x2
    let t := y3 + sha256Sigma1 y0 + chs + w.extractLsb' (e * 32) 32
    let x3' := t + x3
    let y3' := t + sha256Sigma0 x0 + maj
    (x2 ++ x1 ++ x0 ++ y3', y2 ++ y1 ++ y0 ++ x3')) (xIn, yIn)
  if part1 then xOut else yOut

/-- Evaluate `FEAT_SHA1`/`FEAT_SHA256` 2-register SHA instructions (`cryptoSha2Reg`,
    ASL `A64.simd_dp.cryptosha2`):
    - `opcode = 00000` (`0#5`): `SHA1H Sd, Sn`
    - `opcode = 00001` (`1#5`): `SHA1SU1 Vd.4S, Vn.4S`
    - `opcode = 00010` (`2#5`): `SHA256SU0 Vd.4S, Vn.4S` -/
def evalCryptoSha2Reg (opcode : BitVec 5) (vd vn : BitVec 128) : Except String (BitVec 128) :=
  match opcode with
  | 0#5 =>
    -- `SHA1H Sd, Sn`: `V{32}(d) = ROL(V{32}(n), 30)`
    pure (((vn.truncate 32).rotateLeft 30).zeroExtend 128)
  | 1#5 =>
    -- `SHA1SU1 Vd.4S, Vn.4S`
    let t : BitVec 128 := vd ^^^ (vn >>> 32)
    let t0 := (t.extractLsb' 0 32).rotateLeft 1
    let t1 := (t.extractLsb' 32 32).rotateLeft 1
    let t2 := (t.extractLsb' 64 32).rotateLeft 1
    let t3 := (t.extractLsb' 96 32).rotateLeft 1 ^^^ (t0.rotateLeft 1)
    pure (t3 ++ t2 ++ t1 ++ t0)
  | 2#5 =>
    -- `SHA256SU0 Vd.4S, Vn.4S`
    let t : BitVec 128 := (vn.extractLsb' 0 32) ++ (vd.extractLsb' 32 96)
    let res := (List.range 4).foldl (fun acc e =>
      let elt := t.extractLsb' (e * 32) 32
      let s0 := elt.rotateRight 7 ^^^ elt.rotateRight 18 ^^^ (elt >>> 3)
      let out := s0 + vd.extractLsb' (e * 32) 32
      acc ||| (out.zeroExtend 128 <<< (e * 32))) 0#128
    pure res
  | _ =>
    throw (toString "unsupported AdvSIMD: cryptoSha2Reg (opcode=0x" ++ toString (String.ofList (Nat.toDigits 16 opcode.toNat)) ++ toString ") — architecturally UNDEFINED" : String)

/-- Evaluate `FEAT_SHA1`/`FEAT_SHA256` 3-register SHA instructions (`cryptoSha3Reg`,
    ASL `A64.simd_dp.cryptosha3`):
    - `opcode = 000` (`0#3`): `SHA1C Qd, Sn, Vm.4S`
    - `opcode = 001` (`1#3`): `SHA1P Qd, Sn, Vm.4S`
    - `opcode = 010` (`2#3`): `SHA1M Qd, Sn, Vm.4S`
    - `opcode = 011` (`3#3`): `SHA1SU0 Vd.4S, Vn.4S, Vm.4S`
    - `opcode = 100` (`4#3`): `SHA256H Qd, Qn, Vm.4S`
    - `opcode = 101` (`5#3`): `SHA256H2 Qd, Qn, Vm.4S`
    - `opcode = 110` (`6#3`): `SHA256SU1 Vd.4S, Vn.4S, Vm.4S` -/
def evalCryptoSha3Reg (opcode : BitVec 3) (vd vn vm : BitVec 128) : Except String (BitVec 128) :=
  if opcode == 0#3 || opcode == 1#3 || opcode == 2#3 then
    -- `SHA1C`, `SHA1P`, `SHA1M`
    let (xOut, _) := (List.range 4).foldl (fun (xy : BitVec 128 × BitVec 32) e =>
      let x := xy.1
      let y := xy.2
      let x0 := x.extractLsb' 0 32
      let x1 := x.extractLsb' 32 32
      let x2 := x.extractLsb' 64 32
      let x3 := x.extractLsb' 96 32
      let t :=
        if opcode == 0#3 then shaChoose32 x1 x2 x3
        else if opcode == 1#3 then shaParity32 x1 x2 x3
        else shaMajority32 x1 x2 x3
      let y' := y + x0.rotateLeft 5 + t + vm.extractLsb' (e * 32) 32
      let x1' := x1.rotateLeft 30
      (x2 ++ x1' ++ x0 ++ y', x3)) (vd, vn.truncate 32)
    pure xOut
  else if opcode == 3#3 then
    -- `SHA1SU0 Vd.4S, Vn.4S, Vm.4S`: `(Vn<63:0> : Vd<127:64>) EOR Vd EOR Vm`
    let res : BitVec 128 := ((vn.extractLsb' 0 64) ++ (vd.extractLsb' 64 64)) ^^^ vd ^^^ vm
    pure res
  else if opcode == 4#3 then
    -- `SHA256H Qd, Qn, Vm.4S`
    pure (sha256Hash vd vn vm true)
  else if opcode == 5#3 then
    -- `SHA256H2 Qd, Qn, Vm.4S`
    pure (sha256Hash vn vd vm false)
  else if opcode == 6#3 then
    -- `SHA256SU1 Vd.4S, Vn.4S, Vm.4S`
    let t0 : BitVec 128 := (vm.extractLsb' 0 32) ++ (vn.extractLsb' 32 96)
    let sigma1 (elt : BitVec 32) : BitVec 32 :=
      elt.rotateRight 17 ^^^ elt.rotateRight 19 ^^^ (elt >>> 10)
    let r0 := sigma1 (vm.extractLsb' 64 32) + vd.extractLsb' 0 32 + t0.extractLsb' 0 32
    let r1 := sigma1 (vm.extractLsb' 96 32) + vd.extractLsb' 32 32 + t0.extractLsb' 32 32
    let r2 := sigma1 r0 + vd.extractLsb' 64 32 + t0.extractLsb' 64 32
    let r3 := sigma1 r1 + vd.extractLsb' 96 32 + t0.extractLsb' 96 32
    pure (r3 ++ r2 ++ r1 ++ r0)
  else
    throw (toString "unsupported AdvSIMD: cryptoSha3Reg (opcode=0x" ++ toString (String.ofList (Nat.toDigits 16 opcode.toNat)) ++ toString ") — architecturally UNDEFINED" : String)

/-- Evaluate `SHA512SU0 Vd.2D, Vn.2D` (`cryptoSha512Reg2`,
    ASL `A64.simd_dp.cryptosha512_2.SHA512SU0_VV2_cryptosha512_2`). -/
def evalCryptoSha512Reg2 (vd vn : BitVec 128) : BitVec 128 :=
  let w0 := vd.extractLsb' 0 64
  let w1 := vd.extractLsb' 64 64
  let x0 := vn.extractLsb' 0 64
  let sig0_lo := w1.rotateRight 1 ^^^ w1.rotateRight 8 ^^^ (w1 >>> 7)
  let sig0_hi := x0.rotateRight 1 ^^^ x0.rotateRight 8 ^^^ (x0 >>> 7)
  (w1 + sig0_hi) ++ (w0 + sig0_lo)

/-- Evaluate `FEAT_SHA512`/`FEAT_SHA3` 3-register instructions (`cryptoSha512Reg3`,
    ASL `A64.simd_dp.cryptosha512_3`):
    - `opcode = 00` (`0#2`): `SHA512H Qd, Qn, Vm.2D`
    - `opcode = 01` (`1#2`): `SHA512H2 Qd, Qn, Vm.2D`
    - `opcode = 10` (`2#2`): `SHA512SU1 Vd.2D, Vn.2D, Vm.2D`
    - `opcode = 11` (`3#2`): `RAX1 Vd.2D, Vn.2D, Vm.2D` -/
def evalCryptoSha512Reg3 (opcode : BitVec 2) (vd vn vm : BitVec 128) : BitVec 128 :=
  let w0 := vd.extractLsb' 0 64
  let w1 := vd.extractLsb' 64 64
  let x0 := vn.extractLsb' 0 64
  let x1 := vn.extractLsb' 64 64
  let y0 := vm.extractLsb' 0 64
  let y1 := vm.extractLsb' 64 64
  if opcode == 0#2 then
    -- `SHA512H Qd, Qn, Vm.2D` (`x = V(n)`, `y = V(m)`, `w = V(d)`)
    let mSigma1 (v : BitVec 64) : BitVec 64 :=
      v.rotateRight 14 ^^^ v.rotateRight 18 ^^^ v.rotateRight 41
    let vtmpHi := ((y1 &&& x0) ^^^ (~~~y1 &&& x1)) + mSigma1 y1 + w1
    let tmp := vtmpHi + y0
    let vtmpLo := ((tmp &&& y1) ^^^ (~~~tmp &&& x0)) + mSigma1 tmp + w0
    vtmpHi ++ vtmpLo
  else if opcode == 1#2 then
    -- `SHA512H2 Qd, Qn, Vm.2D` (`x = V(n)`, `y = V(m)`, `w = V(d)`)
    let nSigma0 (v : BitVec 64) : BitVec 64 :=
      v.rotateRight 28 ^^^ v.rotateRight 34 ^^^ v.rotateRight 39
    let vtmpHi := shaMajority64 x0 y1 y0 + nSigma0 y0 + w1
    let vtmpLo := shaMajority64 vtmpHi y0 y1 + nSigma0 vtmpHi + w0
    vtmpHi ++ vtmpLo
  else if opcode == 2#2 then
    -- `SHA512SU1 Vd.2D, Vn.2D, Vm.2D` (`x = V(n)`, `y = V(m)`, `w = V(d)`)
    let sig1 (v : BitVec 64) : BitVec 64 :=
      v.rotateRight 19 ^^^ v.rotateRight 61 ^^^ (v >>> 6)
    (w1 + sig1 x1 + y1) ++ (w0 + sig1 x0 + y0)
  else
    -- `RAX1 Vd.2D, Vn.2D, Vm.2D`
    (x1 ^^^ y1.rotateLeft 1) ++ (x0 ^^^ y0.rotateLeft 1)

/-- Evaluate `EOR3` (`isBcax = false`) / `BCAX` (`isBcax = true`) (`cryptoSha3FourReg`,
    ASL `A64.simd_dp.crypto4`). -/
def evalCryptoSha3FourReg (isBcax : Bool) (vn vm va : BitVec 128) : BitVec 128 :=
  if isBcax then vn ^^^ (vm &&& ~~~va) else vn ^^^ vm ^^^ va

/-- Evaluate `XAR Vd.2D, Vn.2D, Vm.2D, #imm6` (`cryptoXar`,
    ASL `A64.simd_dp.crypto3_imm6.XAR_VVV2_crypto3_imm6`). -/
def evalCryptoXar (imm6 : BitVec 6) (vn vm : BitVec 128) : BitVec 128 :=
  let sh := imm6.toNat
  let tmp := vn ^^^ vm
  ((tmp.extractLsb' 64 64).rotateRight sh) ++ ((tmp.extractLsb' 0 64).rotateRight sh)

/-- Whole-register transfer size for a vector arrangement: `Q128` if `q`, else `D64`. -/
def SimdMemSize.ofQ (q : Bool) : SimdMemSize := if q then .Q128 else .D64

/-- `ST1` (multiple structures): store `k` registers `vt, vt+1, …` (mod 32, read via `rd`) of
    `sz` (`D64` or `Q128`) bytes each, contiguously from `ea`. -/
def simdStoreRegs (sz : SimdMemSize) (rd : BitVec 5 → BitVec 128) :
    Nat → BitVec 5 → BitVec 64 → Memory → Memory
  | 0, _, _, m => m
  | k + 1, vt, ea, m =>
    simdStoreRegs sz rd k (vt + 1#5) (ea + BitVec.ofNat 64 sz.bytes) (m.writeSimdSized sz ea (rd vt))

/-- `LD1` (multiple structures): load `k` registers `vt, vt+1, …` (mod 32) of `sz` (`D64`
    zero-extended, or `Q128`) bytes each, contiguously from `ea` in memory `m`. -/
def simdLoadRegs (sz : SimdMemSize) (m : Memory) : Nat → BitVec 5 → BitVec 64 → State → State
  | 0, _, _, s => s
  | k + 1, vt, ea, s =>
    simdLoadRegs sz m k (vt + 1#5) (ea + BitVec.ofNat 64 sz.bytes) (s.writeVReg128 vt (m.readSimdSized sz ea))

/-- Apply a pure SIMD register result (`Except String (BitVec 128)`) to `rd` and advance `PC`,
    or transition to `.Exception msg` on an unsupported/UNDEFINED encoding. -/
@[simp] def applySimdResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) : State :=
  match r with
  | .ok res => (s.writeVReg128 rd res).advancePC
  | .error msg => { s with status := .Exception msg }

/-- Apply a pure SIMD register result (`Except String (BitVec 128)`) and optional `FPSR.QC`
    saturation flags to `rd`/`s.fpsr` and advance `PC`, or transition to `.Exception msg` on an
    unsupported/UNDEFINED encoding. -/
@[simp] def applySimdSatResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) : State :=
  match r, satFlags with
  | .ok res, none => (s.writeVReg128 rd res).advancePC
  | .ok res, some flags => ((s.writeVReg128 rd res).orFpsr flags).advancePC
  | .error msg, _ => { s with status := .Exception msg }

/-- Unsigned integer value (`UInt(x<esize-1:0>)`) of an `esize`-bit SIMD lane (`esize ≤ 64`). -/
def simdLaneUInt (esize : Nat) (x : BitVec 128) : Int :=
  let mask : BitVec 128 := (1#128 <<< esize) - 1#128
  Int.ofNat (x &&& mask).toNat

/-- Two's-complement signed integer value (`SInt(x<esize-1:0>)`) of an `esize`-bit SIMD lane (`esize ≤ 64`). -/
def simdLaneSInt (esize : Nat) (x : BitVec 128) : Int :=
  let u := simdLaneUInt esize x
  if x.getLsbD (esize - 1) then u - Int.ofNat (1 <<< esize) else u

/-- Truncate mathematical integer `v` to its low `esize` two's-complement bits (`v<esize-1:0>`). -/
def intToSimdLane (esize : Nat) (v : Int) : BitVec 128 :=
  (BitVec.ofInt 128 v) &&& ((1#128 <<< esize) - 1#128)

/-- Insert the low `esize` bits of `elem` into lane `idx` of 128-bit vector `v`,
    preserving all other bits of `v`. -/
def setSimdLane (v : BitVec 128) (esize : Nat) (idx : Nat) (elem : BitVec 128) : BitVec 128 :=
  let mask : BitVec 128 := ((1#128 <<< esize) - 1#128) <<< (idx * esize)
  (v &&& ~~~mask) ||| ((elem <<< (idx * esize)) &&& mask)

/-- Compute the lane index for AdvSIMD `LD1`/`ST1` single-structure lane transfers. -/
def simdLdSt1SingleLaneIdx (q : Bool) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) : Nat :=
  let qNat := if q then 1 else 0
  let sNat := if sBit then 1 else 0
  let opcHi := opcode.extractLsb' 1 2
  if opcHi == 0#2 then (qNat <<< 3) ||| (sNat <<< 2) ||| size.toNat
  else if opcHi == 1#2 then (qNat <<< 2) ||| (sNat <<< 1) ||| (size.extractLsb' 1 1).toNat
  else if size.extractLsb' 0 1 == 0#1 then (qNat <<< 1) ||| sNat
  else qNat

/-- Build the `k`-th (`k = (r - vt).toNat`) contiguous `datasize`-bit memory chunk for
    AdvSIMD `ST2`/`ST3`/`ST4` multiple-structure stores (`selem ∈ {2, 3, 4}`). -/
def simdInterleaveChunk (q : Bool) (size : BitVec 2) (selem : Nat) (vt : BitVec 5)
    (rd : BitVec 5 → BitVec 128) (r : BitVec 5) : BitVec 128 :=
  let k := (r - vt).toNat
  let datasize := if q then 128 else 64
  let esize := 8 <<< size.toNat
  let elements := datasize / esize
  (List.range elements).foldl (fun acc j =>
    let idx := k * elements + j
    let e := idx / selem
    let sIdx := idx % selem
    let regVal := rd (vt + BitVec.ofNat 5 sIdx)
    let lane := getSimdLane regVal esize e
    acc ||| (lane <<< (j * esize))) 0#128

/-- Extract the `sIdx`-th destination register (`vt + sIdx`, zero-extended to 128 bits when
    `q = false`) from the `selem` contiguous `datasize`-bit memory chunks `c0..c3` loaded by
    AdvSIMD `LD2`/`LD3`/`LD4` multiple-structure loads (`selem ∈ {2, 3, 4}`). -/
def simdDeinterleaveReg (q : Bool) (size : BitVec 2) (selem sIdx : Nat)
    (c0 c1 c2 c3 : BitVec 128) : BitVec 128 :=
  let datasize := if q then 128 else 64
  let esize := 8 <<< size.toNat
  let elements := datasize / esize
  (List.range elements).foldl (fun acc e =>
    let idx := e * selem + sIdx
    let k := idx / elements
    let j := idx % elements
    let chunk := match k with | 0 => c0 | 1 => c1 | 2 => c2 | _ => c3
    let lane := getSimdLane chunk esize j
    acc ||| (lane <<< (e * esize))) 0#128

/-- Evaluate AdvSIMD scalar `DUP <V><d>, <Vn>.<T>[<index>]` (`A64.simd_dp.asisdone.DUP_asisdone_only`). -/
def evalSimdDupScalar (imm5 : BitVec 5) (vn : BitVec 128) : BitVec 128 :=
  if imm5.getLsbD 0 then
    getSimdLane vn 8 (imm5.toNat >>> 1)
  else if imm5.getLsbD 1 then
    getSimdLane vn 16 (imm5.toNat >>> 2)
  else if imm5.getLsbD 2 then
    getSimdLane vn 32 (imm5.toNat >>> 3)
  else
    getSimdLane vn 64 (imm5.toNat >>> 4)

/-- Evaluate AdvSIMD three-different instructions (`A64.simd_dp.asimddiff.*`). -/
def evalSimdThreeDiff (q u : Bool) (size : BitVec 2) (opcode : BitVec 4)
    (vd vn vm : BitVec 128) : BitVec 128 :=
  let esize := 8 <<< size.toNat
  let dstEsize := 2 * esize
  let numLanes := 64 / esize
  if opcode == 4#4 || opcode == 6#4 then
    let isSub := opcode == 6#4
    let roundConst : Int := if u then Int.ofNat (1 <<< (esize - 1)) else 0
    let dstMask : BitVec 64 := (1#64 <<< esize) - 1#64
    let res64 : BitVec 64 :=
      (List.range numLanes).foldl (fun acc e =>
        let e1 := simdLaneUInt dstEsize (getSimdLane vn dstEsize e)
        let e2 := simdLaneUInt dstEsize (getSimdLane vm dstEsize e)
        let sum := (if isSub then e1 - e2 else e1 + e2) + roundConst
        let narrow := (((intToSimdLane dstEsize sum) >>> esize).truncate 64) &&& dstMask
        acc ||| (narrow <<< (e * esize))) 0#64
    if q then res64 ++ vd.truncate 64 else res64.zeroExtend 128
  else
    let nHalf : BitVec 128 := if q then vn >>> 64 else vn
    let mHalf : BitVec 128 := if q then vm >>> 64 else vm
    let narrowVal (v : BitVec 128) (e : Nat) : Int :=
      let lane := getSimdLane v esize e
      if u then simdLaneUInt esize lane else simdLaneSInt esize lane
    let wideVal (v : BitVec 128) (e : Nat) : Int :=
      let lane := getSimdLane v dstEsize e
      if u then simdLaneUInt dstEsize lane else simdLaneSInt dstEsize lane
    (List.range numLanes).foldl (fun acc e =>
      let n := narrowVal nHalf e
      let m := narrowVal mHalf e
      let val : Int :=
        match opcode with
        | 0#4  => n + m
        | 1#4  => wideVal vn e + m
        | 2#4  => n - m
        | 3#4  => wideVal vn e - m
        | 5#4  => wideVal vd e + Int.ofNat (n - m).natAbs
        | 7#4  => Int.ofNat (n - m).natAbs
        | 8#4  => wideVal vd e + n * m
        | 10#4 => wideVal vd e - n * m
        | _    => n * m
      let wide := intToSimdLane dstEsize val
      acc ||| (wide <<< (e * dstEsize))) 0#128

/-- ASL `RShr(value, shift, round)`: arithmetic right shift of mathematical integer `value`
    by `shift > 0`, with optional rounding (`+ 2^(shift - 1)` before floor-dividing by `2^shift`). -/
def aslRShr (value : Int) (shift : Nat) (round : Bool) : Int :=
  if shift == 0 then value
  else
    let v := if round then value + Int.ofNat (1 <<< (shift - 1)) else value
    v / Int.ofNat (1 <<< shift)

/-- ASL `SignedSatQ{esize}(i)` value component (`[-2^(esize-1), 2^(esize-1) - 1]`). -/
def aslSignedSat (esize : Nat) (i : Int) : BitVec 128 :=
  let half : Int := Int.ofNat (1 <<< (esize - 1))
  let maxVal : Int := half - 1
  let minVal : Int := -half
  let clamped : Int := if i > maxVal then maxVal else if i < minVal then minVal else i
  intToSimdLane esize clamped

/-- ASL `SignedSatQ{esize}(i)` saturation predicate (`i ∉ [-2^(esize-1), 2^(esize-1) - 1]`). -/
def aslSignedSatFlag (esize : Nat) (i : Int) : Bool :=
  let half : Int := Int.ofNat (1 <<< (esize - 1))
  i > half - 1 || i < -half

/-- ASL `UnsignedSatQ{esize}(i)` value component (`[0, 2^esize - 1]`). -/
def aslUnsignedSat (esize : Nat) (i : Int) : BitVec 128 :=
  let maxVal : Int := Int.ofNat (1 <<< esize) - 1
  let clamped : Int := if i > maxVal then maxVal else if i < 0 then 0 else i
  BitVec.ofNat 128 clamped.toNat

/-- ASL `UnsignedSatQ{esize}(i)` saturation predicate (`i ∉ [0, 2^esize - 1]`). -/
def aslUnsignedSatFlag (esize : Nat) (i : Int) : Bool :=
  i > Int.ofNat (1 <<< esize) - 1 || i < 0

/-- ASL `SatQ{esize}(i, unsigned)`. -/
def aslSat (esize : Nat) (i : Int) (unsigned : Bool) : BitVec 128 :=
  if unsigned then aslUnsignedSat esize i else aslSignedSat esize i

/-- ASL `SatQ{esize}(i, unsigned)` saturation predicate. -/
def aslSatFlag (esize : Nat) (i : Int) (unsigned : Bool) : Bool :=
  if unsigned then aslUnsignedSatFlag esize i else aslSignedSatFlag esize i

/-- Check whether any `esize`-bit lane of `vn` (`(if q then 128 else 64) / esize` lanes) satisfies `f`. -/
def anySimdLane (q : Bool) (esize : Nat) (vn : BitVec 128) (f : BitVec 128 → Bool) : Bool :=
  let numLanes := (if q then 128 else 64) / esize
  (List.range numLanes).any (fun i => f (getSimdLane vn esize i))

/-- Check whether any pair of `esize`-bit lanes from `vn` and `vm` satisfies `f`. -/
def anyZipSimdLane (q : Bool) (esize : Nat) (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → Bool) : Bool :=
  let numLanes := (if q then 128 else 64) / esize
  (List.range numLanes).any (fun i => f (getSimdLane vn esize i) (getSimdLane vm esize i))

/-- Check whether any of the `64 / esize` wide lanes of width `2 * esize` in `vn` satisfies `f`. -/
def anyNarrowSimdLane (esize : Nat) (vn : BitVec 128) (f : BitVec 128 → Bool) : Bool :=
  let srcEsize := 2 * esize
  let numLanes := 64 / esize
  (List.range numLanes).any (fun e => f (getSimdLane vn srcEsize e))

/-- Narrow `64 / esize` wide lanes of width `2 * esize` from 128-bit `vn` into a 64-bit result,
    writing `Vpart{64}(d, Q)` (`Q = false` zero-extends upper 64 bits; `Q = true` writes upper
    64 bits `[127:64]` and preserves `vd[63:0]`). -/
def narrowSimdLanes (q : Bool) (esize : Nat) (vd vn : BitVec 128)
    (f : BitVec 128 → BitVec 128) : BitVec 128 :=
  let srcEsize := 2 * esize
  let numLanes := 64 / esize
  let dstMask : BitVec 64 := (1#64 <<< esize) - 1#64
  let res64 : BitVec 64 :=
    (List.range numLanes).foldl (fun acc e =>
      let wide := getSimdLane vn srcEsize e
      let narrow := ((f wide).truncate 64) &&& dstMask
      acc ||| (narrow <<< (e * esize))) 0#64
  if q then res64 ++ vd.truncate 64 else res64.zeroExtend 128

/-- ASL `AdvSIMDExpandImm(op, cmode, imm8)`: expand an 8-bit modified immediate to 64 bits. -/
def advSimdExpandImm (op : Bool) (cmode : BitVec 4) (imm8 : BitVec 8) : BitVec 64 :=
  let c31 := cmode.extractLsb' 1 3
  let c0 := cmode.getLsbD 0
  match c31 with
  | 0b000#3 =>
    let w32 : BitVec 32 := imm8.zeroExtend 32
    w32 ++ w32
  | 0b001#3 =>
    let w32 : BitVec 32 := (imm8.zeroExtend 32) <<< 8
    w32 ++ w32
  | 0b010#3 =>
    let w32 : BitVec 32 := (imm8.zeroExtend 32) <<< 16
    w32 ++ w32
  | 0b011#3 =>
    let w32 : BitVec 32 := (imm8.zeroExtend 32) <<< 24
    w32 ++ w32
  | 0b100#3 =>
    let h16 : BitVec 16 := imm8.zeroExtend 16
    h16 ++ h16 ++ h16 ++ h16
  | 0b101#3 =>
    let h16 : BitVec 16 := (imm8.zeroExtend 16) <<< 8
    h16 ++ h16 ++ h16 ++ h16
  | 0b110#3 =>
    let w32 : BitVec 32 :=
      if !c0 then ((imm8.zeroExtend 32) <<< 8) ||| 0xff#32
      else ((imm8.zeroExtend 32) <<< 16) ||| 0xffff#32
    w32 ++ w32
  | _ =>
    if !c0 && !op then
      imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8
    else if !c0 && op then
      let b (i : Nat) : BitVec 8 := if imm8.getLsbD i then 0xff#8 else 0x00#8
      b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0
    else if c0 && !op then
      let w32 := vfpExpandImm32 imm8
      w32 ++ w32
    else
      vfpExpandImm64 imm8

/-- ASL `CountLeadingZeroBits` on an `esize`-bit SIMD lane. -/
def simdClz (esize : Nat) (lane : BitVec 128) : Nat :=
  ((List.range esize).foldl (fun (count, done) j =>
    let bitIdx := esize - 1 - j
    if done then (count, true)
    else if lane.getLsbD bitIdx then (count, true)
    else (count + 1, false)) (0, false)).1

/-- ASL `CountLeadingSignBits` on an `esize`-bit SIMD lane. -/
def simdCls (esize : Nat) (lane : BitVec 128) : Nat :=
  let sign := lane.getLsbD (esize - 1)
  ((List.range (esize - 1)).foldl (fun (count, done) k =>
    let bitIdx := esize - 2 - k
    if done then (count, true)
    else if lane.getLsbD bitIdx != sign then (count, true)
    else (count + 1, false)) (0, false)).1

/-- Evaluate AdvSIMD modified-immediate encodings (`simdImmShift` with `immh == 0`) beyond basic
    `MOVI`: `MOVI` MSL (`cmode = 110x`), `MVNI` (`LSL` 16/32-bit and `MSL` 32-bit), `ORR`/`BIC`
    immediate (`cmode = 0xx1 / 10x1`), and vector `FMOV #imm8` (`cmode = 1111, o2 = 0`). -/
def evalSimdModImmExt (q op : Bool) (immb : BitVec 3) (opc : BitVec 5) (rn : BitVec 5)
    (vd : BitVec 128) : Except String (BitVec 128) :=
  let o2 := opc.getLsbD 0
  let cmode := opc.extractLsb' 1 4
  if o2 then
    if !op && cmode == 0b1111#4 then
      .error (toString "unsupported AdvSIMD: simdImmShift vector-FP FMOV FP16 (q=" ++ toString (if q then 1 else 0) ++ toString " op=0 cmode=1111 o2=1) — vector FP not modeled in Arm64/Trusted/ISA" : String)
    else
      .error (toString "unsupported AdvSIMD: simdImmShift modified-immediate (q=" ++ toString (if q then 1 else 0) ++ toString " op=" ++ toString (if op then 1 else 0) ++ toString " cmode=" ++ toString (cmode.toNat) ++ toString " o2=1) — architecturally UNDEFINED" : String)
  else
    let imm8 : BitVec 8 := immb ++ rn
    let imm64 := advSimdExpandImm op cmode imm8
    let packQ (d64 : BitVec 64) : BitVec 128 := if q then d64 ++ d64 else d64.zeroExtend 128
    let dst := if q then vd else (vd.truncate 64).zeroExtend 128
    if !op && ((cmode &&& 0b1001#4) == 0b0000#4 || (cmode &&& 0b1101#4) == 0b1000#4 ||
        (cmode &&& 0b1110#4) == 0b1100#4 || cmode == 0b1110#4 || cmode == 0b1111#4) then
      -- MOVI (LSL, MSL, 8-bit) and FMOV (vector 2S/4S)
      .ok (packQ imm64)
    else if !op && ((cmode &&& 0b1001#4) == 0b0001#4 || (cmode &&& 0b1101#4) == 0b1001#4) then
      -- ORR (vector, immediate) 16-bit and 32-bit
      .ok (dst ||| packQ imm64)
    else if op && ((cmode &&& 0b1001#4) == 0b0000#4 || (cmode &&& 0b1101#4) == 0b1000#4 ||
        (cmode &&& 0b1110#4) == 0b1100#4) then
      -- MVNI (LSL 16/32-bit and MSL 32-bit)
      .ok (packQ (~~~imm64))
    else if op && ((cmode &&& 0b1001#4) == 0b0001#4 || (cmode &&& 0b1101#4) == 0b1001#4) then
      -- BIC (vector, immediate) 16-bit and 32-bit
      .ok (dst &&& packQ (~~~imm64))
    else if op && cmode == 0b1110#4 then
      -- MOVI Dd / Vd.2D, #imm
      .ok (packQ imm64)
    else if op && cmode == 0b1111#4 then
      if q then
        -- FMOV Vd.2D, #imm8
        .ok (packQ imm64)
      else
        .error "unsupported AdvSIMD: simdImmShift modified-immediate (q=0 op=1 cmode=1111 o2=0) — architecturally UNDEFINED"
    else
      .error (toString "unsupported AdvSIMD: simdImmShift modified-immediate (q=" ++ toString (if q then 1 else 0) ++ toString " op=" ++ toString (if op then 1 else 0) ++ toString " cmode=" ++ toString (cmode.toNat) ++ toString " o2=0) — architecturally UNDEFINED" : String)

/-- Evaluate AdvSIMD shift-by-immediate encodings (`simdImmShift` with `immh != 0`):
    `SSHR`/`USHR`, `SSRA`/`USRA`, `SRSHR`/`URSHR`, `SRSRA`/`URSRA`, `SRI`, `SHL`, `SLI`,
    `SQSHLU`, `SQSHL`/`UQSHL` (imm), narrowing `SHRN`/`RSHRN`/`SQSHRUN`/`SQRSHRUN`/`SQSHRN`/
    `SQRSHRN`/`UQSHRN`/`UQRSHRN` (+2), and widening `SSHLL`/`USHLL` (+2). -/
def evalSimdImmShiftNonZeroExt (q op : Bool) (immh : BitVec 4) (immb : BitVec 3) (opc : BitVec 5)
    (vd vn : BitVec 128) : Except String (BitVec 128) :=
  let immhb := (immh ++ immb).toNat
  let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
  let shiftLeftAmt := immhb - esize
  let shiftRightAmt := 2 * esize - immhb
  if (opc == 0b00000#5 || opc == 0b00010#5 || opc == 0b00100#5 || opc == 0b00110#5) &&
      !(immh.getLsbD 3 && !q) then
    -- SSHR/USHR (`00000`), SSRA/USRA (`00010`), SRSHR/URSHR (`00100`), SRSRA/URSRA (`00110`)
    let round := opc == 0b00100#5 || opc == 0b00110#5
    let accum := opc == 0b00010#5 || opc == 0b00110#5
    let res := zipSimdLanes q esize vn vd (fun lane acc =>
      let val := if op then simdLaneUInt esize lane else simdLaneSInt esize lane
      let sh := intToSimdLane esize (aslRShr val shiftRightAmt round)
      if accum then acc + sh else sh)
    .ok res
  else if op && opc == 0b01100#5 && !(immh.getLsbD 3 && !q) then
    -- SQSHLU (immediate)
    let res := mapSimdLanes q esize vn (fun lane =>
      aslUnsignedSat esize ((simdLaneSInt esize lane) * Int.ofNat (1 <<< shiftLeftAmt)))
    .ok res
  else if opc == 0b01110#5 && !(immh.getLsbD 3 && !q) then
    -- SQSHL (`op = 0`) / UQSHL (`op = 1`) (immediate)
    let res := mapSimdLanes q esize vn (fun lane =>
      let val := if op then simdLaneUInt esize lane else simdLaneSInt esize lane
      aslSat esize (val * Int.ofNat (1 <<< shiftLeftAmt)) op)
    .ok res
  else if (opc == 0b10000#5 || opc == 0b10001#5) && !immh.getLsbD 3 then
    -- SHRN/SHRN2 (`op = 0, 10000`), RSHRN/RSHRN2 (`op = 0, 10001`),
    -- SQSHRUN/SQSHRUN2 (`op = 1, 10000`), SQRSHRUN/SQRSHRUN2 (`op = 1, 10001`)
    let round := opc.getLsbD 0
    let res := narrowSimdLanes q esize vd vn (fun wide =>
      if !op then
        intToSimdLane esize (aslRShr (simdLaneUInt (2 * esize) wide) shiftRightAmt round)
      else
        aslUnsignedSat esize (aslRShr (simdLaneSInt (2 * esize) wide) shiftRightAmt round))
    .ok res
  else if (opc == 0b10010#5 || opc == 0b10011#5) && !immh.getLsbD 3 then
    -- SQSHRN/SQSHRN2 (`op = 0, 10010`), SQRSHRN/SQRSHRN2 (`op = 0, 10011`),
    -- UQSHRN/UQSHRN2 (`op = 1, 10010`), UQRSHRN/UQRSHRN2 (`op = 1, 10011`)
    let round := opc.getLsbD 0
    let res := narrowSimdLanes q esize vd vn (fun wide =>
      let val := if op then simdLaneUInt (2 * esize) wide else simdLaneSInt (2 * esize) wide
      aslSat esize (aslRShr val shiftRightAmt round) op)
    .ok res
  else if !op && opc == 0b10100#5 && !immh.getLsbD 3 then
    -- SSHLL / SSHLL2 (`SXTL` / `SXTL2` when `shiftLeftAmt == 0`)
    let half : BitVec 128 := if q then vn >>> 64 else (vn.truncate 64).zeroExtend 128
    let dstEsize := 2 * esize
    let numLanes := 64 / esize
    let res : BitVec 128 :=
      (List.range numLanes).foldl (fun acc e =>
        let lane := getSimdLane half esize e
        let sVal := (simdLaneSInt esize lane) * Int.ofNat (1 <<< shiftLeftAmt)
        let wide := intToSimdLane dstEsize sVal
        acc ||| (wide <<< (e * dstEsize))) 0#128
    .ok res
  else if (opc == 0b11100#5 || opc == 0b11111#5) && (immh.extractLsb' 2 2 != 0#2) &&
      !(immh.getLsbD 3 && !q) then
    let mnem :=
      if opc == 0b11100#5 then (if op then "UCVTF" else "SCVTF")
      else (if op then "FCVTZU" else "FCVTZS")
    .error (toString "unsupported AdvSIMD: simdImmShift vector-FP fixed-point " ++ toString (mnem) ++ toString " (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if op then 1 else 0) ++ toString " immh=" ++ toString (immh.toNat) ++ toString " immb=" ++ toString (immb.toNat) ++ toString " opcode=" ++ toString (opc.toNat) ++ toString ") — vector FP not modeled in Arm64/Trusted/ISA" : String)
  else
    .error (toString "unsupported AdvSIMD: simdImmShift (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if op then 1 else 0) ++ toString " immh=" ++ toString (immh.toNat) ++ toString " immb=" ++ toString (immb.toNat) ++ toString " opcode=" ++ toString (opc.toNat) ++ toString ") — architecturally UNDEFINED" : String)

/-- Optional `FPSR.QC` saturation flag for `evalSimdImmShiftNonZeroExt` (`some` only for saturating opcodes). -/
def evalSimdImmShiftNonZeroExtSatFlags (q op : Bool) (immh : BitVec 4) (immb : BitVec 3)
    (opc : BitVec 5) (vn : BitVec 128) : Option (BitVec 32) :=
  let immhb := (immh ++ immb).toNat
  let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
  let shiftLeftAmt := immhb - esize
  let shiftRightAmt := 2 * esize - immhb
  if op && opc == 0b01100#5 && !(immh.getLsbD 3 && !q) then
    let sat := anySimdLane q esize vn (fun lane =>
      aslUnsignedSatFlag esize ((simdLaneSInt esize lane) * Int.ofNat (1 <<< shiftLeftAmt)))
    some (if sat then fpsrQC else 0#32)
  else if opc == 0b01110#5 && !(immh.getLsbD 3 && !q) then
    let sat := anySimdLane q esize vn (fun lane =>
      let val := if op then simdLaneUInt esize lane else simdLaneSInt esize lane
      aslSatFlag esize (val * Int.ofNat (1 <<< shiftLeftAmt)) op)
    some (if sat then fpsrQC else 0#32)
  else if op && (opc == 0b10000#5 || opc == 0b10001#5) && !immh.getLsbD 3 then
    let round := opc.getLsbD 0
    let sat := anyNarrowSimdLane esize vn (fun wide =>
      aslUnsignedSatFlag esize (aslRShr (simdLaneSInt (2 * esize) wide) shiftRightAmt round))
    some (if sat then fpsrQC else 0#32)
  else if (opc == 0b10010#5 || opc == 0b10011#5) && !immh.getLsbD 3 then
    let round := opc.getLsbD 0
    let sat := anyNarrowSimdLane esize vn (fun wide =>
      let val := if op then simdLaneUInt (2 * esize) wide else simdLaneSInt (2 * esize) wide
      aslSatFlag esize (aslRShr val shiftRightAmt round) op)
    some (if sat then fpsrQC else 0#32)
  else
    none

/-- Name the vector-FP mnemonic in `simdThreeSame` (`opcode[4:3] == 11`) when known. -/
def simdThreeSameFpMnemonic (u : Bool) (size : BitVec 2) (opcode : BitVec 5) : Option String :=
  let s1 := size.getLsbD 1
  match opcode with
  | 0b11000#5 => some (if !u then (if !s1 then "FMAXNM" else "FMINNM") else (if !s1 then "FMAXNMP" else "FMINNMP"))
  | 0b11001#5 => if !u then some (if !s1 then "FMLA" else "FMLS") else some "BFMLA/BFMLS"
  | 0b11010#5 => if !u then some (if !s1 then "FADD" else "FSUB") else (if !s1 then some "FADDP" else some "BFDOT")
  | 0b11011#5 => if !s1 then some (if !u then "FMULX" else "FMUL") else none
  | 0b11100#5 => if !u then (if !s1 then some "FCMEQ" else none) else some (if !s1 then "FCMGE" else "FCMGT")
  | 0b11101#5 => if u then some (if !s1 then "FACGE" else "FACGT") else some "FMLAL2/FMLSL2"
  | 0b11110#5 => some (if !u then (if !s1 then "FMAX" else "FMIN") else (if !s1 then "FMAXP" else "FMINP"))
  | 0b11111#5 => if !u then some (if !s1 then "FRECPS" else "FRSQRTS") else (if !s1 then some "FDIV" else none)
  | _ => none

/-- Evaluate `simdThreeSame` encodings beyond core logical/add/sub/cmp/sshl/addp. -/
def evalSimdThreeSameExt (q u : Bool) (size : BitVec 2) (opcode : BitVec 5)
    (vd vn vm : BitVec 128) : Except String (BitVec 128) :=
  let esize := 8 <<< size.toNat
  let truncQ (x : BitVec 128) : BitVec 128 := if q then x else (x.truncate 64).zeroExtend 128
  if opcode == 0b00011#5 && u && (size == 0b10#2 || size == 0b11#2) then
    -- BIT (`u = 1, size = 10`) and BIF (`u = 1, size = 11`)
    let mask := if size == 0b10#2 then vm else ~~~vm
    .ok (truncQ (vd ^^^ ((vd ^^^ vn) &&& mask)))
  else if (opcode == 0b00000#5 || opcode == 0b00010#5 || opcode == 0b00100#5) && size != 0b11#2 then
    -- Halving arithmetic: SHADD/UHADD (`00000`), SRHADD/URHADD (`00010`), SHSUB/UHSUB (`00100`)
    let round := opcode == 0b00010#5
    let isSub := opcode == 0b00100#5
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let v1 := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let v2 := if u then simdLaneUInt esize b else simdLaneSInt esize b
      let sum := if isSub then v1 - v2 else v1 + v2
      intToSimdLane esize (aslRShr sum 1 round))
    .ok res
  else if (opcode == 0b00001#5 || opcode == 0b00101#5) && !(size == 0b11#2 && !q) then
    -- Saturating arithmetic: SQADD/UQADD (`00001`), SQSUB/UQSUB (`00101`)
    let isSub := opcode == 0b00101#5
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let v1 := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let v2 := if u then simdLaneUInt esize b else simdLaneSInt esize b
      let sum := if isSub then v1 - v2 else v1 + v2
      aslSat esize sum u)
    .ok res
  else if !(size == 0b11#2 && !q) &&
      (opcode == 0b01001#5 || opcode == 0b01010#5 || opcode == 0b01011#5) then
    -- Variable shifts: SQSHL/UQSHL (`01001`), SRSHL/URSHL (`01010`), SQRSHL/UQRSHL (`01011`)
    let round := opcode == 0b01010#5 || opcode == 0b01011#5
    let sat := opcode == 0b01001#5 || opcode == 0b01011#5
    let maxSh : Int := Int.ofNat (esize + 1)
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let rawShift : Int := (b.truncate 8).toInt
      let shift : Int :=
        if rawShift > maxSh then maxSh else if rawShift < -maxSh then -maxSh else rawShift
      let val : Int := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let shifted : Int :=
        if shift >= 0 then val * Int.ofNat (1 <<< shift.toNat)
        else aslRShr val (-shift).toNat round
      if sat then aslSat esize shifted u else intToSimdLane esize shifted)
    .ok res
  else if (opcode == 0b01100#5 || opcode == 0b01101#5) && size != 0b11#2 then
    -- Element-wise min/max: SMAX/UMAX (`01100`), SMIN/UMIN (`01101`)
    let isMax := opcode == 0b01100#5
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let v1 := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let v2 := if u then simdLaneUInt esize b else simdLaneSInt esize b
      intToSimdLane esize (if isMax then max v1 v2 else min v1 v2))
    .ok res
  else if (opcode == 0b01110#5 || opcode == 0b01111#5) && size != 0b11#2 then
    -- Absolute difference & accumulate: SABD/UABD (`01110`), SABA/UABA (`01111`)
    let isAcc := opcode == 0b01111#5
    let diffVec := zipSimdLanes q esize vn vm (fun a b =>
      let v1 := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let v2 := if u then simdLaneUInt esize b else simdLaneSInt esize b
      BitVec.ofNat 128 (v1 - v2).natAbs)
    let res := if isAcc then zipSimdLanes q esize vd diffVec (fun acc d => acc + d) else diffVec
    .ok res
  else if opcode == 0b10010#5 && size != 0b11#2 then
    -- MLA (`u = 0`) and MLS (`u = 1`)
    let prodVec := zipSimdLanes q esize vn vm (fun a b => a * b)
    let res := zipSimdLanes q esize vd prodVec (fun acc p => if u then acc - p else acc + p)
    .ok res
  else if opcode == 0b10011#5 && !u && size != 0b11#2 then
    -- MUL (`u = 0, size != 11`)
    .ok (zipSimdLanes q esize vn vm (fun a b => a * b))
  else if opcode == 0b10011#5 && u && size == 0b00#2 then
    -- PMUL Vd.<8B|16B>, Vn.<8B|16B>, Vm.<8B|16B> (`u = 1, size = 00`)
    .ok (zipSimdLanes q 8 vn vm (fun a b => polyMul 8 (a.truncate 64) (b.truncate 64)))
  else if (opcode == 0b10100#5 || opcode == 0b10101#5) && size != 0b11#2 then
    -- Pairwise min/max: SMAXP/UMAXP (`10100`), SMINP/UMINP (`10101`)
    let isMax := opcode == 0b10100#5
    let elems := (if q then 128 else 64) / esize
    let half := elems / 2
    let res : BitVec 128 :=
      (List.range elems).foldl (fun acc i =>
        let src := if i < half then vn else vm
        let j := if i < half then i else i - half
        let a := getSimdLane src esize (2 * j)
        let b := getSimdLane src esize (2 * j + 1)
        let v1 := if u then simdLaneUInt esize a else simdLaneSInt esize a
        let v2 := if u then simdLaneUInt esize b else simdLaneSInt esize b
        let lane := intToSimdLane esize (if isMax then max v1 v2 else min v1 v2)
        acc ||| (lane <<< (i * esize))) 0#128
    .ok res
  else if opcode == 0b10110#5 && (size == 0b01#2 || size == 0b10#2) then
    -- SQDMULH (`u = 0`) and SQRDMULH (`u = 1`) on 16-bit (`01`) and 32-bit (`10`) lanes
    let res := zipSimdLanes q esize vn vm (fun a b =>
      let v1 := simdLaneSInt esize a
      let v2 := simdLaneSInt esize b
      aslSignedSat esize (aslRShr (2 * v1 * v2) esize u))
    .ok res
  else
    match simdThreeSameFpMnemonic u size opcode with
    | some mnem =>
      .error (toString "unsupported AdvSIMD: simdThreeSame vector-FP " ++ toString (mnem) ++ toString " (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — vector FP not modeled in Arm64/Trusted/ISA" : String)
    | none =>
      .error (toString "unsupported AdvSIMD: simdThreeSame (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED" : String)

/-- Optional `FPSR.QC` saturation flag for `evalSimdThreeSameExt` (`some` only for saturating opcodes). -/
def evalSimdThreeSameExtSatFlags (q u : Bool) (size : BitVec 2) (opcode : BitVec 5)
    (vn vm : BitVec 128) : Option (BitVec 32) :=
  let esize := 8 <<< size.toNat
  if (opcode == 0b00001#5 || opcode == 0b00101#5) && !(size == 0b11#2 && !q) then
    let isSub := opcode == 0b00101#5
    let sat := anyZipSimdLane q esize vn vm (fun a b =>
      let v1 := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let v2 := if u then simdLaneUInt esize b else simdLaneSInt esize b
      let sum := if isSub then v1 - v2 else v1 + v2
      aslSatFlag esize sum u)
    some (if sat then fpsrQC else 0#32)
  else if !(size == 0b11#2 && !q) && (opcode == 0b01001#5 || opcode == 0b01011#5) then
    let round := opcode == 0b01011#5
    let maxSh : Int := Int.ofNat (esize + 1)
    let sat := anyZipSimdLane q esize vn vm (fun a b =>
      let rawShift : Int := (b.truncate 8).toInt
      let shift : Int :=
        if rawShift > maxSh then maxSh else if rawShift < -maxSh then -maxSh else rawShift
      let val : Int := if u then simdLaneUInt esize a else simdLaneSInt esize a
      let shifted : Int :=
        if shift >= 0 then val * Int.ofNat (1 <<< shift.toNat)
        else aslRShr val (-shift).toNat round
      aslSatFlag esize shifted u)
    some (if sat then fpsrQC else 0#32)
  else if opcode == 0b10110#5 && (size == 0b01#2 || size == 0b10#2) then
    let sat := anyZipSimdLane q esize vn vm (fun a b =>
      let v1 := simdLaneSInt esize a
      let v2 := simdLaneSInt esize b
      aslSignedSatFlag esize (aslRShr (2 * v1 * v2) esize u))
    some (if sat then fpsrQC else 0#32)
  else
    none

/-- Name the vector-FP mnemonic in `simdTwoRegMisc` when known. -/
def simdTwoRegMiscFpMnemonic (u : Bool) (size : BitVec 2) (opcode : BitVec 5) : Option String :=
  let s1 := size.getLsbD 1
  match opcode with
  | 0b01100#5 => if s1 then some (if !u then "FCMGT" else "FCMGE") else none
  | 0b01101#5 => if !u && !s1 then some "FCMEQ" else if u && s1 then some "FCMLE" else none
  | 0b01110#5 => if !u && s1 then some "FCMLT" else none
  | 0b10110#5 => if !s1 then some (if !u then "FCVTN" else "FCVTXN") else none
  | 0b10111#5 => if !u && !s1 then some "FCVTL" else none
  | 0b11000#5 => if !u then some (if !s1 then "FRINTN" else "FRINTP") else if !s1 then some "FRINTA" else none
  | 0b11001#5 => some (if !u then (if !s1 then "FRINTM" else "FRINTZ") else (if !s1 then "FRINTX" else "FRINTI"))
  | 0b11010#5 => some (if !u then (if !s1 then "FCVTNS" else "FCVTPS") else (if !s1 then "FCVTNU" else "FCVTPU"))
  | 0b11011#5 => some (if !u then (if !s1 then "FCVTMS" else "FCVTZS") else (if !s1 then "FCVTMU" else "FCVTZU"))
  | 0b11100#5 => if !s1 then some (if !u then "FCVTAS" else "FCVTAU") else none
  | 0b11101#5 => some (if !s1 then (if !u then "SCVTF" else "UCVTF") else (if !u then "FRECPE" else "FRSQRTE"))
  | 0b11110#5 => if !s1 then some (if !u then "FRINT32Z" else "FRINT32X") else none
  | 0b11111#5 => if !s1 then some (if !u then "FRINT64Z" else "FRINT64X") else if u then some "FSQRT" else none
  | _ => none

/-- Evaluate `simdTwoRegMisc` encodings beyond core `REV64`/`REV32`/zero-comparisons/`NOT`/`CNT`. -/
def evalSimdTwoRegMiscExt (q u : Bool) (size : BitVec 2) (opcode : BitVec 5)
    (vd vn : BitVec 128) : Except String (BitVec 128) :=
  let esize := 8 <<< size.toNat
  if !u && opcode == 0b00001#5 && size == 0b00#2 then
    -- REV16 Vd.<8B|16B>, Vn.<8B|16B>: reverse bytes within each 16-bit halfword
    let lo := rev16_64 (vn.truncate 64)
    let hi := if q then rev16_64 (vn.extractLsb' 64 64) else 0#64
    .ok (hi ++ lo)
  else if (opcode == 0b00010#5 || opcode == 0b00110#5) && size != 0b11#2 then
    -- Pairwise add long & accumulate: SADDLP/UADDLP (`00010`), SADALP/UADALP (`00110`)
    let isAcc := opcode == 0b00110#5
    let dstEsize := 2 * esize
    let numPairs := (if q then 128 else 64) / dstEsize
    let dstMask : BitVec 128 := (1#128 <<< dstEsize) - 1#128
    let res : BitVec 128 :=
      (List.range numPairs).foldl (fun acc e =>
        let p0 := getSimdLane vn esize (2 * e)
        let p1 := getSimdLane vn esize (2 * e + 1)
        let v0 := if u then simdLaneUInt esize p0 else simdLaneSInt esize p0
        let v1 := if u then simdLaneUInt esize p1 else simdLaneSInt esize p1
        let sum := intToSimdLane dstEsize (v0 + v1)
        let outLane := if isAcc then (getSimdLane vd dstEsize e + sum) &&& dstMask else sum
        acc ||| (outLane <<< (e * dstEsize))) 0#128
    .ok res
  else if opcode == 0b00011#5 && !(size == 0b11#2 && !q) then
    -- SUQADD (`u = 0`) and USQADD (`u = 1`)
    let res := zipSimdLanes q esize vn vd (fun a d =>
      if !u then
        aslSignedSat esize (simdLaneUInt esize a + simdLaneSInt esize d)
      else
        aslUnsignedSat esize (simdLaneSInt esize a + simdLaneUInt esize d))
    .ok res
  else if opcode == 0b00100#5 && size != 0b11#2 then
    -- CLS (`u = 0`) / CLZ (`u = 1`)
    let res := mapSimdLanes q esize vn (fun lane =>
      BitVec.ofNat 128 (if u then simdClz esize lane else simdCls esize lane))
    .ok res
  else if u && opcode == 0b00101#5 && size == 0b01#2 then
    -- RBIT Vd.<8B|16B>, Vn.<8B|16B>: reverse bits within each byte (`size = 01` in encoding)
    let res := mapSimdLanes q 8 vn (fun a => (reverseBits (a.truncate 8)).zeroExtend 128)
    .ok res
  else if opcode == 0b00111#5 && !(size == 0b11#2 && !q) then
    -- SQABS (`u = 0`) and SQNEG (`u = 1`)
    let res := mapSimdLanes q esize vn (fun a =>
      let v := simdLaneSInt esize a
      aslSignedSat esize (if u then -v else Int.ofNat v.natAbs))
    .ok res
  else if opcode == 0b01011#5 && !(size == 0b11#2 && !q) then
    -- ABS (`u = 0`) and NEG (`u = 1`)
    let res := mapSimdLanes q esize vn (fun a =>
      let v := simdLaneSInt esize a
      intToSimdLane esize (if u then -v else Int.ofNat v.natAbs))
    .ok res
  else if opcode == 0b01111#5 && size.getLsbD 1 && !(size == 0b11#2 && !q) then
    -- FABS (`u = 0`) and FNEG (`u = 1`) on 32-bit (`size = 10`) and 64-bit (`size = 11, q = 1`) lanes
    let signBit : BitVec 128 := 1#128 <<< (esize - 1)
    let res := mapSimdLanes q esize vn (fun a =>
      if u then a ^^^ signBit else a &&& (signBit - 1#128))
    .ok res
  else if opcode == 0b10010#5 && size != 0b11#2 then
    -- XTN/XTN2 (`u = 0`) and SQXTUN/SQXTUN2 (`u = 1`)
    let res := narrowSimdLanes q esize vd vn (fun wide =>
      if !u then wide
      else aslUnsignedSat esize (simdLaneSInt (2 * esize) wide))
    .ok res
  else if u && opcode == 0b10011#5 && size != 0b11#2 then
    -- SHLL / SHLL2 Vd.<2*esize>, Vn.<esize>, #esize (`U = 1, opcode = 10011`)
    let half : BitVec 128 := if q then vn >>> 64 else (vn.truncate 64).zeroExtend 128
    let dstEsize := 2 * esize
    let numLanes := 64 / esize
    let dstMask : BitVec 128 := (1#128 <<< dstEsize) - 1#128
    let res : BitVec 128 :=
      (List.range numLanes).foldl (fun acc e =>
        let lane := getSimdLane half esize e
        let wide := (lane <<< esize) &&& dstMask
        acc ||| (wide <<< (e * dstEsize))) 0#128
    .ok res
  else if opcode == 0b10100#5 && size != 0b11#2 then
    -- SQXTN/SQXTN2 (`u = 0`) and UQXTN/UQXTN2 (`u = 1`)
    let res := narrowSimdLanes q esize vd vn (fun wide =>
      if !u then aslSignedSat esize (simdLaneSInt (2 * esize) wide)
      else aslUnsignedSat esize (simdLaneUInt (2 * esize) wide))
    .ok res
  else if opcode == 0b11100#5 && size == 0b10#2 then
    -- URECPE (`u = 0`) and URSQRTE (`u = 1`) on 32-bit lanes (`2S` / `4S`)
    let res := mapSimdLanes q 32 vn (fun x =>
      if !u then
        if !x.getLsbD 31 then 0xffffffff#128
        else
          let scaled := (x.extractLsb' 23 9).toNat * 2 + 1
          let b := (1 <<< 19) / scaled
          let r := (b + 1) / 2
          (BitVec.ofNat 128 r) <<< 23
      else
        if (x.extractLsb' 30 2) == 0#2 then 0xffffffff#128
        else
          let a :=
            if x.getLsbD 31 then (((x.extractLsb' 24 8).toNat) * 2 + 1) * 2
            else ((x.extractLsb' 23 8).toNat) * 2 + 1
          let b := (List.range 512).foldl (fun best k =>
            let cand := 512 + k
            if a * cand * cand < (1 <<< 28) then cand else best) 512
          let r := (b + 1) / 2
          (BitVec.ofNat 128 r) <<< 23)
    .ok res
  else
    match simdTwoRegMiscFpMnemonic u size opcode with
    | some mnem =>
      .error (toString "unsupported AdvSIMD: simdTwoRegMisc vector-FP " ++ toString (mnem) ++ toString " (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — vector FP not modeled in Arm64/Trusted/ISA" : String)
    | none =>
      .error (toString "unsupported AdvSIMD: simdTwoRegMisc (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED" : String)

/-- Optional `FPSR.QC` saturation flag for `evalSimdTwoRegMiscExt` (`some` only for saturating opcodes). -/
def evalSimdTwoRegMiscExtSatFlags (q u : Bool) (size : BitVec 2) (opcode : BitVec 5)
    (vd vn : BitVec 128) : Option (BitVec 32) :=
  let esize := 8 <<< size.toNat
  if opcode == 0b00011#5 && !(size == 0b11#2 && !q) then
    let sat := anyZipSimdLane q esize vn vd (fun a d =>
      if !u then
        aslSignedSatFlag esize (simdLaneUInt esize a + simdLaneSInt esize d)
      else
        aslUnsignedSatFlag esize (simdLaneSInt esize a + simdLaneUInt esize d))
    some (if sat then fpsrQC else 0#32)
  else if opcode == 0b00111#5 && !(size == 0b11#2 && !q) then
    let sat := anySimdLane q esize vn (fun a =>
      let v := simdLaneSInt esize a
      aslSignedSatFlag esize (if u then -v else Int.ofNat v.natAbs))
    some (if sat then fpsrQC else 0#32)
  else if opcode == 0b10010#5 && size != 0b11#2 && u then
    let sat := anyNarrowSimdLane esize vn (fun wide =>
      aslUnsignedSatFlag esize (simdLaneSInt (2 * esize) wide))
    some (if sat then fpsrQC else 0#32)
  else if opcode == 0b10100#5 && size != 0b11#2 then
    let sat := anyNarrowSimdLane esize vn (fun wide =>
      if !u then aslSignedSatFlag esize (simdLaneSInt (2 * esize) wide)
      else aslUnsignedSatFlag esize (simdLaneUInt (2 * esize) wide))
    some (if sat then fpsrQC else 0#32)
  else
    none

/-- Supervisor-call handler that fails closed on every `SVC #0` with
    `.Exception "unmodeled syscall (svc)"`. -/
def noSyscalls (s : State) : State :=
  s.setStatus (.Exception "unmodeled syscall (svc)")

/-- Execute a single AArch64 `Instr` on machine state `s`, delegating `SVC #0` to `svc`. -/
def execInstWithSvc (svc : State → State) (inst : Instr) (s : State) : State :=
  match inst with
  -- Loads and Stores (GPR)
  | .ldr w sz signed rt addr =>
    execLdr w sz signed rt addr s
  | .ldrLit w signed rt offset =>
    execLdrLit w (if signed then .W32 else (w : MemWidth)) signed rt offset s
  | .str sz rt addr =>
    execStr sz rt addr s
  | .ldp w signed rt1 rt2 addr =>
    execLdp w signed rt1 rt2 addr s
  | .stp w rt1 rt2 addr =>
    execStp w rt1 rt2 addr s

  -- Data Processing — Immediate
  | .adr page rd offset =>
    let base := if page then s.pc &&& 0xfffffffffffff000#64 else s.pc
    (s.writeReg64 rd (base + offset)).advancePC
  | .addSubImm w op rd rn imm12 shift12 =>
    execAddSubImm w op rd rn imm12 shift12 s
  | .logicalImm w op rd rn mask =>
    execLogicalImm w op rd rn mask s
  | .moveWide w op rd imm16 hw =>
    execMoveWide w op rd imm16 hw s
  | .bitfield w op rd rn immr imms =>
    execBitfield w op rd rn immr imms s
  | .extr w rd rn rm lsb =>
    let res : BitVec 64 :=
      match w with
      | .W32 =>
        let n32 := s.readReg32 rn
        let m32 := s.readReg32 rm
        let pair64 : BitVec 64 := n32 ++ m32
        ((pair64 >>> (lsb % 32)).truncate 32).zeroExtend 64
      | .W64 =>
        let n64 := s.readReg64 rn
        let m64 := s.readReg64 rm
        let pair128 : BitVec 128 := n64 ++ m64
        (pair128 >>> (lsb % 64)).truncate 64
    (s.writeReg w rd res).advancePC

  -- Data Processing — Register
  | .logicalShift w op rd rn rm shift amount =>
    execLogicalShift w op rd rn rm shift amount s
  | .addSubShift w op rd rn rm shift amount =>
    execAddSubShift w op rd rn rm shift amount s
  | .addSubExt w op rd rn rm ext amount =>
    execAddSubExt w op rd rn rm ext amount s
  | .addSubCarry w op rd rn rm =>
    execAddSubCarry w op rd rn rm s
  | .condCompareReg w isSub rn rm nzcv cond =>
    execCondCompare w isSub false rn 0#64 rm nzcv cond s
  | .condCompareImm w isSub rn imm5 nzcv cond =>
    execCondCompare w isSub true rn (imm5.zeroExtend 64) .xzr nzcv cond s
  | .condSelect w op rd rn rm cond =>
    execCondSelect w op rd rn rm cond s
  | .dataProc1 w op rd rn =>
    execDataProc1 w op rd rn s
  | .dataProc2 w op rd rn rm =>
    execDataProc2 w op rd rn rm s
  | .dataProc3 w op rd rn rm ra =>
    execDataProc3 w op rd rn rm ra s

  -- Control Flow
  | .b offset =>
    s.setPC (s.pc + offset)
  | .bl offset =>
    let s1 := s.writeReg64 Reg.lr (s.pc + 4#64)
    s1.setPC (s.pc + offset)
  | .bCond cond offset =>
    if ConditionHolds cond s.pstate then
      s.setPC (s.pc + offset)
    else
      s.advancePC
  | .br rn =>
    let targetAddr := s.readReg64 rn
    s.setPC targetAddr
  | .blr rn =>
    let targetAddr := s.readReg64 rn
    let s1 := s.writeReg64 Reg.lr (s.pc + 4#64)
    s1.setPC targetAddr
  | .ret rn =>
    let targetAddr := s.readReg64 rn
    s.setPC targetAddr
  | .cbz w isNonZero rt offset =>
    let val := s.readReg w rt
    let cond := if isNonZero then (val == 0#64) != true else val == 0#64
    if cond then
      s.setPC (s.pc + offset)
    else
      s.advancePC
  | .tbz _ isNonZero rt bitPos offset =>
    let val := s.readReg64 rt
    let bit := val.getLsbD bitPos
    if bit == isNonZero then
      s.setPC (s.pc + offset)
    else
      s.advancePC

  -- Misc
  | .nop =>
    s.advancePC

  -- System, Exclusive, Atomic, SIMD/FP, and Cryptographic instructions
  | .system isHalt imm =>
    if isHalt then
      if imm == 1#16 then
        s.setStatus (.Exited 101#64)
      else
        s.setStatus .Halted
    else if imm == 0#16 then
      svc s
    else
      s.setStatus (.Exception "unmodeled syscall (svc)")

  | .ldarStlr sz isLoad rn rt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if isLoad then
        if !s.mem.canRead ea sz.bytes then
          s.setStatus (.Exception "permission fault")
        else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let val := s.mem.readSized sz false ea
        (s.writeReg w rt val).advancePC
      else
        if !s.mem.canWrite ea sz.bytes then
          s.setStatus (.Exception "permission fault")
        else
        let val := s.readReg64 rt
        (s.setMem (s.mem.writeSized sz ea val)).advancePC

  -- Load-Exclusive (`LDXR*` / `LDAXR*`). Single-threaded model with no other observers: the
  -- exclusive monitor is not represented, so this is a plain load (acquire is identical).
  -- Exclusive accesses require natural alignment regardless of `SCTLR_EL1.A`, like `LDAR`.
  | .ldxr sz _acq rn rt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if !s.mem.canRead ea sz.bytes then
        s.setStatus (.Exception "permission fault")
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let val := s.mem.readSized sz false ea
        (s.writeReg w rt val).advancePC

  -- Store-Exclusive (`STXR*` / `STLXR*`). Single-threaded model without an exclusive monitor:
  -- spurious hardware failures are drawn from the finite oracle stream `s.exclFails` (`headD false`,
  -- consumed via `s.stepExclOracle`). On failure (`s.exclWillFail = true`), memory is unchanged and
  -- the status register is written `Ws := 1`; on success (`s.exclWillFail = false`), the store is
  -- performed and `Ws := 0`. Decode rejects the CONSTRAINED UNPREDICTABLE overlaps `rs == rt` and
  -- `rs == rn` (`rn != SP`).
  | .stxr sz _rel rs rn rt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if !s.mem.canWrite ea sz.bytes then
        s.setStatus (.Exception "permission fault")
      else
        let val := s.readReg64 rt
        if s.exclWillFail then
          ((s.stepExclOracle).writeReg .W32 rs 1#64).advancePC
        else
          (((s.stepExclOracle).setMem (s.mem.writeSized sz ea val)).writeReg .W32 rs 0#64).advancePC

  | .sysReg isRead sysreg rt =>
    if sysreg == 0x5e82#15 then
      if isRead then
        (s.writeReg64 rt s.tpidrEl0).advancePC
      else
        ({ s with tpidrEl0 := s.readReg64 rt }).advancePC
    else if sysreg == 0x5a10#15 then
      -- `NZCV`: N = bit 31, Z = bit 30, C = bit 29, V = bit 28; other bits RES0.
      if isRead then
        let ps := s.pstate
        let b (x : Bool) (i : Nat) : BitVec 64 := if x then 1#64 <<< i else 0#64
        (s.writeReg64 rt (b ps.n 31 ||| b ps.z 30 ||| b ps.c 29 ||| b ps.v 28)).advancePC
      else
        (s.setPState (PState.ofBits4 ((s.readReg64 rt).extractLsb' 28 4))).advancePC
    else if sysreg == 0x5a20#15 then
      -- `FPCR`: pinned to `0#64` (RNE, no FZ, DN = 0, no trap enables).
      if isRead then
        (s.writeReg64 rt 0#64).advancePC
      else if s.readReg64 rt == 0#64 then
        s.advancePC
      else
        { s with status := .Exception "unsupported FPCR value" }
    else if sysreg == 0x5a21#15 then
      -- `FPSR`: reads zero-extended 32-bit `s.fpsr`; writes mask to modeled bits `fpsrMask` (`0x0800009f`).
      if isRead then
        (s.writeReg64 rt (s.fpsr.zeroExtend 64)).advancePC
      else
        (s.setFpsr ((s.readReg64 rt).truncate 32 &&& fpsrMask)).advancePC
    else if sysreg == 0x5807#15 then
      -- `DCZID_EL0` (read-only): `DZP = 0` (DC ZVA permitted), `BS = 4` (2^4 words = 64 bytes).
      if isRead then
        (s.writeReg64 rt 4#64).advancePC
      else
        { s with status := .Exception "unmodeled system register" }
    else
      { s with status := .Exception "unmodeled system register" }

  | .barrier _crm _op2 =>
    s.advancePC

  | .ldpSimd sz vt1 vt2 addr =>
    if !checkAddrSPAligned s addr then
      s.setStatus (.Exception "SP alignment fault")
    else
      let (ea, wb) := evalAddrMode s addr
      let stepBytes : BitVec 64 :=
        match sz with | .B8 => 1#64 | .H16 => 2#64 | .S32 => 4#64 | .D64 => 8#64 | .Q128 => 16#64
      if !(s.mem.canRead ea sz.bytes && s.mem.canRead (ea + stepBytes) sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
      let v1 := s.mem.readSimdSized sz ea
      let v2 := s.mem.readSimdSized sz (ea + stepBytes)
      let s1 := match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s
      let s2 := s1.writeVReg128 vt1 v1
      let s3 := s2.writeVReg128 vt2 v2
      s3.advancePC

  | .stpSimd sz vt1 vt2 addr =>
    if !checkAddrSPAligned s addr then
      s.setStatus (.Exception "SP alignment fault")
    else
      let (ea, wb) := evalAddrMode s addr
      let stepBytes : BitVec 64 :=
        match sz with | .B8 => 1#64 | .H16 => 2#64 | .S32 => 4#64 | .D64 => 8#64 | .Q128 => 16#64
      if !(s.mem.canWrite ea sz.bytes && s.mem.canWrite (ea + stepBytes) sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
      let v1 := s.readVReg128 vt1
      let v2 := s.readVReg128 vt2
      let m1 := s.mem.writeSimdSized sz ea v1
      let m2 := m1.writeSimdSized sz (ea + stepBytes) v2
      let s1 := s.setMem m2
      let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
      s2.advancePC

  | .ldrSimd sz vt addr =>
    if !checkAddrSPAligned s addr then
      s.setStatus (.Exception "SP alignment fault")
    else
      let (ea, wb) := evalAddrMode s addr
      if !s.mem.canRead ea sz.bytes then
        s.setStatus (.Exception "permission fault")
      else
      let val := s.mem.readSimdSized sz ea
      let s1 := match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s
      (s1.writeVReg128 vt val).advancePC

  | .strSimd sz vt addr =>
    if !checkAddrSPAligned s addr then
      s.setStatus (.Exception "SP alignment fault")
    else
      let (ea, wb) := evalAddrMode s addr
      if !s.mem.canWrite ea sz.bytes then
        s.setStatus (.Exception "permission fault")
      else
      let val := s.readVReg128 vt
      let s1 := s.setMem (s.mem.writeSimdSized sz ea val)
      let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
      s2.advancePC

  | .st1SinglePost q rm opcode sBit size rn vt =>
    let validSt1 :=
      (opcode == 0b000#3) ||
      (opcode == 0b010#3 && (size.extractLsb' 0 1) == 0#1) ||
      (opcode == 0b100#3 && (size == 0b00#2 || (size == 0b01#2 && !sBit)))
    if !validSt1 then
      { s with status := .Exception (toString "unsupported AdvSIMD: st1SinglePost (q=" ++ toString (if q then 1 else 0) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString " S=" ++ toString (if sBit then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString ") — multi-register ST2-ST4 single-structure or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      let v := s.readVReg128 vt
      let opcHi := opcode.extractLsb' 1 2
      let nbytes : Nat :=
        if opcHi == 0#2 then 1 else if opcHi == 1#2 then 2
        else if (size.extractLsb' 0 1) == 0#1 then 4 else 8
      if !s.mem.canWrite ea nbytes then
        s.setStatus (.Exception "permission fault")
      else
      let sNat := if sBit then 1 else 0
      let qNat := if q then 1 else 0
      let (m1, stepBytes) : Memory × BitVec 64 :=
        if opcHi == 0#2 then
          let idx := (qNat <<< 3) ||| (sNat <<< 2) ||| size.toNat
          let b8 := (v >>> (idx * 8)).truncate 8
          (s.mem.write8 ea b8, 1#64)
        else if opcHi == 1#2 then
          let idx := (qNat <<< 2) ||| (sNat <<< 1) ||| (size.extractLsb' 1 1).toNat
          let h16 := (v >>> (idx * 16)).truncate 16
          (s.mem.write16 ea h16, 2#64)
        else if (size.extractLsb' 0 1) == 0#1 then
          let idx := (qNat <<< 1) ||| sNat
          let w32 := (v >>> (idx * 32)).truncate 32
          (s.mem.write32 ea w32, 4#64)
        else
          let idx := qNat
          let d64 := (v >>> (idx * 64)).truncate 64
          (s.mem.write64 ea d64, 8#64)
      let inc := if rm == 31#5 then stepBytes else s.readReg64 (Reg.fromZRBits rm)
      let s1 := s.setMem m1
      (s1.writeReg64 rn (ea + inc)).advancePC

  | .aes op vd vn =>
    let dVal := s.readVReg128 vd
    let nVal := s.readVReg128 vn
    let res := evalAesOp op dVal nVal
    (s.writeVReg128 vd res).advancePC

  | .fmovGprVec sf ftype rmode opcode rn rd =>
    if opcode == 0b110#3 then
      let dstReg := Reg.fromZRBits rd
      if !sf && ftype == 0b00#2 && rmode == 0b00#2 then
        (s.writeReg32 dstReg (s.readVReg32 rn)).advancePC
      else if sf && ftype == 0b01#2 && rmode == 0b00#2 then
        (s.writeReg64 dstReg (s.readVReg64 rn)).advancePC
      else if sf && ftype == 0b10#2 && rmode == 0b01#2 then
        let hi64 := (s.readVReg128 rn).extractLsb' 64 64
        (s.writeReg64 dstReg hi64).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fmovGprVec (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if opcode == 0b111#3 then
      let srcReg := Reg.fromZRBits rn
      if !sf && ftype == 0b00#2 && rmode == 0b00#2 then
        (s.writeVReg32 rd (s.readReg32 srcReg)).advancePC
      else if sf && ftype == 0b01#2 && rmode == 0b00#2 then
        (s.writeVReg64 rd (s.readReg64 srcReg)).advancePC
      else if sf && ftype == 0b10#2 && rmode == 0b01#2 then
        let lo64 := (s.readVReg128 rd).truncate 64
        let hi64 := s.readReg64 srcReg
        (s.writeVReg128 rd (hi64 ++ lo64)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fmovGprVec (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if opcode == 0b000#3 || opcode == 0b001#3 then
      let unsigned := opcode == 0b001#3
      let dstReg := Reg.fromZRBits rd
      if !sf && ftype == 0b00#2 then
        let x := s.readVReg32 rn
        ((s.writeReg32 dstReg (evalFpToInt32_32 unsigned rmode x)).orFpsr (evalFpToIntFlags32_32 unsigned rmode x)).advancePC
      else if sf && ftype == 0b00#2 then
        let x := s.readVReg32 rn
        ((s.writeReg64 dstReg (evalFpToInt64_32 unsigned rmode x)).orFpsr (evalFpToIntFlags64_32 unsigned rmode x)).advancePC
      else if !sf && ftype == 0b01#2 then
        let x := s.readVReg64 rn
        ((s.writeReg32 dstReg (evalFpToInt32_64 unsigned rmode x)).orFpsr (evalFpToIntFlags32_64 unsigned rmode x)).advancePC
      else if sf && ftype == 0b01#2 then
        let x := s.readVReg64 rn
        ((s.writeReg64 dstReg (evalFpToInt64_64 unsigned rmode x)).orFpsr (evalFpToIntFlags64_64 unsigned rmode x)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fmovGprVec (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if rmode == 0b00#2 && (opcode == 0b100#3 || opcode == 0b101#3) then
      let unsigned := opcode == 0b101#3
      let dstReg := Reg.fromZRBits rd
      if !sf && ftype == 0b00#2 then
        let x := s.readVReg32 rn
        ((s.writeReg32 dstReg (evalFpToIntRound32_32 unsigned .RNA 0 x)).orFpsr (evalFpToIntRoundFlags32_32 unsigned .RNA 0 x)).advancePC
      else if sf && ftype == 0b00#2 then
        let x := s.readVReg32 rn
        ((s.writeReg64 dstReg (evalFpToIntRound64_32 unsigned .RNA 0 x)).orFpsr (evalFpToIntRoundFlags64_32 unsigned .RNA 0 x)).advancePC
      else if !sf && ftype == 0b01#2 then
        let x := s.readVReg64 rn
        ((s.writeReg32 dstReg (evalFpToIntRound32_64 unsigned .RNA 0 x)).orFpsr (evalFpToIntRoundFlags32_64 unsigned .RNA 0 x)).advancePC
      else if sf && ftype == 0b01#2 then
        let x := s.readVReg64 rn
        ((s.writeReg64 dstReg (evalFpToIntRound64_64 unsigned .RNA 0 x)).orFpsr (evalFpToIntRoundFlags64_64 unsigned .RNA 0 x)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fmovGprVec (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if rmode == 0b00#2 && (opcode == 0b010#3 || opcode == 0b011#3) then
      let unsigned := opcode == 0b011#3
      let srcReg := Reg.fromZRBits rn
      if !sf && ftype == 0b00#2 then
        let x := s.readReg32 srcReg
        ((s.writeVReg32 rd (evalIntToFp32_32 unsigned x)).orFpsr (evalIntToFpFlags32_32 unsigned x)).advancePC
      else if sf && ftype == 0b00#2 then
        let x := s.readReg64 srcReg
        ((s.writeVReg32 rd (evalIntToFp32_64 unsigned x)).orFpsr (evalIntToFpFlags32_64 unsigned x)).advancePC
      else if !sf && ftype == 0b01#2 then
        let x := s.readReg32 srcReg
        ((s.writeVReg64 rd (evalIntToFp64_32 unsigned x)).orFpsr (evalIntToFpFlags64_32 unsigned x)).advancePC
      else if sf && ftype == 0b01#2 then
        let x := s.readReg64 srcReg
        ((s.writeVReg64 rd (evalIntToFp64_64 unsigned x)).orFpsr (evalIntToFpFlags64_64 unsigned x)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fmovGprVec (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fmovGprVec (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED or FJCVTZS not modeled in Arm64/Trusted/ISA" : String) }

  | .simdImmShift q op immh immb opc rn rd =>
    if immh == 0#4 then
      if opc.getLsbD 0 then
        applySimdResult s rd (evalSimdModImmExt q op immb opc rn (s.readVReg128 rd))
      else
        let imm8 : BitVec 8 := immb ++ rn
        let cmode := opc.extractLsb' 1 4
        let writeD64 (d64 : BitVec 64) : State :=
          let res128 : BitVec 128 := if q then d64 ++ d64 else d64.zeroExtend 128
          (s.writeVReg128 rd res128).advancePC
        if !op && cmode == 0b1110#4 then
          writeD64 (imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8)
        else if op && cmode == 0b1110#4 then
          let b (i : Nat) : BitVec 8 := if imm8.getLsbD i then 0xff#8 else 0x00#8
          writeD64 (b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0)
        else if !op && (cmode &&& 0b1001#4) == 0b0000#4 then
          let sh := (cmode.extractLsb' 1 2).toNat * 8
          let w32 : BitVec 32 := (imm8.zeroExtend 32) <<< sh
          writeD64 (w32 ++ w32)
        else if !op && (cmode &&& 0b1101#4) == 0b1000#4 then
          let sh := (cmode.extractLsb' 1 1).toNat * 8
          let h16 : BitVec 16 := (imm8.zeroExtend 16) <<< sh
          writeD64 (h16 ++ h16 ++ h16 ++ h16)
        else
          applySimdResult s rd (evalSimdModImmExt q op immb opc rn (s.readVReg128 rd))
    else
      let immhb := (immh ++ immb).toNat
      let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
      let shiftLeftAmt := immhb - esize
      let shiftRightAmt := 2 * esize - immhb
      let vn := s.readVReg128 rn
      if !op && opc == 0b01010#5 && !(immh.getLsbD 3 && !q) then
        let res := mapSimdLanes q esize vn (fun lane => lane <<< shiftLeftAmt)
        (s.writeVReg128 rd res).advancePC
      else if op && opc == 0b10100#5 && !immh.getLsbD 3 then
        let half : BitVec 64 := if q then vn.extractLsb' 64 64 else vn.truncate 64
        let dstEsize := 2 * esize
        let numLanes := 64 / esize
        let srcMask : BitVec 64 := (1#64 <<< esize) - 1#64
        let res : BitVec 128 := Id.run do
          let mut acc : BitVec 128 := 0#128
          for i in [0:numLanes] do
            let lane64 := (half >>> (i * esize)) &&& srcMask
            let wide128 := (lane64.zeroExtend 128) <<< shiftLeftAmt
            acc := acc ||| (wide128 <<< (i * dstEsize))
          return acc
        (s.writeVReg128 rd res).advancePC
      else if op && opc == 0b00000#5 && !(immh.getLsbD 3 && !q) then
        let res := mapSimdLanes q esize vn (fun lane => lane >>> shiftRightAmt)
        (s.writeVReg128 rd res).advancePC
      else if op && (opc == 0b01000#5 || opc == 0b01010#5) && !(immh.getLsbD 3 && !q) then
        -- SRI (`01000`) / SLI (`01010`): insert the shifted source, keeping the destination bits
        -- the shift vacates (`ASL: result = (operand2 AND NOT mask) OR shifted`).
        let isSli := opc == 0b01010#5
        let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
        let res := zipSimdLanes q esize vn (s.readVReg128 rd) (fun a d =>
          let m : BitVec 128 :=
            if isSli then (laneMask <<< shiftLeftAmt) &&& laneMask else laneMask >>> shiftRightAmt
          let sh := if isSli then (a <<< shiftLeftAmt) &&& laneMask else a >>> shiftRightAmt
          (d &&& ~~~m) ||| (sh &&& m))
        (s.writeVReg128 rd res).advancePC
      else
        applySimdSatResult s rd
          (evalSimdImmShiftNonZeroExt q op immh immb opc (s.readVReg128 rd) vn)
          (evalSimdImmShiftNonZeroExtSatFlags q op immh immb opc vn)

  | .simdInsDup q op imm5 imm4 rn rd =>
    if (imm5.extractLsb' 0 4) == 0#4 then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdInsDup (q=" ++ toString (if q then 1 else 0) ++ toString " op=" ++ toString (if op then 1 else 0) ++ toString " imm5=" ++ toString (imm5.toNat) ++ toString " imm4=" ++ toString (imm4.toNat) ++ toString ") — architecturally UNDEFINED" : String) }
    else
      let esize : Nat :=
        if (imm5.extractLsb' 0 1) == 1#1 then 8
        else if (imm5.extractLsb' 0 2) == 2#2 then 16
        else if (imm5.extractLsb' 0 3) == 4#3 then 32
        else 64
      let dstIdx : Nat :=
        if esize == 8 then imm5.toNat >>> 1
        else if esize == 16 then imm5.toNat >>> 2
        else if esize == 32 then imm5.toNat >>> 3
        else imm5.toNat >>> 4
      let mask : BitVec 128 := (1#128 <<< esize) - 1#128
      if !op && imm4 == 0b0001#4 && !(esize == 64 && !q) then
        let elem := ((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
        let res := mapSimdLanes q esize 0#128 (fun _ => elem)
        (s.writeVReg128 rd res).advancePC
      else if !op && imm4 == 0b0000#4 && !(esize == 64 && !q) then
        let elem := getSimdLane (s.readVReg128 rn) esize dstIdx
        let res := mapSimdLanes q esize 0#128 (fun _ => elem)
        (s.writeVReg128 rd res).advancePC
      else if q && !op && imm4 == 0b0011#4 then
        let elem := ((s.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
        let old := s.readVReg128 rd
        let clearMask := ~~~(mask <<< (dstIdx * esize))
        let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
        (s.writeVReg128 rd res).advancePC
      else if !op && imm4 == 0b0111#4 && ((q && esize == 64) || (!q && esize < 64)) then
        let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
        let w : Width := if q then .W64 else .W32
        (s.writeReg w (Reg.fromZRBits rd) elem).advancePC
      else if !op && imm4 == 0b0101#4 && ((q && esize < 64) || (!q && esize < 32)) then
        -- SMOV Wd/Xd, Vn.<B|H|S>[index]: sign-extend lane to 32-bit (`Q = 0`) or 64-bit (`Q = 1`).
        let elem := (getSimdLane (s.readVReg128 rn) esize dstIdx).truncate 64
        let signExt :=
          if elem.getLsbD (esize - 1) then elem ||| ~~~((1#64 <<< esize) - 1#64) else elem
        let w : Width := if q then .W64 else .W32
        (s.writeReg w (Reg.fromZRBits rd) signExt).advancePC
      else if q && op then
        let srcIdx : Nat :=
          if esize == 8 then imm4.toNat
          else if esize == 16 then imm4.toNat >>> 1
          else if esize == 32 then imm4.toNat >>> 2
          else imm4.toNat >>> 3
        let elem := getSimdLane (s.readVReg128 rn) esize srcIdx
        let old := s.readVReg128 rd
        let clearMask := ~~~(mask <<< (dstIdx * esize))
        let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
        (s.writeVReg128 rd res).advancePC
      else
        { s with status := .Exception (toString "unsupported AdvSIMD: simdInsDup (q=" ++ toString (if q then 1 else 0) ++ toString " op=" ++ toString (if op then 1 else 0) ++ toString " imm5=" ++ toString (imm5.toNat) ++ toString " imm4=" ++ toString (imm4.toNat) ++ toString ") — architecturally UNDEFINED" : String) }

  | .simdThreeSame q u size rm opcode rn rd =>
    let vn := s.readVReg128 rn
    let vm := s.readVReg128 rm
    let esize := 8 <<< size.toNat
    let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
    let truncQ (v : BitVec 128) : BitVec 128 := if q then v else (v.truncate 64).zeroExtend 128
    if opcode == 0b00011#5 then
      match u, size with
      | false, 0b00#2 => (s.writeVReg128 rd (truncQ (vn &&& vm))).advancePC
      | false, 0b01#2 => (s.writeVReg128 rd (truncQ (vn &&& ~~~vm))).advancePC
      | false, 0b10#2 => (s.writeVReg128 rd (truncQ (vn ||| vm))).advancePC
      | false, 0b11#2 => (s.writeVReg128 rd (truncQ (vn ||| ~~~vm))).advancePC
      | true,  0b00#2 => (s.writeVReg128 rd (truncQ (vn ^^^ vm))).advancePC
      | true,  0b01#2 => (s.writeVReg128 rd (truncQ (((vn ^^^ vm) &&& s.readVReg128 rd) ^^^ vm))).advancePC
      | _, _ =>
        applySimdSatResult s rd
          (evalSimdThreeSameExt q u size opcode (s.readVReg128 rd) vn vm)
          (evalSimdThreeSameExtSatFlags q u size opcode vn vm)
    else if size == 0b11#2 && !q then
      applySimdSatResult s rd
        (evalSimdThreeSameExt q u size opcode (s.readVReg128 rd) vn vm)
        (evalSimdThreeSameExtSatFlags q u size opcode vn vm)
    else if opcode == 0b10000#5 then
      let res := zipSimdLanes q esize vn vm (fun a b => if u then a - b else a + b)
      (s.writeVReg128 rd res).advancePC
    else if opcode == 0b10001#5 then
      let res := zipSimdLanes q esize vn vm (fun a b =>
        let cond := if u then a == b else (a &&& b) != 0#128
        if cond then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if opcode == 0b00111#5 then
      let res := zipSimdLanes q esize vn vm (fun a b =>
        let cond :=
          if u then BitVec.ule b a
          else
            let signBit := 1#128 <<< (esize - 1)
            BitVec.ule (b ^^^ signBit) (a ^^^ signBit)
        if cond then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if opcode == 0b00110#5 then
      let res := zipSimdLanes q esize vn vm (fun a b =>
        let cond :=
          if u then BitVec.ult b a
          else
            let signBit := 1#128 <<< (esize - 1)
            BitVec.ult (b ^^^ signBit) (a ^^^ signBit)
        if cond then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if opcode == 0b01000#5 then
      let res := zipSimdLanes q esize vn vm (fun a b =>
        let shByte : BitVec 8 := b.truncate 8
        let shInt : Int := shByte.toInt
        if shInt >= 0 then
          let amt := shInt.toNat
          if amt >= esize then 0#128 else (a <<< amt) &&& laneMask
        else
          let amt := (-shInt).toNat
          if u || !a.getLsbD (esize - 1) then
            if amt >= esize then 0#128 else a >>> amt
          else
            if amt >= esize then laneMask
            else ((a >>> amt) ||| (laneMask <<< (esize - amt))) &&& laneMask)
      (s.writeVReg128 rd res).advancePC
    else if !u && opcode == 0b10111#5 then
      -- ADDP (vector): lane `i` = sum of pair `i` of the concatenation `Vm:Vn` (`Vn` low).
      let elems := (if q then 128 else 64) / esize
      let half := elems / 2
      let pairLane (i : Nat) : BitVec 128 :=
        let src := if i < half then vn else vm
        let j := if i < half then i else i - half
        (getSimdLane src esize (2 * j) + getSimdLane src esize (2 * j + 1)) &&& laneMask
      let res : BitVec 128 := Id.run do
        let mut acc : BitVec 128 := 0#128
        for i in [0:elems] do
          acc := acc ||| (pairLane i <<< (i * esize))
        return acc
      (s.writeVReg128 rd res).advancePC
    else
      applySimdSatResult s rd
        (evalSimdThreeSameExt q u size opcode (s.readVReg128 rd) vn vm)
        (evalSimdThreeSameExtSatFlags q u size opcode vn vm)

  | .simdTwoRegMisc q u size opcode rn rd =>
    let vn := s.readVReg128 rn
    let esize := 8 <<< size.toNat
    let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
    if !u && opcode == 0b00000#5 && size != 0b11#2 then
      -- REV64: reverse `esize`-bit elements within each 64-bit doubleword (container_size = 64 > esize)
      let subLanes := 64 / esize
      let revDword (d : BitVec 64) : BitVec 64 := Id.run do
        let mut acc : BitVec 64 := 0#64
        let m64 : BitVec 64 := (1#64 <<< esize) - 1#64
        for i in [0:subLanes] do
          let elem := (d >>> (i * esize)) &&& m64
          acc := acc ||| (elem <<< ((subLanes - 1 - i) * esize))
        return acc
      let lo := revDword (vn.truncate 64)
      let hi := if q then revDword (vn.extractLsb' 64 64) else 0#64
      (s.writeVReg128 rd (hi ++ lo)).advancePC
    else if u && opcode == 0b00000#5 && size.toNat < 2 then
      -- REV32: reverse `esize`-bit elements within each 32-bit word (container_size = 32 > esize)
      let subLanes := 32 / esize
      let revWord (w : BitVec 32) : BitVec 32 := Id.run do
        let mut acc : BitVec 32 := 0#32
        let m32 : BitVec 64 := (1#64 <<< esize) - 1#64
        for i in [0:subLanes] do
          let elem := (w >>> (i * esize)) &&& (m32.truncate 32)
          acc := acc ||| (elem <<< ((subLanes - 1 - i) * esize))
        return acc
      let w0 := revWord (vn.extractLsb' 0 32)
      let w1 := revWord (vn.extractLsb' 32 32)
      let w2 := if q then revWord (vn.extractLsb' 64 32) else 0#32
      let w3 := if q then revWord (vn.extractLsb' 96 32) else 0#32
      (s.writeVReg128 rd (w3 ++ w2 ++ w1 ++ w0)).advancePC
    else if !u && opcode == 0b01000#5 && !(size == 0b11#2 && !q) then
      -- CMGT Vd.<T>, Vn.<T>, #0
      let res := mapSimdLanes q esize vn (fun a => if !a.getLsbD (esize - 1) && a != 0#128 then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if u && opcode == 0b01000#5 && !(size == 0b11#2 && !q) then
      -- CMGE Vd.<T>, Vn.<T>, #0
      let res := mapSimdLanes q esize vn (fun a => if !a.getLsbD (esize - 1) then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if !u && opcode == 0b01001#5 && !(size == 0b11#2 && !q) then
      -- CMEQ Vd.<T>, Vn.<T>, #0
      let res := mapSimdLanes q esize vn (fun a => if a == 0#128 then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if u && opcode == 0b01001#5 && !(size == 0b11#2 && !q) then
      -- CMLE Vd.<T>, Vn.<T>, #0
      let res := mapSimdLanes q esize vn (fun a => if a.getLsbD (esize - 1) || a == 0#128 then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if !u && opcode == 0b01010#5 && !(size == 0b11#2 && !q) then
      -- CMLT Vd.<T>, Vn.<T>, #0 (check sign bit of each `esize`-bit lane)
      let res := mapSimdLanes q esize vn (fun a => if a.getLsbD (esize - 1) then laneMask else 0#128)
      (s.writeVReg128 rd res).advancePC
    else if u && opcode == 0b00101#5 && size == 0b00#2 then
      -- MVN / NOT (size == '00'; size == '01' is RBIT, size == '1x' is UNDEFINED)
      let raw := ~~~vn
      let res := if q then raw else (raw.truncate 64).zeroExtend 128
      (s.writeVReg128 rd res).advancePC
    else if !u && opcode == 0b00101#5 && size == 0b00#2 then
      -- CNT Vd.<8B|16B>, Vn.<8B|16B>: population count of each byte.
      let res := mapSimdLanes q 8 vn (fun a =>
        BitVec.ofNat 128 ((List.range 8).countP (fun i => a.getLsbD i)))
      (s.writeVReg128 rd res).advancePC
    else
      let vd := s.readVReg128 rd
      applySimdSatResult s rd
        (evalSimdTwoRegMiscExt q u size opcode vd vn)
        (evalSimdTwoRegMiscExtSatFlags q u size opcode vd vn)

  | .simdAcrossLanes q u size opcode rn rd =>
    let vn := s.readVReg128 rn
    let esize := 8 <<< size.toNat
    let numLanes := (if q then 128 else 64) / esize
    let mask : BitVec 128 := (1#128 <<< esize) - 1#128
    if u && opcode == 0b01010#5 && !(size == 0b10#2 && !q) && size != 0b11#2 then
      -- UMAXV (size::Q == '100' and size == '11' are UNDEFINED)
      let maxVal : BitVec 128 := Id.run do
        let mut cur : BitVec 128 := 0#128
        for i in [0:numLanes] do
          let lane := (vn >>> (i * esize)) &&& mask
          if BitVec.ult cur lane then
            cur := lane
        return cur
      (s.writeVReg128 rd maxVal).advancePC
    else if opcode == 0b01100#5 || opcode == 0b11100#5 || opcode == 0b01111#5 || opcode == 0b11111#5 then
      let mnem :=
        if opcode == 0b01100#5 then (if size.getLsbD 1 then "FMINNMV" else "FMAXNMV")
        else if opcode == 0b01111#5 then (if size.getLsbD 1 then "FMINV" else "FMAXV")
        else "vector-FP across-lanes"
      { s with status := .Exception (toString "unsupported AdvSIMD: simdAcrossLanes vector-FP " ++ toString (mnem) ++ toString " (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — vector FP not modeled in Arm64/Trusted/ISA" : String) }
    else if (size == 0b10#2 && !q) || size == 0b11#2 then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdAcrossLanes (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED" : String) }
    else if opcode == 0b00011#5 || (!u && opcode == 0b11011#5) then
      -- UADDLV / SADDLV (`00011`, result width `2*esize`) and ADDV (`u = 0`, `11011`, width `esize`).
      let long := opcode == 0b00011#5
      let outBits := if long then 2 * esize else esize
      let outMask : BitVec 128 := (1#128 <<< outBits) - 1#128
      let signBit : BitVec 128 := 1#128 <<< (esize - 1)
      let total : BitVec 128 := Id.run do
        let mut acc : BitVec 128 := 0#128
        for i in [0:numLanes] do
          let lane := (vn >>> (i * esize)) &&& mask
          let ext := if long && !u && (lane &&& signBit) != 0#128 then lane ||| ~~~mask else lane
          acc := acc + ext
        return acc
      (s.writeVReg128 rd (total &&& outMask)).advancePC
    else if opcode == 0b01010#5 || opcode == 0b11010#5 then
      -- SMAXV (`u = 0`, `01010`), UMINV / SMINV (`11010`); UMAXV is handled above.
      let isMin := opcode == 0b11010#5
      let signBit : BitVec 128 := 1#128 <<< (esize - 1)
      let key (x : BitVec 128) : BitVec 128 := if u then x else x ^^^ signBit
      let best : BitVec 128 := Id.run do
        let mut cur : BitVec 128 := vn &&& mask
        for i in [1:numLanes] do
          let lane := (vn >>> (i * esize)) &&& mask
          let better := if isMin then BitVec.ult (key lane) (key cur) else BitVec.ult (key cur) (key lane)
          if better then
            cur := lane
        return cur
      (s.writeVReg128 rd best).advancePC
    else
      { s with status := .Exception (toString "unsupported AdvSIMD: simdAcrossLanes (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED" : String) }

  | .simdPermute q size rm opcode rn rd =>
    if (opcode == 0b001#3 || opcode == 0b101#3 || opcode == 0b011#3 || opcode == 0b111#3) && !(size == 0b11#2 && !q) then
      let vn := s.readVReg128 rn
      let vm := s.readVReg128 rm
      let esize := 8 <<< size.toNat
      let numLanes := (if q then 128 else 64) / esize
      let halfLanes := numLanes / 2
      let res : BitVec 128 := Id.run do
        let mut acc : BitVec 128 := 0#128
        if opcode == 0b001#3 then
          -- UZP1
          for i in [0:halfLanes] do
            let e0 := getSimdLane vn esize (2 * i)
            let e1 := getSimdLane vm esize (2 * i)
            acc := acc ||| (e0 <<< (i * esize))
            acc := acc ||| (e1 <<< ((halfLanes + i) * esize))
        else if opcode == 0b101#3 then
          -- UZP2
          for i in [0:halfLanes] do
            let e0 := getSimdLane vn esize (2 * i + 1)
            let e1 := getSimdLane vm esize (2 * i + 1)
            acc := acc ||| (e0 <<< (i * esize))
            acc := acc ||| (e1 <<< ((halfLanes + i) * esize))
        else if opcode == 0b011#3 then
          -- ZIP1
          for i in [0:halfLanes] do
            let e0 := getSimdLane vn esize i
            let e1 := getSimdLane vm esize i
            acc := acc ||| (e0 <<< ((2 * i) * esize))
            acc := acc ||| (e1 <<< ((2 * i + 1) * esize))
        else
          -- ZIP2
          for i in [0:halfLanes] do
            let e0 := getSimdLane vn esize (halfLanes + i)
            let e1 := getSimdLane vm esize (halfLanes + i)
            acc := acc ||| (e0 <<< ((2 * i) * esize))
            acc := acc ||| (e1 <<< ((2 * i + 1) * esize))
        return acc
      (s.writeVReg128 rd res).advancePC
    else if (opcode == 0b010#3 || opcode == 0b110#3) && !(size == 0b11#2 && !q) then
      -- TRN1 (`010`, part = 0) / TRN2 (`110`, part = 1):
      -- `Vd[2p] = Vn[2p + part]`, `Vd[2p + 1] = Vm[2p + part]`.
      let vn := s.readVReg128 rn
      let vm := s.readVReg128 rm
      let esize := 8 <<< size.toNat
      let pairs := ((if q then 128 else 64) / esize) / 2
      let part := if opcode == 0b110#3 then 1 else 0
      let res : BitVec 128 := Id.run do
        let mut acc : BitVec 128 := 0#128
        for p in [0:pairs] do
          acc := acc ||| (getSimdLane vn esize (2 * p + part) <<< ((2 * p) * esize))
          acc := acc ||| (getSimdLane vm esize (2 * p + part) <<< ((2 * p + 1) * esize))
        return acc
      (s.writeVReg128 rd res).advancePC
    else
      { s with status := .Exception (toString "unsupported AdvSIMD: simdPermute (q=" ++ toString (if q then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED" : String) }

  | .simdExt q rm imm4 rn rd =>
    if !q && imm4.getLsbD 3 then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdExt (q=0 imm4=" ++ toString (imm4.toNat) ++ toString ") — architecturally UNDEFINED" : String) }
    else
      let vn := s.readVReg128 rn
      let vm := s.readVReg128 rm
      let idx := imm4.toNat
      if q then
        let pair256 : BitVec 256 := vm ++ vn
        let res128 : BitVec 128 := (pair256 >>> (idx * 8)).truncate 128
        (s.writeVReg128 rd res128).advancePC
      else
        let pair128 : BitVec 128 := (vm.truncate 64) ++ (vn.truncate 64)
        let res64 : BitVec 64 := (pair128 >>> (idx * 8)).truncate 64
        (s.writeVReg64 rd res64).advancePC

  | .fpDataProc1 ftype opcode rn rd =>
    if opcode == 0b000000#6 then
      if ftype == 0b00#2 then
        (s.writeVReg32 rd (s.readVReg32 rn)).advancePC
      else if ftype == 0b01#2 then
        (s.writeVReg64 rd (s.readVReg64 rn)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc1 (ftype=" ++ toString (ftype.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if ftype == 0b00#2 && opcode == 0b000101#6 then
      let x := s.readVReg32 rn
      ((s.writeVReg64 rd (evalFpCvt32To64 x)).orFpsr (evalFpCvt32To64Flags x)).advancePC
    else if ftype == 0b01#2 && opcode == 0b000100#6 then
      let x := s.readVReg64 rn
      ((s.writeVReg32 rd (evalFpCvt64To32 x)).orFpsr (evalFpCvt64To32Flags x)).advancePC
    else if opcode == 0b000001#6 || opcode == 0b000010#6 then
      if ftype == 0b00#2 then
        (s.writeVReg32 rd (evalFp1Op32 opcode (s.readVReg32 rn))).advancePC
      else if ftype == 0b01#2 then
        (s.writeVReg64 rd (evalFp1Op64 opcode (s.readVReg64 rn))).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc1 (ftype=" ++ toString (ftype.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else if opcode == 0b000011#6 ||
        (opcode >= 0b001000#6 && opcode <= 0b001111#6 && opcode != 0b001101#6) then
      if ftype == 0b00#2 then
        let x := s.readVReg32 rn
        ((s.writeVReg32 rd (evalFp1Op32 opcode x)).orFpsr (evalFp1OpFlags32 opcode x)).advancePC
      else if ftype == 0b01#2 then
        let x := s.readVReg64 rn
        ((s.writeVReg64 rd (evalFp1Op64 opcode x)).orFpsr (evalFp1OpFlags64 opcode x)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc1 (ftype=" ++ toString (ftype.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc1 (ftype=" ++ toString (ftype.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16/BF16/FRINT32/64 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }

  | .fpDataProc2 ftype rm opcode rn rd =>
    if opcode <= 0b1000#4 then
      if ftype == 0b00#2 then
        let vn := s.readVReg32 rn
        let vm := s.readVReg32 rm
        ((s.writeVReg32 rd (evalFp2Op32 opcode vn vm)).orFpsr (evalFp2OpFlags32 opcode vn vm)).advancePC
      else if ftype == 0b01#2 then
        let vn := s.readVReg64 rn
        let vm := s.readVReg64 rm
        ((s.writeVReg64 rd (evalFp2Op64 opcode vn vm)).orFpsr (evalFp2OpFlags64 opcode vn vm)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc2 (ftype=" ++ toString (ftype.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc2 (ftype=" ++ toString (ftype.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED" : String) }

  | .fpCompare ftype rm op rn opcode2 =>
    if op == 0b00#2 && (opcode2 == 0b00000#5 || opcode2 == 0b01000#5 || opcode2 == 0b10000#5 || opcode2 == 0b11000#5) then
      let withZero := opcode2.getLsbD 3
      let signalNaN := opcode2.getLsbD 4
      if ftype == 0b00#2 then
        let lhs := s.readVReg32 rn
        let rhs := if withZero then 0#32 else s.readVReg32 rm
        ((s.setPState (evalFpCmp32 signalNaN lhs rhs)).orFpsr (evalFpCmpFlags32 signalNaN lhs rhs)).advancePC
      else if ftype == 0b01#2 then
        let lhs := s.readVReg64 rn
        let rhs := if withZero then 0#64 else s.readVReg64 rm
        ((s.setPState (evalFpCmp64 signalNaN lhs rhs)).orFpsr (evalFpCmpFlags64 signalNaN lhs rhs)).advancePC
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fpCompare (ftype=" ++ toString (ftype.toNat) ++ toString " op=" ++ toString (op.toNat) ++ toString " opcode2=" ++ toString (opcode2.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpCompare (ftype=" ++ toString (ftype.toNat) ++ toString " op=" ++ toString (op.toNat) ++ toString " opcode2=" ++ toString (opcode2.toNat) ++ toString ") — architecturally UNDEFINED" : String) }

  | .fpImm ftype imm8 rd =>
    if ftype == 0b00#2 then
      (s.writeVReg32 rd (vfpExpandImm32 imm8)).advancePC
    else if ftype == 0b01#2 then
      (s.writeVReg64 rd (vfpExpandImm64 imm8)).advancePC
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpImm (ftype=" ++ toString (ftype.toNat) ++ toString " imm8=" ++ toString (imm8.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }

  | .fpCondCompare ftype rm cond rn op nzcv =>
    if ftype == 0b00#2 then
      let holds := ConditionHolds (CondCode.ofBits cond) s.pstate
      let lhs := s.readVReg32 rn
      let rhs := s.readVReg32 rm
      let ps := if holds then evalFpCmp32 op lhs rhs else PState.ofBits4 nzcv
      let flags := if holds then evalFpCmpFlags32 op lhs rhs else 0#32
      ((s.setPState ps).orFpsr flags).advancePC
    else if ftype == 0b01#2 then
      let holds := ConditionHolds (CondCode.ofBits cond) s.pstate
      let lhs := s.readVReg64 rn
      let rhs := s.readVReg64 rm
      let ps := if holds then evalFpCmp64 op lhs rhs else PState.ofBits4 nzcv
      let flags := if holds then evalFpCmpFlags64 op lhs rhs else 0#32
      ((s.setPState ps).orFpsr flags).advancePC
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpCondCompare (ftype=" ++ toString (ftype.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }

  | .fpCondSelect ftype rm cond rn rd =>
    let holds := ConditionHolds (CondCode.ofBits cond) s.pstate
    if ftype == 0b00#2 then
      (s.writeVReg32 rd (if holds then s.readVReg32 rn else s.readVReg32 rm)).advancePC
    else if ftype == 0b01#2 then
      (s.writeVReg64 rd (if holds then s.readVReg64 rn else s.readVReg64 rm)).advancePC
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpCondSelect (ftype=" ++ toString (ftype.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }

  | .fpDataProc3 ftype o1 rm o0 ra rn rd =>
    if ftype == 0b00#2 then
      let vn := s.readVReg32 rn
      let vm := s.readVReg32 rm
      let va := s.readVReg32 ra
      ((s.writeVReg32 rd (evalFp3Op32 o1 o0 vn vm va)).orFpsr (evalFp3OpFlags32 o1 o0 vn vm va)).advancePC
    else if ftype == 0b01#2 then
      let vn := s.readVReg64 rn
      let vm := s.readVReg64 rm
      let va := s.readVReg64 ra
      ((s.writeVReg64 rd (evalFp3Op64 o1 o0 vn vm va)).orFpsr (evalFp3OpFlags64 o1 o0 vn vm va)).advancePC
    else
      { s with status := .Exception (toString "unsupported FP/SIMD: fpDataProc3 (ftype=" ++ toString (ftype.toNat) ++ toString " o1=" ++ toString (if o1 then 1 else 0) ++ toString " o0=" ++ toString (if o0 then 1 else 0) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }

  | .fpFixedConv sf ftype rmode opcode scale rn rd =>
    if !sf && scale.toNat < 32 then
      { s with status := .Exception (toString "unsupported FP/SIMD: fpFixedConv (sf=0 scale=" ++ toString (scale.toNat) ++ toString ") — architecturally UNDEFINED" : String) }
    else
      let fbits := 64 - scale.toNat
      if rmode == 0b11#2 && (opcode == 0b000#3 || opcode == 0b001#3) then
        let unsigned := opcode == 0b001#3
        let dstReg := Reg.fromZRBits rd
        if !sf && ftype == 0b00#2 then
          let x := s.readVReg32 rn
          ((s.writeReg32 dstReg (evalFpToIntRound32_32 unsigned .RTZ fbits x)).orFpsr (evalFpToIntRoundFlags32_32 unsigned .RTZ fbits x)).advancePC
        else if sf && ftype == 0b00#2 then
          let x := s.readVReg32 rn
          ((s.writeReg64 dstReg (evalFpToIntRound64_32 unsigned .RTZ fbits x)).orFpsr (evalFpToIntRoundFlags64_32 unsigned .RTZ fbits x)).advancePC
        else if !sf && ftype == 0b01#2 then
          let x := s.readVReg64 rn
          ((s.writeReg32 dstReg (evalFpToIntRound32_64 unsigned .RTZ fbits x)).orFpsr (evalFpToIntRoundFlags32_64 unsigned .RTZ fbits x)).advancePC
        else if sf && ftype == 0b01#2 then
          let x := s.readVReg64 rn
          ((s.writeReg64 dstReg (evalFpToIntRound64_64 unsigned .RTZ fbits x)).orFpsr (evalFpToIntRoundFlags64_64 unsigned .RTZ fbits x)).advancePC
        else
          { s with status := .Exception (toString "unsupported FP/SIMD: fpFixedConv (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString " scale=" ++ toString (scale.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
      else if rmode == 0b00#2 && (opcode == 0b010#3 || opcode == 0b011#3) then
        let unsigned := opcode == 0b011#3
        let srcReg := Reg.fromZRBits rn
        if !sf && ftype == 0b00#2 then
          let x := s.readReg32 srcReg
          ((s.writeVReg32 rd (evalFixedToFp32_32 unsigned fbits x)).orFpsr (evalFixedToFpFlags32_32 unsigned fbits x)).advancePC
        else if sf && ftype == 0b00#2 then
          let x := s.readReg64 srcReg
          ((s.writeVReg32 rd (evalFixedToFp32_64 unsigned fbits x)).orFpsr (evalFixedToFpFlags32_64 unsigned fbits x)).advancePC
        else if !sf && ftype == 0b01#2 then
          let x := s.readReg32 srcReg
          ((s.writeVReg64 rd (evalFixedToFp64_32 unsigned fbits x)).orFpsr (evalFixedToFpFlags64_32 unsigned fbits x)).advancePC
        else if sf && ftype == 0b01#2 then
          let x := s.readReg64 srcReg
          ((s.writeVReg64 rd (evalFixedToFp64_64 unsigned fbits x)).orFpsr (evalFixedToFpFlags64_64 unsigned fbits x)).advancePC
        else
          { s with status := .Exception (toString "unsupported FP/SIMD: fpFixedConv (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString " scale=" ++ toString (scale.toNat) ++ toString ") — FP16 or architecturally UNDEFINED not modeled in Arm64/Trusted/ISA" : String) }
      else
        { s with status := .Exception (toString "unsupported FP/SIMD: fpFixedConv (sf=" ++ toString (if sf then 1 else 0) ++ toString " ftype=" ++ toString (ftype.toNat) ++ toString " rmode=" ++ toString (rmode.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString " scale=" ++ toString (scale.toNat) ++ toString ") — architecturally UNDEFINED" : String) }

  -- ===== Sequential atomics (single-threaded model; see `Arm64/Trusted/ISA/README.md`) =====

  -- Load-Exclusive pair: plain aligned pair load (no exclusive monitor).
  | .ldxp sz _acq rn rt rt2 =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
      if (ea &&& (step + step - 1#64)) != 0#64 then
        s.setStatus (.Exception "alignment fault")
      else if !s.mem.canRead ea (2 * sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let v1 := s.mem.readSized sz false ea
        let v2 := s.mem.readSized sz false (ea + step)
        ((s.writeReg w rt v1).writeReg w rt2 v2).advancePC

  -- Store-Exclusive pair (`STXP` / `STLXP`): spurious hardware failures are drawn from `s.exclFails`
  -- (`s.exclWillFail`, consumed via `s.stepExclOracle`). On failure, memory is unchanged and
  -- `Ws := 1`; on success, the pair is stored and `Ws := 0`.
  | .stxp sz _rel rs rn rt rt2 =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
      if (ea &&& (step + step - 1#64)) != 0#64 then
        s.setStatus (.Exception "alignment fault")
      else if !s.mem.canWrite ea (2 * sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
        if s.exclWillFail then
          ((s.stepExclOracle).writeReg .W32 rs 1#64).advancePC
        else
          let m1 := s.mem.writeSized sz ea (s.readReg64 rt)
          let m2 := m1.writeSized sz (ea + step) (s.readReg64 rt2)
          (((s.stepExclOracle).setMem m2).writeReg .W32 rs 0#64).advancePC

  -- Compare-and-swap: `old := mem[ea]`; if `old == rs<size>` then `mem[ea] := rt`; `rs := old`.
  -- Read and write permission are both required up front, even if the compare fails: per the ASL,
  -- `CreateAccDescAtomicOp` sets `accdesc.write = TRUE` and `MemAtomic` translates (and aborts on
  -- a fault) before comparing. Not writing back on a failed compare is an allowed
  -- `Unpredictable_WRITEFAILEDCAS` choice.
  | .cas sz _acq _rel rs rn rt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if !(s.mem.canRead ea sz.bytes && s.mem.canWrite ea sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let old := s.mem.readSized sz false ea
        let rsv := s.readReg64 rs
        let expected : BitVec 64 :=
          match sz with
          | .B8 => (rsv.truncate 8).zeroExtend 64
          | .H16 => (rsv.truncate 16).zeroExtend 64
          | .W32 => (rsv.truncate 32).zeroExtend 64
          | .X64 => rsv
        let s1 := if old == expected then s.setMem (s.mem.writeSized sz ea (s.readReg64 rt)) else s
        (s1.writeReg w rs old).advancePC

  -- Compare-and-swap pair (little-endian: `rs`/`rt` at `ea`, `rs2`/`rt2` at `ea + size`).
  | .casp sz _acq _rel rs rs2 rn rt rt2 =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
      if (ea &&& (step + step - 1#64)) != 0#64 then
        s.setStatus (.Exception "alignment fault")
      else if !(s.mem.canRead ea (2 * sz.bytes) && s.mem.canWrite ea (2 * sz.bytes)) then
        s.setStatus (.Exception "permission fault")
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let old1 := s.mem.readSized sz false ea
        let old2 := s.mem.readSized sz false (ea + step)
        let cmp := old1 == (s.readReg w rs) && old2 == (s.readReg w rs2)
        let s1 :=
          if cmp then
            s.setMem ((s.mem.writeSized sz ea (s.readReg64 rt)).writeSized sz (ea + step) (s.readReg64 rt2))
          else s
        ((s1.writeReg w rs old1).writeReg w rs2 old2).advancePC

  -- LSE atomic RMW / SWP: `old := mem[ea]`; `mem[ea] := op(old, rs)`; `rt := old`.
  | .atomicRmw op sz _acq _rel rs rn rt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if !(s.mem.canRead ea sz.bytes && s.mem.canWrite ea sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let old := s.mem.readSized sz false ea
        let new := evalAtomicOp op sz old (s.readReg64 rs)
        ((s.setMem (s.mem.writeSized sz ea new)).writeReg w rt old).advancePC

  -- Load-Acquire RCpc (`LDAPR*`): sequentially identical to `LDAR*` (naturally aligned load).
  | .ldapr sz rn rt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if !s.mem.canRead ea sz.bytes then
        s.setStatus (.Exception "permission fault")
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        (s.writeReg w rt (s.mem.readSized sz false ea)).advancePC

  -- RCpc unscaled `STLUR*` / `LDAPUR*` / `LDAPURS*`. The model requires natural alignment
  -- (a conservative under-approximation of `FEAT_LSE2` unaligned single-copy-atomic accesses).
  | .ldapurStlur sz opc rn rt offset =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn + offset
      if !sz.isAligned ea then
        s.setStatus (.Exception "alignment fault")
      else if opc == 0#2 then
        if !s.mem.canWrite ea sz.bytes then
          s.setStatus (.Exception "permission fault")
        else
          (s.setMem (s.mem.writeSized sz ea (s.readReg64 rt))).advancePC
      else if !s.mem.canRead ea sz.bytes then
        s.setStatus (.Exception "permission fault")
      else if opc == 1#2 then
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        (s.writeReg w rt (s.mem.readSized sz false ea)).advancePC
      else if opc == 2#2 then
        (s.writeReg .W64 rt (s.mem.readSized sz true ea)).advancePC
      else
        (s.writeReg .W32 rt (s.mem.readSized sz true ea)).advancePC

  -- Hint space (`YIELD`, `WFE`, `WFI`, `SEV`, `SEVL`, `PACIASP`, `AUTIASP`, `BTI`, ...): no-op.
  | .hint _imm =>
    s.advancePC

  -- Prefetch: no architectural effect (ASL `Prefetch` is a hint with no `CheckSPAlignment`).
  | .prfm _prfop _addr =>
    s.advancePC
  | .prfmLit _prfop _offset =>
    s.advancePC

  -- SIMD/FP PC-relative literal load.
  | .ldrSimdLit sz vt offset =>
    let ea := s.pc + offset
    if !s.mem.canRead ea sz.bytes then
      s.setStatus (.Exception "permission fault")
    else
      (s.writeVReg128 vt (s.mem.readSimdSized sz ea)).advancePC

  -- Non-temporal pairs: sequentially identical to signed-offset `LDP` / `STP`.
  | .ldnp sz rn rt rt2 offset =>
    execLdp (match sz with | .X64 => .W64 | _ => .W32) false rt rt2 (.Offset rn offset) s
  | .stnp sz rn rt rt2 offset =>
    execStp (match sz with | .X64 => .W64 | _ => .W32) rt rt2 (.Offset rn offset) s
  | .ldnpSimd sz vt1 vt2 rn offset =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn + offset
      let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
      if !(s.mem.canRead ea sz.bytes && s.mem.canRead (ea + step) sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
        let v1 := s.mem.readSimdSized sz ea
        let v2 := s.mem.readSimdSized sz (ea + step)
        ((s.writeVReg128 vt1 v1).writeVReg128 vt2 v2).advancePC
  | .stnpSimd sz vt1 vt2 rn offset =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let ea := s.readReg64 rn + offset
      let step : BitVec 64 := BitVec.ofNat 64 sz.bytes
      if !(s.mem.canWrite ea sz.bytes && s.mem.canWrite (ea + step) sz.bytes) then
        s.setStatus (.Exception "permission fault")
      else
        let m1 := s.mem.writeSimdSized sz ea (s.readVReg128 vt1)
        let m2 := m1.writeSimdSized sz (ea + step) (s.readVReg128 vt2)
        (s.setMem m2).advancePC

  -- Hardware CRC32 / CRC32C.
  | .crc32 c sz rd rn rm =>
    (s.writeReg32 rd (evalCrc32 c sz (s.readReg32 rn) (s.readReg64 rm))).advancePC

  -- SIMD table lookup `TBL` / `TBX` over `len + 1` consecutive table registers (mod 32).
  | .simdTbl q rm len isTbx rn rd =>
    let nTbl := len.toNat + 1
    let tblByte (i : Nat) : BitVec 128 :=
      ((s.readVReg128 (rn + BitVec.ofNat 5 (i / 16))) >>> ((i % 16) * 8)) &&& 0xff#128
    let idxV := s.readVReg128 rm
    let vd := s.readVReg128 rd
    let elems := if q then 16 else 8
    let res : BitVec 128 := Id.run do
      let mut acc : BitVec 128 := 0#128
      for i in [0:elems] do
        let idx := ((idxV >>> (i * 8)) &&& 0xff#128).toNat
        let b : BitVec 128 :=
          if idx < 16 * nTbl then tblByte idx
          else if isTbx then (vd >>> (i * 8)) &&& 0xff#128 else 0#128
        acc := acc ||| (b <<< (i * 8))
      return acc
    (s.writeVReg128 rd res).advancePC

  -- Scalar pairwise `ADDP Dd, Vn.2D`.
  | .simdAddpScalar rn rd =>
    let vn := s.readVReg128 rn
    (s.writeVReg64 rd (vn.extractLsb' 0 64 + vn.extractLsb' 64 64)).advancePC

  -- Scalar duplicate element `DUP <V><d>, <Vn>.<T>[<index>]`.
  | .simdDupScalar imm5 rn rd =>
    if imm5.extractLsb' 0 4 == 0#4 then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdDupScalar (imm5=" ++ toString (imm5.toNat) ++ toString ") — architecturally UNDEFINED" : String) }
    else
      (s.writeVReg128 rd (evalSimdDupScalar imm5 (s.readVReg128 rn))).advancePC

  -- `LD1` / `ST1` (single-structure lane transfer, no-offset or post-indexed).
  | .simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt =>
    if !validSimdLdSt1Single opcode sBit size then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdLdSt1Single (isLoad=" ++ toString (if isLoad then 1 else 0) ++ toString " q=" ++ toString (if q then 1 else 0) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString " S=" ++ toString (if sBit then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString ") — architecturally UNDEFINED" : String) }
    else if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let msz : MemWidth :=
        let opcHi := opcode.extractLsb' 1 2
        if opcHi == 0#2 then .B8
        else if opcHi == 1#2 then .H16
        else if size.extractLsb' 0 1 == 0#1 then .W32
        else .X64
      let idx := simdLdSt1SingleLaneIdx q opcode sBit size
      let ea := s.readReg64 rn
      let inc := if rm == 31#5 then BitVec.ofNat 64 msz.bytes else s.readReg64 (Reg.fromZRBits rm)
      if isLoad then
        if !s.mem.canRead ea msz.bytes then
          s.setStatus (.Exception "permission fault")
        else
          let elem := (s.mem.readSized msz false ea).zeroExtend 128
          let v' := setSimdLane (s.readVReg128 vt) (msz.bytes * 8) idx elem
          let s1 := s.writeVReg128 vt v'
          if postIdx then (s1.writeReg64 rn (ea + inc)).advancePC else s1.advancePC
      else
        if !s.mem.canWrite ea msz.bytes then
          s.setStatus (.Exception "permission fault")
        else
          let lane := (getSimdLane (s.readVReg128 vt) (msz.bytes * 8) idx).truncate 64
          let s1 := s.setMem (s.mem.writeSized msz ea lane)
          if postIdx then (s1.writeReg64 rn (ea + inc)).advancePC else s1.advancePC

  -- `LD1` / `ST1` (multiple structures, 1–4 registers): contiguous transfer of `nregs` whole
  -- registers (little-endian element order equals byte order, so `size` does not affect layout).
  | .simdLdSt1Multi isLoad q _size nregs rn postIdx rm vt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let sz := SimdMemSize.ofQ q
      let ea := s.readReg64 rn
      let total := nregs * sz.bytes
      let finish (s' : State) : State :=
        if postIdx then
          let inc := if rm == 31#5 then BitVec.ofNat 64 total else s.readReg64 (Reg.fromZRBits rm)
          (s'.writeReg64 rn (ea + inc)).advancePC
        else s'.advancePC
      if isLoad then
        if !s.mem.canRead ea total then
          s.setStatus (.Exception "permission fault")
        else finish (simdLoadRegs sz s.mem nregs vt ea s)
      else
        if !s.mem.canWrite ea total then
          s.setStatus (.Exception "permission fault")
        else finish (s.setMem (simdStoreRegs sz s.readVReg128 nregs vt ea s.mem))

  -- `LD2`–`LD4` / `ST2`–`ST4` (multiple structures, `selem ∈ {2, 3, 4}` interleaved registers).
  | .simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    if (size == 3#2 && !q) || !(selem == 2 || selem == 3 || selem == 4) then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdLdStMulti (isLoad=" ++ toString (if isLoad then 1 else 0) ++ toString " q=" ++ toString (if q then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " selem=" ++ toString (selem) ++ toString ") — architecturally UNDEFINED" : String) }
    else if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let sz := SimdMemSize.ofQ q
      let ea := s.readReg64 rn
      let step := BitVec.ofNat 64 sz.bytes
      let total := selem * sz.bytes
      let finish (s' : State) : State :=
        if postIdx then
          let inc := if rm == 31#5 then BitVec.ofNat 64 total else s.readReg64 (Reg.fromZRBits rm)
          (s'.writeReg64 rn (ea + inc)).advancePC
        else s'.advancePC
      if isLoad then
        if !s.mem.canRead ea total then
          s.setStatus (.Exception "permission fault")
        else
          let c0 := s.mem.readSimdSized sz ea
          let c1 := s.mem.readSimdSized sz (ea + step)
          let c2 := if selem >= 3 then s.mem.readSimdSized sz (ea + step + step) else 0#128
          let c3 := if selem >= 4 then s.mem.readSimdSized sz (ea + step + step + step) else 0#128
          let s1 := (s.writeVReg128 vt (simdDeinterleaveReg q size selem 0 c0 c1 c2 c3)).writeVReg128
            (vt + 1#5) (simdDeinterleaveReg q size selem 1 c0 c1 c2 c3)
          let s2 := if selem >= 3 then
            s1.writeVReg128 (vt + 2#5) (simdDeinterleaveReg q size selem 2 c0 c1 c2 c3)
          else s1
          let s3 := if selem >= 4 then
            s2.writeVReg128 (vt + 3#5) (simdDeinterleaveReg q size selem 3 c0 c1 c2 c3)
          else s2
          finish s3
      else
        if !s.mem.canWrite ea total then
          s.setStatus (.Exception "permission fault")
        else
          finish (s.setMem (simdStoreRegs sz (simdInterleaveChunk q size selem vt s.readVReg128) selem vt ea s.mem))

  -- `LD1R`: load one element and replicate it to every lane.
  | .simdLd1r q size rn postIdx rm vt =>
    if !checkRegSPAligned s rn then
      s.setStatus (.Exception "SP alignment fault")
    else
      let msz := MemWidth.ofBits size
      let ea := s.readReg64 rn
      if !s.mem.canRead ea msz.bytes then
        s.setStatus (.Exception "permission fault")
      else
        let elem := (s.mem.readSized msz false ea).zeroExtend 128
        let res := mapSimdLanes q (msz.bytes * 8) 0#128 (fun _ => elem)
        let s1 := s.writeVReg128 vt res
        if postIdx then
          let inc := if rm == 31#5 then BitVec.ofNat 64 msz.bytes else s.readReg64 (Reg.fromZRBits rm)
          (s1.writeReg64 rn (ea + inc)).advancePC
        else s1.advancePC

  -- `DC ZVA, Xt`: zero the 64-byte block (`DCZID_EL0.BS = 4`) containing `Xt`.
  | .dcZva rt =>
    let ea := s.readReg64 rt &&& ~~~63#64
    if !s.mem.canWrite ea 64 then
      s.setStatus (.Exception "permission fault")
    else
      (s.setMem (simdStoreRegs .Q128 (fun _ => 0#128) 4 0#5 ea s.mem)).advancePC

  -- Permanently undefined.
  | .udf _imm =>
    s.setStatus (.Exception "udf")

  -- SIMD polynomial multiply long `PMULL` / `PMULL2`.
  | .simdPmull q is64 rm rn rd =>
    (s.writeVReg128 rd (evalPmull q is64 (s.readVReg128 rn) (s.readVReg128 rm))).advancePC

  -- SIMD three-different (`SADDL`/`UADDL`, `SADDW`/`UADDW`, `SSUBL`/`USUBL`, `SSUBW`/`USUBW`,
  -- `ADDHN`/`RADDHN`, `SABAL`/`UABAL`, `SUBHN`/`RSUBHN`, `SABDL`/`UABDL`, `SMLAL`/`UMLAL`,
  -- `SMLSL`/`UMLSL`, `SMULL`/`UMULL`, and `*2` variants).
  | .simdThreeDiff q u size rm opcode rn rd =>
    if !validSimdThreeDiff size opcode then
      { s with status := .Exception (toString "unsupported AdvSIMD: simdThreeDiff (q=" ++ toString (if q then 1 else 0) ++ toString " u=" ++ toString (if u then 1 else 0) ++ toString " size=" ++ toString (size.toNat) ++ toString " opcode=" ++ toString (opcode.toNat) ++ toString ") — architecturally UNDEFINED or SQDM*" : String) }
    else
      (s.writeVReg128 rd (evalSimdThreeDiff q u size opcode (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC

  -- `FEAT_SHA1` / `FEAT_SHA256` 2-register SHA (`SHA1H`, `SHA1SU1`, `SHA256SU0`).
  | .cryptoSha2Reg opcode rn rd =>
    applySimdResult s rd (evalCryptoSha2Reg opcode (s.readVReg128 rd) (s.readVReg128 rn))

  -- `FEAT_SHA1` / `FEAT_SHA256` 3-register SHA (`SHA1C`, `SHA1P`, `SHA1M`, `SHA1SU0`,
  -- `SHA256H`, `SHA256H2`, `SHA256SU1`).
  | .cryptoSha3Reg opcode rm rn rd =>
    applySimdResult s rd (evalCryptoSha3Reg opcode (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))

  -- `FEAT_SHA512` 2-register schedule update 0 (`SHA512SU0`).
  | .cryptoSha512Reg2 rn rd =>
    (s.writeVReg128 rd (evalCryptoSha512Reg2 (s.readVReg128 rd) (s.readVReg128 rn))).advancePC

  -- `FEAT_SHA512` / `FEAT_SHA3` 3-register (`SHA512H`, `SHA512H2`, `SHA512SU1`, `RAX1`).
  | .cryptoSha512Reg3 opcode rm rn rd =>
    (s.writeVReg128 rd (evalCryptoSha512Reg3 opcode (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC

  -- `FEAT_SHA3` 4-register bitwise (`EOR3`, `BCAX`).
  | .cryptoSha3FourReg isBcax rm ra rn rd =>
    (s.writeVReg128 rd (evalCryptoSha3FourReg isBcax (s.readVReg128 rn) (s.readVReg128 rm) (s.readVReg128 ra))).advancePC

  -- `FEAT_SHA3` Exclusive-OR and Rotate (`XAR`).
  | .cryptoXar rm imm6 rn rd =>
    (s.writeVReg128 rd (evalCryptoXar imm6 (s.readVReg128 rn) (s.readVReg128 rm))).advancePC

end Arm64


