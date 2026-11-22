-- Prove2me | Definitions.Def_Arm64_ISA_Syntax
-- name    : Arm64_ISA_Syntax
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:01:48.985665+00:00
-- url     : https://prove2.me/theorems/b4a899aa-d4a8-44e1-9268-df2697404a53
-- title:
--   Arm64.Trusted.ISA.Syntax — AArch64 Instruction Abstract Syntax
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/Syntax.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Syntax.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/Syntax.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Syntax.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/Syntax.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

/-!
# AArch64 Instruction Abstract Syntax

Defines the AArch64 A64 instruction AST (`Instr`), register and width types (`Reg`, `VReg`,
`RegWidth`, `MemWidth`, `SimdMemSize`), addressing modes (`AddrMode`), and ASL encoding-class
operation enums, together with total bit-field decoders (`ofBits`, `fromZRBits`, `fromSPBits`).
-/

@[expose] public section

namespace Arm64

/-! ## Register widths, memory access sizes, condition codes, shifts, and extends -/

/-- Architectural general-purpose register width (`sf = 0` for 32-bit `W`, `sf = 1` for 64-bit `X`). -/
inductive RegWidth where
  | W32
  | W64
  deriving DecidableEq, Repr, Inhabited, BEq

namespace RegWidth

/-- Convert `RegWidth` to its `sf` bit (`false` for `W32`, `true` for `W64`). -/
@[inline] def toBool : RegWidth → Bool
  | .W32 => false
  | .W64 => true

/-- Decode the `sf` bit into a `RegWidth` (`false ↦ W32`, `true ↦ W64`). -/
@[inline] def ofBool (sf : Bool) : RegWidth :=
  if sf then .W64 else .W32

/-- Bit width (`32` or `64`). -/
@[inline] def bits : RegWidth → Nat
  | .W32 => 32
  | .W64 => 64

end RegWidth

/-- Alias for `RegWidth`. -/
abbrev Width := RegWidth

/-- General-purpose memory access width (`size` field `bits[31:30]`): 1, 2, 4, or 8 bytes. -/
inductive MemWidth where
  | B8
  | H16
  | W32
  | X64
  deriving DecidableEq, Repr, Inhabited, BEq

namespace MemWidth

abbrev W8  : MemWidth := .B8
abbrev W16 : MemWidth := .H16
abbrev W64 : MemWidth := .X64

/-- Byte width (`1`, `2`, `4`, or `8`) of a `MemWidth`. -/
@[simp, reducible] def bytes : MemWidth → Nat
  | .B8  => 1
  | .H16 => 2
  | .W32 => 4
  | .X64 => 8

/-- Decode a 2-bit `size` field (`00 ↦ B8`, `01 ↦ H16`, `10 ↦ W32`, `11 ↦ X64`). -/
@[inline] def ofBits (b : BitVec 2) : MemWidth :=
  match b.toNat with
  | 0 => .B8
  | 1 => .H16
  | 2 => .W32
  | _ => .X64

end MemWidth

instance : Coe RegWidth MemWidth where
  coe
    | .W32 => .W32
    | .W64 => .X64

/-- AArch64 4-bit condition code (`cond` field). -/
inductive CondCode where
  | EQ | NE | CS | CC
  | MI | PL | VS | VC
  | HI | LS | GE | LT
  | GT | LE | AL | NV
  deriving DecidableEq, Repr, Inhabited, BEq

namespace CondCode

/-- Decode a 4-bit condition code field into `CondCode`. -/
def ofBits (b : BitVec 4) : CondCode :=
  match b.toNat with
  | 0x0 => .EQ | 0x1 => .NE | 0x2 => .CS | 0x3 => .CC
  | 0x4 => .MI | 0x5 => .PL | 0x6 => .VS | 0x7 => .VC
  | 0x8 => .HI | 0x9 => .LS | 0xa => .GE | 0xb => .LT
  | 0xc => .GT | 0xd => .LE | 0xe => .AL | _   => .NV

end CondCode

/-- AArch64 bitwise shift type (`shift` 2-bit field in shifted-register instructions). -/
inductive ShiftType where
  | LSL
  | LSR
  | ASR
  | ROR
  deriving DecidableEq, Repr, Inhabited, BEq

namespace ShiftType

/-- Decode a 2-bit `shift` field (`00 ↦ LSL`, `01 ↦ LSR`, `10 ↦ ASR`, `11 ↦ ROR`). -/
@[inline] def ofBits (b : BitVec 2) : ShiftType :=
  match b.toNat with
  | 0 => .LSL
  | 1 => .LSR
  | 2 => .ASR
  | _ => .ROR

end ShiftType

/-- AArch64 register extension type (`option` 3-bit field in extended-register and register-offset instructions). -/
inductive ExtendType where
  | UXTB
  | UXTH
  | UXTW
  | UXTX
  | SXTB
  | SXTH
  | SXTW
  | SXTX
  deriving DecidableEq, Repr, Inhabited, BEq

namespace ExtendType

/-- Decode a 3-bit `option` field into `ExtendType`. -/
def ofBits (b : BitVec 3) : ExtendType :=
  match b.toNat with
  | 0 => .UXTB
  | 1 => .UXTH
  | 2 => .UXTW
  | 3 => .UXTX
  | 4 => .SXTB
  | 5 => .SXTH
  | 6 => .SXTW
  | _ => .SXTX

end ExtendType

/-! ## General-purpose and SIMD/FP registers -/

/-- General-purpose register identifier:
    - `.gpr idx` (`idx < 31`) for architectural registers `X0`..`X30` (`W0`..`W30`),
    - `.sp` when encoding `31` denotes the stack pointer `SP`/`WSP`,
    - `.xzr` when encoding `31` denotes the zero register `XZR`/`WZR`. -/
inductive Reg where
  | gpr (idx : BitVec 5)
  | sp
  | xzr
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Reg

/-- Decode a 5-bit register field where `31` denotes the zero register (`XZR`/`WZR`). -/
@[inline] def fromZRBits (b : BitVec 5) : Reg :=
  if b == 31#5 then .xzr else .gpr b

/-- Decode a 5-bit register field where `31` denotes the stack pointer (`SP`/`WSP`). -/
@[inline] def fromSPBits (b : BitVec 5) : Reg :=
  if b == 31#5 then .sp else .gpr b

abbrev x0  : Reg := .gpr 0#5
abbrev x1  : Reg := .gpr 1#5
abbrev x2  : Reg := .gpr 2#5
abbrev x3  : Reg := .gpr 3#5
abbrev x4  : Reg := .gpr 4#5
abbrev x5  : Reg := .gpr 5#5
abbrev x6  : Reg := .gpr 6#5
abbrev x7  : Reg := .gpr 7#5
abbrev x8  : Reg := .gpr 8#5
abbrev x9  : Reg := .gpr 9#5
abbrev x10 : Reg := .gpr 10#5
abbrev x11 : Reg := .gpr 11#5
abbrev x12 : Reg := .gpr 12#5
abbrev x13 : Reg := .gpr 13#5
abbrev x14 : Reg := .gpr 14#5
abbrev x15 : Reg := .gpr 15#5
abbrev x16 : Reg := .gpr 16#5
abbrev x17 : Reg := .gpr 17#5
abbrev x18 : Reg := .gpr 18#5
abbrev x19 : Reg := .gpr 19#5
abbrev x20 : Reg := .gpr 20#5
abbrev x21 : Reg := .gpr 21#5
abbrev x22 : Reg := .gpr 22#5
abbrev x23 : Reg := .gpr 23#5
abbrev x24 : Reg := .gpr 24#5
abbrev x25 : Reg := .gpr 25#5
abbrev x26 : Reg := .gpr 26#5
abbrev x27 : Reg := .gpr 27#5
abbrev x28 : Reg := .gpr 28#5
abbrev x29 : Reg := .gpr 29#5
abbrev x30 : Reg := .gpr 30#5
abbrev fp  : Reg := .gpr 29#5
abbrev lr  : Reg := .gpr 30#5

end Reg

/-- 128-bit SIMD/FP vector register index `V0`..`V31` (`Q`/`D`/`S`/`H`/`B`). -/
abbrev VReg := BitVec 5

/-- SIMD/FP scalar and vector memory transfer size (`1`, `2`, `4`, `8`, or `16` bytes). -/
inductive SimdMemSize where
  | B8
  | H16
  | S32
  | D64
  | Q128
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ## Addressing modes -/

/-- Unified AArch64 memory addressing mode used across general-purpose, SIMD/FP, and prefetch
    loads and stores:
    - `.Offset base offset`: scaled unsigned immediate (or signed pair immediate) `[base, #offset]`
    - `.UnscaledOffset base offset`: unscaled 9-bit signed immediate `[base, #simm9]` (`LDUR*`/`STUR*`)
    - `.PreIndex base offset`: pre-indexed `[base, #offset]!` (writes `base + offset` back to `base`)
    - `.PostIndex base offset`: post-indexed `[base], #offset` (writes `base + offset` back to `base`)
    - `.RegOffset base index ext amount`: register offset `[base, index, ext #amount]` -/
inductive AddrMode where
  | Offset (base : Reg) (offset : BitVec 64)
  | UnscaledOffset (base : Reg) (offset : BitVec 64)
  | PreIndex (base : Reg) (offset : BitVec 64)
  | PostIndex (base : Reg) (offset : BitVec 64)
  | RegOffset (base : Reg) (index : Reg) (ext : ExtendType) (amount : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ## ARM ASL encoding-class operation enums -/

/-- Add/subtract operation (`op` bit `30` = `isSub`, `S` bit `29` = `setFlags`). -/
inductive AddSubOp where
  | ADD
  | ADDS
  | SUB
  | SUBS
  deriving DecidableEq, Repr, Inhabited, BEq

namespace AddSubOp

/-- Decode `(isSub, setFlags)` (`bits[30], bits[29]`) into `AddSubOp`. -/
@[inline] def ofBits (isSub setFlags : Bool) : AddSubOp :=
  match isSub, setFlags with
  | false, false => .ADD
  | false, true  => .ADDS
  | true,  false => .SUB
  | true,  true  => .SUBS

/-- True when the operation updates `PSTATE.NZCV` (`ADDS`, `SUBS`) and uses `XZR`/`WZR` for `Rd = 31`. -/
@[inline] def setsFlags : AddSubOp → Bool
  | .ADDS | .SUBS => true
  | .ADD  | .SUB  => false

end AddSubOp

/-- Logical operation (`opc` `bits[30:29]` and `N` `bit[21]`). -/
inductive LogicalOp where
  | AND
  | BIC
  | ORR
  | ORN
  | EOR
  | EON
  | ANDS
  | BICS
  deriving DecidableEq, Repr, Inhabited, BEq

namespace LogicalOp

/-- Decode `(opc, nBit)` into `LogicalOp`. -/
@[inline] def ofBits (opc : BitVec 2) (nBit : Bool) : LogicalOp :=
  match opc.toNat, nBit with
  | 0, false => .AND
  | 0, true  => .BIC
  | 1, false => .ORR
  | 1, true  => .ORN
  | 2, false => .EOR
  | 2, true  => .EON
  | _, false => .ANDS
  | _, true  => .BICS

end LogicalOp

/-- Move wide (immediate) operation (`opc` `bits[30:29]`: `00 ↦ MOVN`, `10 ↦ MOVZ`, `11 ↦ MOVK`). -/
inductive MoveWideOp where
  | MOVN
  | MOVZ
  | MOVK
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Bitfield move operation (`opc` `bits[30:29]`: `00 ↦ SBFM`, `01 ↦ BFM`, `10 ↦ UBFM`). -/
inductive BitfieldOp where
  | SBFM
  | BFM
  | UBFM
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Conditional select operation (`op` `bit[30]`, `o2` `bit[10]`). -/
inductive CondSelectOp where
  | CSEL
  | CSINC
  | CSINV
  | CSNEG
  deriving DecidableEq, Repr, Inhabited, BEq

namespace CondSelectOp

/-- Decode `(opBit, o2Bit)` (`bit[30], bit[10]`) into `CondSelectOp`. -/
@[inline] def ofBits (opBit o2Bit : Bool) : CondSelectOp :=
  match opBit, o2Bit with
  | false, false => .CSEL
  | false, true  => .CSINC
  | true,  false => .CSINV
  | true,  true  => .CSNEG

end CondSelectOp

/-- Data-processing (1 source) operation (`opcode` `bits[15:10]`). -/
inductive DataProc1Op where
  | RBIT
  | REV16
  | REV32
  | REV
  | CLZ
  | CLS
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Data-processing (2 source) operation (`opcode` `bits[15:10]`). -/
inductive DataProc2Op where
  | UDIV
  | SDIV
  | LSLV
  | LSRV
  | ASRV
  | RORV
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Data-processing (3 source) multiply-accumulate and high-multiply operation. -/
inductive DataProc3Op where
  | MADD
  | MSUB
  | SMADDL
  | SMSUBL
  | UMADDL
  | UMSUBL
  | SMULH
  | UMULH
  deriving DecidableEq, Repr, Inhabited, BEq

/-- LSE (`FEAT_LSE`) atomic read-modify-write and swap operations (`LD<op>*`, `ST<op>*`, `SWP*`). -/
inductive AtomicOp where
  | ADD
  | CLR
  | EOR
  | SET
  | SMAX
  | SMIN
  | UMAX
  | UMIN
  | SWP
  deriving DecidableEq, Repr, Inhabited, BEq

namespace AtomicOp

/-- Decode the 3-bit `opc` field (`bits[14:12]`) when `o3 = 0` into `AtomicOp`. -/
def ofBits (b : BitVec 3) : AtomicOp :=
  match b.toNat with
  | 0 => .ADD
  | 1 => .CLR
  | 2 => .EOR
  | 3 => .SET
  | 4 => .SMAX
  | 5 => .SMIN
  | 6 => .UMAX
  | _ => .UMIN

end AtomicOp

/-- `FEAT_AES` cryptographic block cipher operations (`AESE`, `AESD`, `AESMC`, `AESIMC`). -/
inductive AesOp where
  | AESE
  | AESD
  | AESMC
  | AESIMC
  deriving DecidableEq, Repr, Inhabited, BEq

namespace AesOp

/-- Decode a 2-bit AES opcode (`bits[13:12]`). -/
def ofBits (b : BitVec 2) : AesOp :=
  match b.toNat with
  | 0 => .AESE
  | 1 => .AESD
  | 2 => .AESMC
  | _ => .AESIMC

end AesOp

/-! ## Decoded AArch64 instruction AST (`Instr`) -/

/-- Decoded AArch64 A64 instruction, structured by ARM ARM / ASL encoding classes. -/
inductive Instr : Type where
  -- Data processing (immediate)
  /-- PC-relative address calculation: `ADR` (`page = false`) or `ADRP` (`page = true`). -/
  | adr (page : Bool) (rd : Reg) (offset : BitVec 64)
  /-- Add/subtract (immediate): `ADD`, `ADDS`, `SUB`, `SUBS` with 12-bit unsigned immediate and optional `LSL #12` (`shift12`). -/
  | addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12) (shift12 : Bool)
  /-- Logical (immediate): `AND`, `ORR`, `EOR`, `ANDS` with decoded 64-bit `DecodeBitMasks` bitmask. -/
  | logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64)
  /-- Move wide (immediate): `MOVN`, `MOVZ`, `MOVK` with 16-bit immediate and halfword shift `hw ∈ {0, 16, 32, 48}`. -/
  | moveWide (w : RegWidth) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16) (hw : Nat)
  /-- Bitfield move: `SBFM`, `BFM`, `UBFM` with rotate `immr` and width/msb index `imms`. -/
  | bitfield (w : RegWidth) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat)
  /-- Extract register from pair: `EXTR` (`ROR` when `rn = rm`). -/
  | extr (w : RegWidth) (rd rn rm : Reg) (lsb : Nat)

  -- Branches, Exception Generation, and System Instructions
  /-- Unconditional PC-relative branch (`B label`). -/
  | b (offset : BitVec 64)
  /-- Unconditional PC-relative branch with link (`BL label`, writes `PC + 4` to `X30`). -/
  | bl (offset : BitVec 64)
  /-- Conditional PC-relative branch (`B.<cond> label`). -/
  | bCond (cond : CondCode) (offset : BitVec 64)
  /-- Compare and branch on zero (`CBZ`, `isNonZero = false`) or non-zero (`CBNZ`, `isNonZero = true`). -/
  | cbz (w : RegWidth) (isNonZero : Bool) (rt : Reg) (offset : BitVec 64)
  /-- Test bit and branch on zero (`TBZ`, `isNonZero = false`) or non-zero (`TBNZ`, `isNonZero = true`). -/
  | tbz (w : RegWidth) (isNonZero : Bool) (rt : Reg) (bit : Nat) (offset : BitVec 64)
  /-- Unconditional branch to register (`BR Xn`). -/
  | br (rn : Reg)
  /-- Unconditional branch with link to register (`BLR Xn`, writes `PC + 4` to `X30`). -/
  | blr (rn : Reg)
  /-- Subroutine return (`RET {Xn}`). -/
  | ret (rn : Reg)
  /-- Architectural no-op (`NOP`, `HINT #0`). -/
  | nop
  /-- Non-`NOP` `HINT #imm` (`YIELD`, `WFE`, `WFI`, `SEV`, `SEVL`, `PACIASP`, `AUTIASP`, `BTI`, ...). -/
  | hint (imm : BitVec 7)
  /-- Memory barrier or exclusive monitor clear (`CLREX`, `DSB`, `DMB`, `ISB`). -/
  | barrier (crm : BitVec 4) (op2 : BitVec 3)
  /-- System register move (`MRS Xt, <sysreg>` when `isRead = true`, `MSR <sysreg>, Xt` when `isRead = false`). -/
  | sysReg (isRead : Bool) (sysreg : BitVec 15) (rt : Reg)
  /-- Data cache zero by VA (`DC ZVA, Xt`). -/
  | dcZva (rt : Reg)
  /-- Exception generation: `SVC #imm16` (`isHalt = false`) or `BRK #imm16` (`isHalt = true`). -/
  | system (isHalt : Bool) (imm : BitVec 16)
  /-- Permanently undefined instruction (`UDF #imm16`). -/
  | udf (imm : BitVec 16)

  -- Data processing (register)
  /-- Logical (shifted register): `AND`, `BIC`, `ORR`, `ORN`, `EOR`, `EON`, `ANDS`, `BICS`. -/
  | logicalShift (w : RegWidth) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat)
  /-- Add/subtract (shifted register): `ADD`, `ADDS`, `SUB`, `SUBS`. -/
  | addSubShift (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat)
  /-- Add/subtract (extended register): `ADD`, `ADDS`, `SUB`, `SUBS`. -/
  | addSubExt (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType) (amount : Nat)
  /-- Add/subtract with carry: `ADC`, `ADCS`, `SBC`, `SBCS`. -/
  | addSubCarry (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg)
  /-- Conditional compare (register): `CCMN` (`isSub = false`) or `CCMP` (`isSub = true`). -/
  | condCompareReg (w : RegWidth) (isSub : Bool) (rn rm : Reg) (nzcv : BitVec 4) (cond : CondCode)
  /-- Conditional compare (immediate): `CCMN` (`isSub = false`) or `CCMP` (`isSub = true`). -/
  | condCompareImm (w : RegWidth) (isSub : Bool) (rn : Reg) (imm5 : BitVec 5) (nzcv : BitVec 4) (cond : CondCode)
  /-- Conditional select: `CSEL`, `CSINC`, `CSINV`, `CSNEG`. -/
  | condSelect (w : RegWidth) (op : CondSelectOp) (rd rn rm : Reg) (cond : CondCode)
  /-- Data-processing (1 source): `RBIT`, `REV16`, `REV32`, `REV`, `CLZ`, `CLS`. -/
  | dataProc1 (w : RegWidth) (op : DataProc1Op) (rd rn : Reg)
  /-- Data-processing (2 source): `UDIV`, `SDIV`, `LSLV`, `LSRV`, `ASRV`, `RORV`. -/
  | dataProc2 (w : RegWidth) (op : DataProc2Op) (rd rn rm : Reg)
  /-- Data-processing (3 source): `MADD`, `MSUB`, `SMADDL`, `SMSUBL`, `UMADDL`, `UMSUBL`, `SMULH`, `UMULH`. -/
  | dataProc3 (w : RegWidth) (op : DataProc3Op) (rd rn rm ra : Reg)
  /-- Hardware CRC-32 (`crc32c = false`) / CRC-32C (`crc32c = true`) over 8, 16, 32, or 64 bits (`FEAT_CRC32`). -/
  | crc32 (crc32c : Bool) (sz : MemWidth) (rd rn rm : Reg)

  -- Loads and Stores (General-Purpose)
  /-- Single-register load (`LDR`, `LDUR`, `LDRB`, `LDURB`, `LDRSB`, `LDURSB`, `LDRH`, `LDURH`, `LDRSH`, `LDURSH`, `LDRSW`, `LDURSW`). -/
  | ldr (w : RegWidth) (sz : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode)
  /-- PC-relative literal load (`LDR Wt/Xt, label` when `signed = false`, `LDRSW Xt, label` when `signed = true`). -/
  | ldrLit (w : RegWidth) (signed : Bool) (rt : Reg) (offset : BitVec 64)
  /-- Single-register store (`STR`, `STUR`, `STRB`, `STURB`, `STRH`, `STURH`). -/
  | str (sz : MemWidth) (rt : Reg) (addr : AddrMode)
  /-- Register-pair load (`LDP` when `signed = false`, `LDPSW` when `signed = true`). -/
  | ldp (w : RegWidth) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode)
  /-- Register-pair store (`STP`). -/
  | stp (w : RegWidth) (rt1 rt2 : Reg) (addr : AddrMode)
  /-- Load No-Allocate Pair: `LDNP` (`sz ∈ {.W32, .X64}`). -/
  | ldnp (sz : MemWidth) (rn rt rt2 : Reg) (offset : BitVec 64)
  /-- Store No-Allocate Pair: `STNP` (`sz ∈ {.W32, .X64}`). -/
  | stnp (sz : MemWidth) (rn rt rt2 : Reg) (offset : BitVec 64)

  -- Atomics, Exclusives, Ordered Loads/Stores, and Prefetch
  /-- Load-Acquire (`LDAR`, `LDARB`, `LDARH`, `isLoad = true`) and Store-Release (`STLR`, `STLRB`, `STLRH`, `isLoad = false`). -/
  | ldarStlr (sz : MemWidth) (isLoad : Bool) (rn rt : Reg)
  /-- Load-Exclusive (`LDXR*`, `acq = false`) and Load-Acquire Exclusive (`LDAXR*`, `acq = true`). -/
  | ldxr (sz : MemWidth) (acq : Bool) (rn rt : Reg)
  /-- Store-Exclusive (`STXR*`, `rel = false`) and Store-Release Exclusive (`STLXR*`, `rel = true`). -/
  | stxr (sz : MemWidth) (rel : Bool) (rs rn rt : Reg)
  /-- Load-Exclusive pair (`LDXP`, `LDAXP`, `sz ∈ {.W32, .X64}`). -/
  | ldxp (sz : MemWidth) (acq : Bool) (rn rt rt2 : Reg)
  /-- Store-Exclusive pair (`STXP`, `STLXP`, `sz ∈ {.W32, .X64}`). -/
  | stxp (sz : MemWidth) (rel : Bool) (rs rn rt rt2 : Reg)
  /-- Compare and swap (`CAS{A}{L}{B,H}`). -/
  | cas (sz : MemWidth) (acq rel : Bool) (rs rn rt : Reg)
  /-- Compare and swap pair (`CASP{A}{L}`, `sz ∈ {.W32, .X64}`). -/
  | casp (sz : MemWidth) (acq rel : Bool) (rs rs2 rn rt rt2 : Reg)
  /-- LSE atomic read-modify-write and swap (`LD<op>{A}{L}{B,H}`, `ST<op>{L}{B,H}`, `SWP{A}{L}{B,H}`). -/
  | atomicRmw (op : AtomicOp) (sz : MemWidth) (acq rel : Bool) (rs rn rt : Reg)
  /-- Load-Acquire RCpc register (`LDAPR`, `LDAPRB`, `LDAPRH`, `FEAT_LRCPC`). -/
  | ldapr (sz : MemWidth) (rn rt : Reg)
  /-- Load-Acquire / Store-Release RCpc unscaled offset (`STLUR*`, `LDAPUR*`, `LDAPURS*`, `FEAT_LRCPC2`). -/
  | ldapurStlur (sz : MemWidth) (opc : BitVec 2) (rn rt : Reg) (offset : BitVec 64)
  /-- Prefetch memory (`PRFM`, `PRFUM`). -/
  | prfm (prfop : BitVec 5) (addr : AddrMode)
  /-- Prefetch memory PC-relative literal (`PRFM <prfop>, label`). -/
  | prfmLit (prfop : BitVec 5) (offset : BitVec 64)

  -- SIMD/FP Loads and Stores
  /-- SIMD/FP single-register load (`LDR`, `LDUR` on `B`/`H`/`S`/`D`/`Q`). -/
  | ldrSimd (sz : SimdMemSize) (vt : VReg) (addr : AddrMode)
  /-- SIMD/FP single-register store (`STR`, `STUR` on `B`/`H`/`S`/`D`/`Q`). -/
  | strSimd (sz : SimdMemSize) (vt : VReg) (addr : AddrMode)
  /-- SIMD/FP PC-relative literal load (`LDR St/Dt/Qt, label`). -/
  | ldrSimdLit (sz : SimdMemSize) (vt : VReg) (offset : BitVec 64)
  /-- SIMD/FP register-pair load (`LDP` on `S`/`D`/`Q`). -/
  | ldpSimd (sz : SimdMemSize) (vt1 vt2 : VReg) (addr : AddrMode)
  /-- SIMD/FP register-pair store (`STP` on `S`/`D`/`Q`). -/
  | stpSimd (sz : SimdMemSize) (vt1 vt2 : VReg) (addr : AddrMode)
  /-- SIMD/FP non-temporal pair load (`LDNP` on `S`/`D`/`Q`). -/
  | ldnpSimd (sz : SimdMemSize) (vt1 vt2 : VReg) (rn : Reg) (offset : BitVec 64)
  /-- SIMD/FP non-temporal pair store (`STNP` on `S`/`D`/`Q`). -/
  | stnpSimd (sz : SimdMemSize) (vt1 vt2 : VReg) (rn : Reg) (offset : BitVec 64)
  /-- AdvSIMD `ST1` single structure (post-indexed). -/
  | st1SinglePost (q : Bool) (rm : VReg) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) (rn : Reg) (vt : VReg)
  /-- AdvSIMD `LD1` single structure (no-offset or post-indexed) and `ST1` single structure (no-offset). -/
  | simdLdSt1Single (isLoad q postIdx : Bool) (rm : VReg) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) (rn : Reg) (vt : VReg)
  /-- AdvSIMD `LD1`/`ST1` multiple structures (`1..4` consecutive registers, offset or post-indexed). -/
  | simdLdSt1Multi (isLoad q : Bool) (size : BitVec 2) (nregs : Nat) (rn : Reg) (postIdx : Bool) (rm vt : VReg)
  /-- AdvSIMD `LD2`/`LD3`/`LD4` and `ST2`/`ST3`/`ST4` multiple structures (`selem ∈ {2, 3, 4}` interleaved registers, offset or post-indexed). -/
  | simdLdStMulti (isLoad q : Bool) (size : BitVec 2) (selem : Nat) (rn : Reg) (postIdx : Bool) (rm vt : VReg)
  /-- AdvSIMD `LD1R` single structure replicate to all lanes (offset or post-indexed). -/
  | simdLd1r (q : Bool) (size : BitVec 2) (rn : Reg) (postIdx : Bool) (rm vt : VReg)

  -- Scalar Floating-Point
  /-- Floating-point conversion/move between GPR and SIMD/FP register (`FMOV`, `SCVTF`, `UCVTF`, `FCVT*`). -/
  | fmovGprVec (sf : Bool) (ftype : BitVec 2) (rmode : BitVec 2) (opcode : BitVec 3) (rn rd : VReg)
  /-- Scalar floating-point data-processing (1 source: `FMOV`, `FABS`, `FNEG`, `FSQRT`, `FCVT`, `FRINT*`). -/
  | fpDataProc1 (ftype : BitVec 2) (opcode : BitVec 6) (rn rd : VReg)
  /-- Scalar floating-point data-processing (2 source: `FMUL`, `FDIV`, `FADD`, `FSUB`, `FMAX*`, `FMIN*`). -/
  | fpDataProc2 (ftype : BitVec 2) (rm : VReg) (opcode : BitVec 4) (rn rd : VReg)
  /-- Scalar floating-point compare (`FCMP`, `FCMPE`). -/
  | fpCompare (ftype : BitVec 2) (rm : VReg) (op : BitVec 2) (rn : VReg) (opcode2 : BitVec 5)
  /-- Scalar floating-point immediate (`FMOV Sd/Dd, #imm8`). -/
  | fpImm (ftype : BitVec 2) (imm8 : BitVec 8) (rd : VReg)
  /-- Scalar floating-point conditional compare (`FCCMP`, `FCCMPE`). -/
  | fpCondCompare (ftype : BitVec 2) (rm : VReg) (cond : BitVec 4) (rn : VReg) (op : Bool) (nzcv : BitVec 4)
  /-- Scalar floating-point conditional select (`FCSEL`). -/
  | fpCondSelect (ftype : BitVec 2) (rm : VReg) (cond : BitVec 4) (rn rd : VReg)
  /-- Scalar floating-point data-processing (3 source: `FMADD`, `FMSUB`, `FNMADD`, `FNMSUB`). -/
  | fpDataProc3 (ftype : BitVec 2) (o1 : Bool) (rm : VReg) (o0 : Bool) (ra rn rd : VReg)
  /-- Scalar floating-point / fixed-point conversion (`SCVTF`, `UCVTF`, `FCVTZS`, `FCVTZU` fixed-point). -/
  | fpFixedConv (sf : Bool) (ftype : BitVec 2) (rmode : BitVec 2) (opcode : BitVec 3) (scale : BitVec 6) (rn rd : VReg)

  -- AdvSIMD & Cryptographic Extensions
  /-- AdvSIMD modified immediate (`MOVI`, `MVNI`, `ORR`, `BIC`, `FMOV`) and shift by immediate (`SHL`, `USHR`, `SSHR`, `SHRN`, `USHLL`, ...). -/
  | simdImmShift (q op : Bool) (immh : BitVec 4) (immb : BitVec 3) (opcode : BitVec 5) (rn rd : VReg)
  /-- AdvSIMD copy / duplicate / insert / extract (`DUP`, `INS`, `UMOV`, `SMOV`). -/
  | simdInsDup (q op : Bool) (imm5 : BitVec 5) (imm4 : BitVec 4) (rn rd : VReg)
  /-- AdvSIMD three-register same (`AND`, `BIC`, `ORR`, `ORN`, `EOR`, `BSL`, `BIT`, `BIF`, `ADD`, `SUB`, `CMEQ`, `CMGT`, `CMHI`, `SSHL`, `USHL`, `ADDP`, ...). -/
  | simdThreeSame (q u : Bool) (size : BitVec 2) (rm : VReg) (opcode : BitVec 5) (rn rd : VReg)
  /-- AdvSIMD two-register miscellaneous (`REV64`, `REV32`, `REV16`, `CNT`, `NOT`, `RBIT`, `CLZ`, `CLS`, `XTN`, `CM* #0`, `ABS`, `NEG`, ...). -/
  | simdTwoRegMisc (q u : Bool) (size : BitVec 2) (opcode : BitVec 5) (rn rd : VReg)
  /-- AdvSIMD across-lanes reduction (`ADDV`, `SADDLV`, `UADDLV`, `SMAXV`, `UMAXV`, `SMINV`, `UMINV`). -/
  | simdAcrossLanes (q u : Bool) (size : BitVec 2) (opcode : BitVec 5) (rn rd : VReg)
  /-- AdvSIMD vector permute (`UZP1`, `TRN1`, `ZIP1`, `UZP2`, `TRN2`, `ZIP2`). -/
  | simdPermute (q : Bool) (size : BitVec 2) (rm : VReg) (opcode : BitVec 3) (rn rd : VReg)
  /-- AdvSIMD byte-wise extract from pair (`EXT`). -/
  | simdExt (q : Bool) (rm : VReg) (imm4 : BitVec 4) (rn rd : VReg)
  /-- AdvSIMD byte table lookup (`TBL`, `isTbx = false`) and table extension (`TBX`, `isTbx = true`). -/
  | simdTbl (q : Bool) (rm : VReg) (len : BitVec 2) (isTbx : Bool) (rn rd : VReg)
  /-- AdvSIMD scalar pairwise add (`ADDP Dd, Vn.2D`). -/
  | simdAddpScalar (rn rd : VReg)
  /-- AdvSIMD scalar duplicate element (`DUP <V><d>, <Vn>.<T>[<index>]` / `MOV <V><d>, <Vn>.<T>[<index>]`). -/
  | simdDupScalar (imm5 : BitVec 5) (rn rd : VReg)
  /-- AdvSIMD polynomial multiply long (`PMULL`, `PMULL2`). -/
  | simdPmull (q is64 : Bool) (rm rn rd : VReg)
  /-- AdvSIMD three-register different (`SADDL`/`UADDL`, `SADDW`/`UADDW`, `SSUBL`/`USUBL`, `SSUBW`/`USUBW`, `ADDHN`/`RADDHN`, `SABAL`/`UABAL`, `SUBHN`/`RSUBHN`, `SABDL`/`UABDL`, `SMLAL`/`UMLAL`, `SMLSL`/`UMLSL`, `SMULL`/`UMULL`, and `*2` variants). -/
  | simdThreeDiff (q u : Bool) (size : BitVec 2) (rm : VReg) (opcode : BitVec 4) (rn rd : VReg)
  /-- `FEAT_AES` round operations (`AESE`, `AESD`, `AESMC`, `AESIMC`). -/
  | aes (op : AesOp) (rd rn : VReg)
  /-- `FEAT_SHA1`/`FEAT_SHA256` 2-register SHA (`SHA1H`, `SHA1SU1`, `SHA256SU0`). -/
  | cryptoSha2Reg (opcode : BitVec 5) (rn rd : VReg)
  /-- `FEAT_SHA1`/`FEAT_SHA256` 3-register SHA (`SHA1C`, `SHA1P`, `SHA1M`, `SHA1SU0`, `SHA256H`, `SHA256H2`, `SHA256SU1`). -/
  | cryptoSha3Reg (opcode : BitVec 3) (rm rn rd : VReg)
  /-- `FEAT_SHA512` 2-register schedule update 0 (`SHA512SU0`). -/
  | cryptoSha512Reg2 (rn rd : VReg)
  /-- `FEAT_SHA512`/`FEAT_SHA3` 3-register (`SHA512H`, `SHA512H2`, `SHA512SU1`, `RAX1`). -/
  | cryptoSha512Reg3 (opcode : BitVec 2) (rm rn rd : VReg)
  /-- `FEAT_SHA3` 4-register bitwise (`EOR3`, `BCAX`). -/
  | cryptoSha3FourReg (isBcax : Bool) (rm ra rn rd : VReg)
  /-- `FEAT_SHA3` Exclusive-OR and Rotate (`XAR`). -/
  | cryptoXar (rm : VReg) (imm6 : BitVec 6) (rn rd : VReg)
  deriving DecidableEq, Repr, Inhabited

/-- True when `(opcode, sBit, size)` encodes a valid AdvSIMD `LD1`/`ST1` single-structure
    lane transfer (`8-bit B` when `opcode = 000`, `16-bit H` when `opcode = 010 && size[0] = 0`,
    `32-bit S` when `opcode = 100 && size = 00`, or `64-bit D` when `opcode = 100 && size = 01 && !sBit`). -/
@[inline] def validSimdLdSt1Single (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) : Bool :=
  opcode == 0b000#3 ||
  (opcode == 0b010#3 && size.extractLsb' 0 1 == 0#1) ||
  (opcode == 0b100#3 && (size == 0b00#2 || (size == 0b01#2 && !sBit)))

/-- True when `(size, opcode)` encodes a modeled non-saturating AdvSIMD three-different instruction
    (`size != 11` and `opcode ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12}`). -/
@[inline] def validSimdThreeDiff (size : BitVec 2) (opcode : BitVec 4) : Bool :=
  size != 3#2 &&
  (opcode <= 8#4 || opcode == 10#4 || opcode == 12#4)

end Arm64


