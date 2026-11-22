-- Prove2me | Definitions.Def_X25519Dalek_Spec
-- name    : X25519Dalek_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T21:20:30.441975+00:00
-- url     : https://prove2.me/theorems/f5093b7d-bc1c-4d12-a78f-e6559a28916f
-- title:
--   Contracts of the x25519-dalek functions on AArch64
-- statement:
--   The encodings curve25519-dalek uses in memory, the pure functions its code computes on them, and one contract per function of `x25519CliMultiLib` (three for the field multiplication). The contracts are Google DeepMind's (google-deepmind/code-verification @ `8c8d371f`, `Shared51/InternalSpecs.lean`), written there with the `rust_spec` macro, which prove2.me rejects as metaprogramming. Each is written out here as the term the macro elaborates to, and the 21 written-out contracts were checked equal by `rfl` to the macro's output under Lean 4.33.1 (repository script `elab/Check/Rfl.lean`). The helper definitions are copied with unchanged bodies.
--
--   **The judgment.** `fnOk fnName spec` says: the function `fnName` is defined in some block $i$ of the library, and for every multi-block placement `mpl` that the `Arm64` model accepts (`Placeable`), `subroutine_ok` holds for block $i$'s placed program at the function's address, with `spec mpl` and with the code of all 19 blocks loaded in memory added to the precondition. It is `Obj.MultiPlacedLib.subroutineOk` without that judgment's requirement that the function be exported; the two exported functions use `x25519CliMultiLib.subroutineOk` itself. `subroutine_ok` is total correctness: for every ghost value, every frame $R$ and every entry state at the address with the stack pointer 16-byte aligned whose memory satisfies the precondition separately from $R$, execution terminates, returning to the link register with the stack pointer and the AAPCS64 callee-saved registers restored and the postcondition holding with $R$; panics, process exits and running out of memory are excluded.
--
--   **Encodings.** curve25519-dalek 5.0.0 describes them in src/backend/serial/u64/field.rs, lines 27–32 (p. 18 of the excerpts): “A `FieldElement51` represents an element of the field $\mathbb Z / (2^{255} - 19)$. In the 64-bit implementation, a `FieldElement` is represented in radix $2^{51}$ as five `u64`s; the coefficients are allowed to grow up to $2^{54}$ between reductions modulo $p$.”; and in src/backend/serial/curve_models.rs (p. 15): “A `CompletedPoint` is a point $((X:Z), (Y:T))$ on the $\mathbb P^1 \times \mathbb P^1$ model of the curve.” (lines 160–161) and “A pre-computed point in the affine model for the curve, represented as $(y+x, y-x, 2dxy)$ in "Niels coordinates".” (lines 176–177).
--   - A `FieldElement51` is 40 bytes, five little-endian 64-bit limbs $l_0, \dots, l_4$ (`ByteSlice.readLE`) with value $l_0 + l_1 2^{51} + l_2 2^{102} + l_3 2^{153} + l_4 2^{204}$ (`fe51Val`, `fe51ValOfBytes`, `fe51ValAt` at an offset). `fe51LimbsBounded bs b` and `fe51LimbsBoundedAt bs off b` say each limb is below $b$ (the first also that `bs` has 40 bytes).
--   - An Edwards point in extended coordinates is 160 bytes, four `FieldElement51`s $X, Y, Z, T$ (`fe51Point4Bounded`, and `edExtOfBytes` for the four values mod $p$); a projective point is 120 bytes $(X, Y, Z)$; an `AffineNielsPoint` is 120 bytes $(y{+}x, y{-}x, xy2d)$ (`fe51AffineNielsBoundedAt`); a `LookupTable` is 8 of them (`fe51LookupTable8Bounded`); the basepoint table is 32 lookup tables, 30,720 bytes (`fe51BasepointTable32Bounded`, using `ByteSlice.slice`).
--   - A Montgomery projective point is 80 bytes, $(U, W)$ (`montProjBounded`, `montProjOfBytes`).
--   - `fe51_one`, `fe51_mont_a24` and `ed25519_basepoint_table` are the placed addresses of the three read-only constants, and `fe51OneBytes`, `fe51MontA24Bytes`, `ed25519BasepointTableBytes` their bytes in the object.
--
--   **Pure functions.** `edProjDouble` and `edAddAffineNiels` are the doubling and mixed-addition formulas of curve25519-dalek's `curve_models.rs`, mod $p$; `edAsProjective` and `edAsExtended` convert a completed point; `edDouble4` is four doublings; `edExtToMontgomeryU` is $(Z + Y)(Z - Y)^{p-2}$; `edSelectAffineNiels` is the signed lookup in an 8-entry table; `scalarRadix16Digits` the signed radix-16 recoding; and `edMulBase` the fixed-base multiplication of `EdwardsBasepointTable::mul_base` through these. The field operations and RFC 7748's functions come from the bundle `X25519Dalek_Rfc7748`.
--
--   **The contracts.** Arguments are in `x0`, `x1`, `x2`; a result larger than a register is written to the buffer whose address is in `x8` (in `x0` for `as_radix_16`, `pow22501` and `select`). Each contract takes the buffers, read-only constants and stack frame it needs (of the stated size below the stack pointer, any contents) and hands them back; buffers are disjoint, and read-only (`↦ᵣ`) where the code only reads them. Field values in results are stated mod $p$ with the limb bounds each contract states, so they can be fed to the next call. The two entry points:
--   - `staticSecretDiffieHellmanSpec`: from the secret $k$ and public key $u$ (32 bytes each), `out` holds `x25519 k u`;
--   - `publicKeyFromSecretSpec`: from the secret $k$, `out` holds `x25519Pubkey k`.
--
--   The internal contracts are described in their milestones.
-- source:
--   curve25519-dalek 5.0.0 (https://crates.io/crates/curve25519-dalek/5.0.0), the FieldElement51 encoding (backend/serial/u64/field.rs, lines 20–45), the point models (backend/serial/curve_models.rs) and the contracts of the 19 functions, after DeepMind's (Shared51/InternalSpecs.lean)

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (dbenbenn/x25519-dalek-aarch64, tools/make_spec.py): from
google-deepmind/code-verification @ 8c8d371f, `LibsignalBinary/Proofs/HookDischarge/CryptoX25519/
Shared51/{InternalSpecs,CommonBase}.lean` and `arm64-semantics/ProofLib/SepLogic/SliceArray.lean`
(`ByteSlice.slice`, `ByteSlice.readLE`). The definitions are kept with unchanged bodies, in the
namespace `X25519Dalek`, as a plain (non-`module`) file; theorems are dropped. Each contract, written
upstream with the `rust_spec` macro (rejected by prove2.me), is written out as the term the macro
elaborates to (Lean 4.33.1). DeepMind's `X25519BlockOk`, which quantifies over a placement type
class, is replaced by `fnOk`, which quantifies over placements explicitly.
-/

import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_Arm64_Spec_Placed

/-!
# Contracts of the x25519-dalek blocks on AArch64

The 40-byte `FieldElement51` encoding (five 64-bit limbs in radix `2^51`) and the point encodings
of curve25519-dalek, the pure functions the code computes on them, the addresses of the
library's three read-only constants, the judgment `fnOk` for a function of the library that is
not exported, and one contract (`Arm64.Spec`) per block and calling mode, after DeepMind's.

Registers follow AAPCS64: arguments in `x0`, `x1`, `x2`, an indirect result address in `x8`, the
result in `x0`. Each contract owns a stack frame of the stated size below `sp`.
-/

namespace X25519Dalek

set_option linter.unusedVariables false

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

namespace ByteSlice

/-- The `n` bytes of `buf` from offset `off`. -/
def slice (buf : List (BitVec 8)) (off n : Nat) : List (BitVec 8) :=
  (buf.drop off).take n
/-- The little-endian value of the `n ≤ 8` bytes of `bs` from offset `off`, as a 64-bit word. -/
def readLE (bs : List (BitVec 8)) (off : Nat) : Nat → BitVec 64
  | 0 => 0#64
  | n + 1 => readLE bs off n ||| (((bs.getD (off + n) 0#8).zeroExtend 64) <<< (8 * n))
end ByteSlice

/-- Address of `FieldElement51::ONE` (40 bytes) under the placement `mpl`. -/
abbrev fe51_one (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.0"

/-- Address of the constant `121666` (40 bytes, `FieldElement51`) under the placement `mpl`. -/
abbrev fe51_mont_a24 (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek:.rodata..Lanon.35"

/-- Address of `ED25519_BASEPOINT_TABLE` (30,720 bytes) under the placement `mpl`. -/
abbrev ed25519_basepoint_table (mpl : Obj.MultiPlacement) : BitVec 64 :=
  mpl.ρ "curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN"

/-- The bytes of `FieldElement51::ONE`. -/
abbrev fe51OneBytes : List (BitVec 8) := x25519CliData00Bytes

/-- The bytes of the constant `121666`. -/
abbrev fe51MontA24Bytes : List (BitVec 8) := x25519CliData01Bytes

/-- The bytes of `ED25519_BASEPOINT_TABLE`. -/
abbrev ed25519BasepointTableBytes : List (BitVec 8) := x25519CliData02Bytes

/-- The value `l0 + l1·2^51 + l2·2^102 + l3·2^153 + l4·2^204` of five limbs. -/
def fe51Val (l0 l1 l2 l3 l4 : BitVec 64) : Nat :=
  l0.toNat + l1.toNat * 2 ^ 51 + l2.toNat * 2 ^ 102 + l3.toNat * 2 ^ 153 + l4.toNat * 2 ^ 204

/-- The value of the `FieldElement51` in the first 40 bytes of `bs`. -/
def fe51ValOfBytes (bs : List (BitVec 8)) : Nat :=
  fe51Val
    (ByteSlice.readLE bs 0 8)
    (ByteSlice.readLE bs 8 8)
    (ByteSlice.readLE bs 16 8)
    (ByteSlice.readLE bs 24 8)
    (ByteSlice.readLE bs 32 8)

/-! ## 1. Little-Endian Word Encoding, Limb Bounds, & Radix-16 Recoding -/

/-- All 5 limbs of a 40-byte `FieldElement51` buffer are bounded by `bound`. -/
def fe51LimbsBounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 40 ∧
  (ByteSlice.readLE bs 0 8).toNat < bound ∧
  (ByteSlice.readLE bs 8 8).toNat < bound ∧
  (ByteSlice.readLE bs 16 8).toNat < bound ∧
  (ByteSlice.readLE bs 24 8).toNat < bound ∧
  (ByteSlice.readLE bs 32 8).toNat < bound

/-- Signed radix-16 recoding (`[i8; 64]`) of a 32-byte scalar `a_bs` (`a_bs[31] ≤ 127`). -/
def scalarRadix16Digits (a_bs : List (BitVec 8)) : List (BitVec 8) :=
  let rec go (idx : Nat) (carry : Int) (acc : List (BitVec 8)) : List (BitVec 8) :=
    match idx with
    | 0 => acc.reverse
    | k + 1 =>
      let i := 63 - k
      let byte := (a_bs.getD (i / 2) 0#8).toNat
      let botHalf : Int := if i % 2 == 0 then Int.ofNat (byte &&& 0x0f) else Int.ofNat (byte >>> 4)
      let d := botHalf + carry
      if i < 63 then
        let carry' : Int := (d + 8) / 16
        let digit' : Int := d - carry' * 16
        go k carry' (BitVec.ofInt 8 digit' :: acc)
      else
        go k 0 (BitVec.ofInt 8 d :: acc)
  go 64 0 []

/-! ## 2. 5-Limb `FieldElement51` Edwards & Montgomery Point Encodings -/

/-- All 5 limbs of a `FieldElement51` at byte offset `off` in `bs` are `< bound`. -/
def fe51LimbsBoundedAt (bs : List (BitVec 8)) (off bound : Nat) : Prop :=
  (ByteSlice.readLE bs off 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 8) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 16) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 24) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 32) 8).toNat < bound

/-- Radix-`2^51` integer value of the `FieldElement51` at byte offset `off` in `bs`. -/
def fe51ValAt (bs : List (BitVec 8)) (off : Nat) : Nat :=
  fe51Val
    (ByteSlice.readLE bs off 8)
    (ByteSlice.readLE bs (off + 8) 8)
    (ByteSlice.readLE bs (off + 16) 8)
    (ByteSlice.readLE bs (off + 24) 8)
    (ByteSlice.readLE bs (off + 32) 8)

/-- A 160-byte `EdwardsPoint` or `CompletedPoint` buffer has 4 limb-bounded `FieldElement51`
    coordinates `(X, Y, Z, T)` at offsets `0, 40, 80, 120`. -/
def fe51Point4Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 160 ∧
  fe51LimbsBoundedAt bs 0 bound ∧
  fe51LimbsBoundedAt bs 40 bound ∧
  fe51LimbsBoundedAt bs 80 bound ∧
  fe51LimbsBoundedAt bs 120 bound

/-- Extract the 4 field coordinates `(X, Y, Z, T) mod p25519` of a 160-byte point buffer. -/
def edExtOfBytes (bs : List (BitVec 8)) : EdExtPoint :=
  ⟨fe51ValAt bs 0 % p25519,
   fe51ValAt bs 40 % p25519,
   fe51ValAt bs 80 % p25519,
   fe51ValAt bs 120 % p25519⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `ProjectivePoint::double(X, Y, Z)`. -/
def edProjDouble (X Y Z : Nat) : EdExtPoint :=
  let XX := fpSq (X % p25519)
  let YY := fpSq (Y % p25519)
  let ZZ2 := fpAdd (fpSq (Z % p25519)) (fpSq (Z % p25519))
  let Y_plus_X_sq := fpSq (fpAdd (X % p25519) (Y % p25519))
  let YpX2 := fpAdd XX YY
  let YmX2 := fpSub YY XX
  ⟨fpSub Y_plus_X_sq YpX2, YpX2, YmX2, fpSub ZZ2 YmX2⟩

/-- `CompletedPoint` result `(X', Y', Z', T')` of `&EdwardsPoint + &AffineNielsPoint`. -/
def edAddAffineNiels (P : EdExtPoint) (y_plus_x y_minus_x xy2d : Nat) : EdExtPoint :=
  let PP := fpMul (fpAdd P.X P.Y) y_plus_x
  let MM := fpMul (fpSub P.Y P.X) y_minus_x
  let TT2d := fpMul P.T xy2d
  let ZZ2 := fpAdd P.Z P.Z
  ⟨fpSub PP MM, fpAdd MM PP, fpAdd TT2d ZZ2, fpSub ZZ2 TT2d⟩

/-- Convert a `CompletedPoint` to a `ProjectivePoint` (`X*T, Y*Z, Z*T`). -/
def edAsProjective (C : EdExtPoint) : EdExtPoint :=
  ⟨fpMul C.X C.T, fpMul C.Y C.Z, fpMul C.Z C.T, 0⟩

/-- Convert a `CompletedPoint` to an `EdwardsPoint` (`X*T, Y*Z, Z*T, X*Y`). -/
def edAsExtended (C : EdExtPoint) : EdExtPoint :=
  ⟨fpMul C.X C.T, fpMul C.Y C.Z, fpMul C.Z C.T, fpMul C.X C.Y⟩

/-- Quadruple point doubling (`[16]P`) computed by `mul_by_pow_2(P, 4)`. -/
def edDouble4 (P : EdExtPoint) : EdExtPoint :=
  let P1 := edAsProjective (edProjDouble P.X P.Y P.Z)
  let P2 := edAsProjective (edProjDouble P1.X P1.Y P1.Z)
  let P3 := edAsProjective (edProjDouble P2.X P2.Y P2.Z)
  edAsExtended (edProjDouble P3.X P3.Y P3.Z)

/-- Montgomery `u`-coordinate `(Z + Y) * (Z - Y)⁻¹ mod p` computed by `EdwardsPoint::to_montgomery`. -/
def edExtToMontgomeryU (P : EdExtPoint) : Nat :=
  fpMul (fpAdd P.Z P.Y) (fpInv (fpSub P.Z P.Y))

/-- All 3 `FieldElement51` coordinates of a 120-byte `AffineNielsPoint` at `base` are `< bound`. -/
def fe51AffineNielsBoundedAt (bs : List (BitVec 8)) (base bound : Nat) : Prop :=
  fe51LimbsBoundedAt bs base bound ∧
  fe51LimbsBoundedAt bs (base + 40) bound ∧
  fe51LimbsBoundedAt bs (base + 80) bound

/-- A 960-byte `LookupTable<AffineNielsPoint>` (8 entries × 120 bytes) has all limbs `< bound`. -/
def fe51LookupTable8Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 960 ∧
  fe51AffineNielsBoundedAt bs 0 bound ∧ fe51AffineNielsBoundedAt bs 120 bound ∧
  fe51AffineNielsBoundedAt bs 240 bound ∧ fe51AffineNielsBoundedAt bs 360 bound ∧
  fe51AffineNielsBoundedAt bs 480 bound ∧ fe51AffineNielsBoundedAt bs 600 bound ∧
  fe51AffineNielsBoundedAt bs 720 bound ∧ fe51AffineNielsBoundedAt bs 840 bound

/-- The `j`-th `AffineNielsPoint` entry `(y_plus_x, y_minus_x, xy2d)` mod `p25519`. -/
def edTableEntryAt (table_bs : List (BitVec 8)) (j : Nat) : Nat × Nat × Nat :=
  (fe51ValAt table_bs (120 * j) % p25519,
   fe51ValAt table_bs (120 * j + 40) % p25519,
   fe51ValAt table_bs (120 * j + 80) % p25519)

/-- Constant-time signed lookup `LookupTable<AffineNielsPoint>::select(table, x)`. -/
def edSelectAffineNiels (table_bs : List (BitVec 8)) (x : BitVec 8) : Nat × Nat × Nat :=
  let (ypx, ymx, xy2d) :=
    if x == 8#8 || x == -8#8 then edTableEntryAt table_bs 7
    else if x == 7#8 || x == -7#8 then edTableEntryAt table_bs 6
    else if x == 6#8 || x == -6#8 then edTableEntryAt table_bs 5
    else if x == 5#8 || x == -5#8 then edTableEntryAt table_bs 4
    else if x == 4#8 || x == -4#8 then edTableEntryAt table_bs 3
    else if x == 3#8 || x == -3#8 then edTableEntryAt table_bs 2
    else if x == 2#8 || x == -2#8 then edTableEntryAt table_bs 1
    else if x == 1#8 || x == -1#8 then edTableEntryAt table_bs 0
    else (1, 1, 0)
  if x.msb then (ymx, ypx, fpNeg xy2d) else (ypx, ymx, xy2d)

/-- A 30,720-byte `EdwardsBasepointTable` (`[LookupTable<AffineNielsPoint>; 32]`) has all 32
    960-byte sub-tables limb-bounded by `< bound`. -/
def fe51BasepointTable32Bounded (table_bs : List (BitVec 8)) (bound : Nat) : Prop :=
  table_bs.length = 30720 ∧
  ∀ i < 32, fe51LookupTable8Bounded (ByteSlice.slice table_bs (960 * i) 960) bound

/-- Single radix-16 step of `EdwardsBasepointTable::mul_base`. -/
def edMulBaseStep (table_bs : List (BitVec 8)) (i : Nat) (d : BitVec 8)
    (acc : EdExtPoint) : EdExtPoint :=
  let (ypx, ymx, xy2d) := edSelectAffineNiels (ByteSlice.slice table_bs (960 * i) 960) d
  edAsExtended (edAddAffineNiels acc ypx ymx xy2d)

/-- Curried single-iteration step of `EdwardsBasepointTable::mul_base` at table index `i`. -/
def edMulBaseStepAt (table_bs digits : List (BitVec 8)) (parity i : Nat)
    (acc : EdExtPoint) : EdExtPoint :=
  edMulBaseStep table_bs i (digits.getD (2 * i + parity) 0#8) acc

/-- Generic structural loop running `step` for `rem` iterations starting at index `i`. -/
def edMulBaseLoopWith {α : Type} (step : Nat → α → α) (i rem : Nat) (acc : α) : α :=
  Nat.rec (motive := fun _ => Nat → α → α)
    (fun _ acc => acc) (fun _ ih i acc => ih (i + 1) (step i acc)) rem i acc

/-- Structural recursion for `rem` iterations of the odd (`parity = 1`) or even (`parity = 0`)
    loop of `EdwardsBasepointTable::mul_base`. -/
def edMulBaseLoop (table_bs digits : List (BitVec 8)) (parity i rem : Nat)
    (acc : EdExtPoint) : EdExtPoint :=
  edMulBaseLoopWith (edMulBaseStepAt table_bs digits parity) i rem acc

/-- Pure projective model of `<EdwardsBasepointTable as BasepointTable>::mul_base`. -/
def edMulBase (table_bs scalar_bs : List (BitVec 8)) : EdExtPoint :=
  let digits := scalarRadix16Digits scalar_bs
  edMulBaseLoop table_bs digits 0 0 32 (edDouble4 (edMulBaseLoop table_bs digits 1 0 32 edExtZero))

/-- All 5 limbs of a `FieldElement51` at byte offset `off` in `bs` are `< bound` (Montgomery alias). -/
abbrev montFe51LimbsBoundedAt := fe51LimbsBoundedAt

/-- Radix-`2^51` integer value at byte offset `off` in `bs` (Montgomery alias). -/
abbrev montFe51ValAt := fe51ValAt

/-- An 80-byte `montgomery::ProjectivePoint` buffer `(U, W)` has two limb-bounded `FieldElement51`
    coordinates at offsets `0` and `40`. -/
def montProjBounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 80 ∧
  montFe51LimbsBoundedAt bs 0 bound ∧
  montFe51LimbsBoundedAt bs 40 bound

/-- Extract `(U mod p25519, W mod p25519)` from an 80-byte `montgomery::ProjectivePoint` buffer. -/
def montProjOfBytes (bs : List (BitVec 8)) : MontProjPoint :=
  ⟨montFe51ValAt bs 0 % p25519, montFe51ValAt bs 40 % p25519⟩

/-! ## The judgment for a function of the library -/

/-- The function `fnName` of `x25519CliMultiLib`, which need not be exported, satisfies `spec`: it
is defined in some block `i` at offset `off`, and for every multi-block placement `mpl` under which
the library is `Placeable`, `subroutine_ok` holds for block `i`'s placed program at the function's
address, with the library's code loaded and the spec instantiated at `mpl` and block `i`'s base.
This is `Obj.MultiPlacedLib.subroutineOk` without its requirement that `fnName` be exported. -/
def fnOk {S α : Type} [ToBaseSpec S α] (fnName : String) (spec : Obj.MultiPlacement → S) : Prop :=
  ∃ i off, lookupBlockSym fnName x25519CliMultiLib.blocks = some (i, off) ∧
    ∀ mpl : Obj.MultiPlacement, x25519CliMultiLib.Placeable mpl →
      subroutine_ok (x25519CliMultiLib.blockProgram mpl i) (x25519CliMultiLib.fnAddr mpl fnName)
        (x25519CliMultiLib.withCodeLoaded mpl (ToBaseSpec.toSpec (spec mpl) (mpl.base i)))

/-! ## Contracts -/

/-- `subtle::black_box::<u8>` (`Blk00`, 5 insns, stack 16): returns `v` (`w0`) unchanged. -/
abbrev blackBoxU8Spec : Spec
  (BitVec 8) :=
{
  pre := fun (v : BitVec 8) (s0 : State) =>
    ⌜BitVec.truncate 8 (s0.readReg32 Reg.x0) = v⌝ ∗ stackFrame s0 16,
  post := fun (v : BitVec 8) (s0 sf : State) =>
    stackFrame sf 16 ∗ ⌜BitVec.truncate 8 (sf.readReg32 Reg.x0) = v⌝ }

/-- `<&FieldElement51 as Mul>::mul` (`Blk01`, 166 insns, stack 224). -/
abbrev fe51MulSpec : Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
{
  pre :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = a ∧
              s0.readReg64 Reg.x1 = b ∧
                out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)⌝ ∗
        a ↦ₛ a_bs ∗ b ↦ₛ b_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 224,
  post :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 sf : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      a ↦ₛ a_bs ∗
        b ↦ₛ b_bs ∗
          stackFrame sf 224 ∗
            ∃∗ res_bs : List (BitVec 8),
              out ↦ₛ res_bs ∗
                ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      fe51ValOfBytes a_bs * fe51ValOfBytes b_bs % p25519⌝ }

/-- Read-only-rhs variant of `<&FieldElement51 as Mul>::mul` (`Blk01`, stack 224). -/
abbrev fe51MulRoRightSpec : Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
{
  pre :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = a ∧
              s0.readReg64 Reg.x1 = b ∧
                out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)⌝ ∗
        a ↦ₛ a_bs ∗ b ↦ᵣ b_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 224,
  post :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 sf : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      a ↦ₛ a_bs ∗
        b ↦ᵣ b_bs ∗
          stackFrame sf 224 ∗
            ∃∗ res_bs : List (BitVec 8),
              out ↦ₛ res_bs ∗
                ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      fe51ValOfBytes a_bs * fe51ValOfBytes b_bs % p25519⌝ }

/-- Read-only-lhs variant of `<&FieldElement51 as Mul>::mul` (`Blk01`, stack 224), used when
    `differential_add_and_double` passes `.rodata` `fe51_mont_a24` in `x0`. -/
abbrev fe51MulRoLeftSpec : Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
{
  pre :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = a ∧
              s0.readReg64 Reg.x1 = b ∧
                out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)⌝ ∗
        a ↦ᵣ a_bs ∗ b ↦ₛ b_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 224,
  post :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 sf : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      a ↦ᵣ a_bs ∗
        b ↦ₛ b_bs ∗
          stackFrame sf 224 ∗
            ∃∗ res_bs : List (BitVec 8),
              out ↦ₛ res_bs ∗
                ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      fe51ValOfBytes a_bs * fe51ValOfBytes b_bs % p25519⌝ }

/-- `FieldElement51::pow2k` (`Blk02`, 100 insns, stack 96). -/
abbrev fe51Pow2kSpec : Spec
  (BitVec 64 × BitVec 64 × BitVec 32 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × BitVec 32 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, a, k, out_bs, a_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = a ∧
              s0.readReg32 Reg.x1 = k ∧
                out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ 0 < k.toNat ∧ k.toNat < 256⌝ ∗
        a ↦ₛ a_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 96,
  post := fun (x : BitVec 64 × BitVec 64 × BitVec 32 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, a, k, out_bs, a_bs) =>
      a ↦ₛ a_bs ∗
        stackFrame sf 96 ∗
          ∃∗ res_bs : List (BitVec 8),
            out ↦ₛ res_bs ∗
              ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                  fe51ValOfBytes res_bs % p25519 =
                    fpPow (fe51ValOfBytes a_bs % p25519)
                      (2 ^ k.toNat)⌝ }

/-- `Scalar::as_radix_16` (`Blk03`, 173 insns, stack 0). -/
abbrev scalarAsRadix16Spec : Spec
  (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, a, out_bs, a_bs) =>
      ⌜s0.readReg64 Reg.x0 = out ∧
            s0.readReg64 Reg.x1 = a ∧ out_bs.length = 64 ∧ a_bs.length = 32 ∧ (a_bs.getD 31 0#8).toNat ≤ 127⌝ ∗
        a ↦ₛ a_bs ∗ out ↦ₛ out_bs,
  post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, a, out_bs, a_bs) => a ↦ₛ a_bs ∗ out ↦ₛ scalarRadix16Digits a_bs }

/-- `Rev::nth` (`Blk04`, 41 insns, stack 16) at `n = 1#64` on `[0, 256)`. -/
abbrev revNthBit254Spec : Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) (s0 : State) =>
    match x with
    | (iter, n, scalar_ptr, scalar_bs) =>
      ⌜s0.readReg64 Reg.x0 = iter ∧ s0.readReg64 Reg.x1 = n ∧ n = 1#64 ∧ scalar_bs.length = 32⌝ ∗
        iter ↦₆₄ scalar_ptr ∗
          (iter + 8#64) ↦₆₄ 0#64 ∗ scalar_ptr ↦ₛ scalar_bs ∗ (iter + 16#64) ↦₆₄ 256#64 ∗ stackFrame s0 16,
  post := fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (iter, n, scalar_ptr, scalar_bs) =>
      iter ↦₆₄ scalar_ptr ∗
        (iter + 8#64) ↦₆₄ 0#64 ∗
          scalar_ptr ↦ₛ scalar_bs ∗
            stackFrame sf 16 ∗
              (iter + 16#64) ↦₆₄ 254#64 ∗
                ⌜BitVec.truncate 8 (sf.readReg32 Reg.x0) =
                    BitVec.ofNat 8 (leBytesToNat scalar_bs / 2 ^ 254 % 2)⌝ }

/-- `FieldElement51::pow22501` (`Blk05`, 101 insns, stack 1040). -/
abbrev fe51Pow22501Spec : Spec
  (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, a, out_bs, a_bs) =>
      ⌜s0.readReg64 Reg.x0 = out ∧
            s0.readReg64 Reg.x1 = a ∧ out_bs.length = 80 ∧ fe51LimbsBounded a_bs (2 ^ 54)⌝ ∗
        a ↦ₛ a_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 1040,
  post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, a, out_bs, a_bs) =>
      a ↦ₛ a_bs ∗
        stackFrame sf 1040 ∗
          ∃∗ t19_bs : List (BitVec 8),
            ∃∗ t3_bs : List (BitVec 8),
              out ↦ₛ (t19_bs ++ t3_bs) ∗
                ⌜fe51LimbsBounded t19_bs (2 ^ 52) ∧
                    fe51LimbsBounded t3_bs (2 ^ 52) ∧
                      fe51ValOfBytes t19_bs % p25519 =
                          fpPow (fe51ValOfBytes a_bs % p25519)
                            (2 ^ 250 - 1) ∧
                        fe51ValOfBytes t3_bs % p25519 =
                          fpPow (fe51ValOfBytes a_bs % p25519) 11⌝ }

/-- `<LookupTable<AffineNielsPoint>>::select` (`Blk06`, 191 insns, stack 192). -/
abbrev lookupTableAffineNielsSelectSpec : Spec
  (BitVec 64 × BitVec 64 × BitVec 8 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × BitVec 8 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, table, x, out_bs, table_bs) =>
      ⌜s0.readReg64 Reg.x0 = out ∧
            s0.readReg64 Reg.x1 = table ∧
              BitVec.truncate 8 (s0.readReg32 Reg.x2) = x ∧
                out_bs.length = 120 ∧ fe51LookupTable8Bounded table_bs (2 ^ 53)⌝ ∗
        table ↦ᵣ table_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 192,
  post := fun (x : BitVec 64 × BitVec 64 × BitVec 8 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, table, x, out_bs, table_bs) =>
      table ↦ᵣ table_bs ∗
        stackFrame sf 192 ∗
          ∃∗ res_bs : List (BitVec 8),
            out ↦ₛ res_bs ∗
              ⌜res_bs.length = 120 ∧
                  fe51AffineNielsBoundedAt res_bs 0 (2 ^ 53) ∧
                    (fe51ValAt res_bs 0 % p25519,
                        fe51ValAt res_bs 40 % p25519,
                        fe51ValAt res_bs 80 % p25519) =
                      edSelectAffineNiels table_bs x⌝ }

/-- `<ProjectivePoint>::double` (`Blk07`, 144 insns, stack 400). -/
abbrev projectivePointDoubleSpec : Spec
  (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, self, out_bs, self_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = self ∧
              out_bs.length = 160 ∧
                self_bs.length = 120 ∧
                  fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
                    fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧ fe51LimbsBoundedAt self_bs 80 (2 ^ 54)⌝ ∗
        self ↦ₛ self_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 400,
  post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, self, out_bs, self_bs) =>
      self ↦ₛ self_bs ∗
        stackFrame sf 400 ∗
          ∃∗ res_bs : List (BitVec 8),
            out ↦ₛ res_bs ∗
              ⌜res_bs.length = 160 ∧
                  fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                    fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                      fe51LimbsBoundedAt res_bs 80 (2 ^ 52) ∧
                        fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
                          edExtOfBytes res_bs =
                            edProjDouble (fe51ValAt self_bs 0) (fe51ValAt self_bs 40) (fe51ValAt self_bs 80)⌝ }

/-- `<&EdwardsPoint as Add<&AffineNielsPoint>>::add` (`Blk08`, 152 insns, stack 528). -/
abbrev edwardsPointAddAffineNielsSpec : Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
{
  pre :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 : State) =>
    match x with
    | (out, self, other, out_bs, self_bs, other_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = self ∧
              s0.readReg64 Reg.x1 = other ∧
                out_bs.length = 160 ∧
                  self_bs.length = 160 ∧
                    other_bs.length = 120 ∧
                      fe51LimbsBoundedAt self_bs 0 (2 ^ 53) ∧
                        fe51LimbsBoundedAt self_bs 40 (2 ^ 53) ∧
                          fe51LimbsBoundedAt self_bs 80 (2 ^ 52) ∧
                            fe51LimbsBoundedAt self_bs 120 (2 ^ 54) ∧
                              fe51LimbsBoundedAt other_bs 0 (2 ^ 54) ∧
                                fe51LimbsBoundedAt other_bs 40 (2 ^ 54) ∧ fe51LimbsBoundedAt other_bs 80 (2 ^ 54)⌝ ∗
        self ↦ₛ self_bs ∗ other ↦ₛ other_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 528,
  post :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 sf : State) =>
    match x with
    | (out, self, other, out_bs, self_bs, other_bs) =>
      self ↦ₛ self_bs ∗
        other ↦ₛ other_bs ∗
          stackFrame sf 528 ∗
            ∃∗ res_bs : List (BitVec 8),
              out ↦ₛ res_bs ∗
                ⌜res_bs.length = 160 ∧
                    fe51LimbsBoundedAt res_bs 0 (2 ^ 52) ∧
                      fe51LimbsBoundedAt res_bs 40 (2 ^ 53) ∧
                        fe51LimbsBoundedAt res_bs 80 (2 ^ 54) ∧
                          fe51LimbsBoundedAt res_bs 120 (2 ^ 52) ∧
                            edExtOfBytes res_bs =
                              edAddAffineNiels (edExtOfBytes self_bs)
                                (fe51ValAt other_bs 0 % p25519)
                                (fe51ValAt other_bs 40 % p25519)
                                (fe51ValAt other_bs 80 % p25519)⌝ }

/-- `<EdwardsPoint>::mul_by_pow_2` (`Blk09`, 79 insns, stack 912, `k = 4#32` specialization). -/
abbrev edwardsPointMulByPow2_4Spec : Spec
  (BitVec 64 × BitVec 64 × BitVec 32 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × BitVec 32 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, self, k, out_bs, self_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = self ∧
              s0.readReg32 Reg.x1 = k ∧ out_bs.length = 160 ∧ fe51Point4Bounded self_bs (2 ^ 53) ∧ k = 4#32⌝ ∗
        self ↦ₛ self_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 912,
  post := fun (x : BitVec 64 × BitVec 64 × BitVec 32 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, self, k, out_bs, self_bs) =>
      self ↦ₛ self_bs ∗
        stackFrame sf 912 ∗
          ∃∗ res_bs : List (BitVec 8),
            out ↦ₛ res_bs ∗
              ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧ edExtOfBytes res_bs = edDouble4 (edExtOfBytes self_bs)⌝ }

/-- `<EdwardsPoint>::to_montgomery` (`Blk10`, 171 insns, stack 1392). -/
abbrev edwardsPointToMontgomerySpec : Spec
  (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, self, out_bs, self_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = self ∧ out_bs.length = 32 ∧ fe51Point4Bounded self_bs (2 ^ 53)⌝ ∗
        self ↦ₛ self_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 1392,
  post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, self, out_bs, self_bs) =>
      self ↦ₛ self_bs ∗
        stackFrame sf 1392 ∗
          out ↦ₛ natToLeBytes 32 (edExtToMontgomeryU (edExtOfBytes self_bs)) }

/-- `<montgomery::ProjectivePoint>::as_affine` (`Blk11`, 130 insns, stack 1312). -/
abbrev montProjectiveAsAffineSpec : Spec
  (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
    match x with
    | (out, self, out_bs, self_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = self ∧ out_bs.length = 32 ∧ montProjBounded self_bs (2 ^ 54)⌝ ∗
        self ↦ₛ self_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 1312,
  post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
    match x with
    | (out, self, out_bs, self_bs) =>
      self ↦ₛ self_bs ∗
        stackFrame sf 1312 ∗
          out ↦ₛ
            natToLeBytes 32
              (fpMul (montProjOfBytes self_bs).U
                (fpInv (montProjOfBytes self_bs).W)) }

/-- `montgomery::differential_add_and_double` (`Blk12`, 238 insns, stack 1056). -/
abbrev montDiffAddAndDoubleSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 : State) =>
      match x with
      | (P, Q, u1, p_bs, q_bs, u1_bs) =>
        ⌜s0.readReg64 Reg.x0 = P ∧
              s0.readReg64 Reg.x1 = Q ∧
                s0.readReg64 Reg.x2 = u1 ∧
                  montProjBounded p_bs (2 ^ 53) ∧ montProjBounded q_bs (2 ^ 53) ∧ fe51LimbsBounded u1_bs (2 ^ 54)⌝ ∗
          u1 ↦ₛ u1_bs ∗ fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗ P ↦ₛ p_bs ∗ Q ↦ₛ q_bs ∗ stackFrame s0 1056,
    post :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 sf : State) =>
      match x with
      | (P, Q, u1, p_bs, q_bs, u1_bs) =>
        u1 ↦ₛ u1_bs ∗
          fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗
            stackFrame sf 1056 ∗
              ∃∗ p_out : List (BitVec 8),
                ∃∗ q_out : List (BitVec 8),
                  P ↦ₛ p_out ∗
                    Q ↦ₛ q_out ∗
                      ⌜montProjBounded p_out (2 ^ 52) ∧
                          montProjBounded q_out (2 ^ 52) ∧
                            montProjOfBytes p_out =
                                (montDiffAddAndDouble
                                    (fe51ValOfBytes u1_bs % p25519) (montProjOfBytes p_bs)
                                    (montProjOfBytes q_bs)).fst ∧
                              montProjOfBytes q_out =
                                (montDiffAddAndDouble
                                    (fe51ValOfBytes u1_bs % p25519) (montProjOfBytes p_bs)
                                    (montProjOfBytes q_bs)).snd⌝ }

/-- `<EdwardsBasepointTable as BasepointTable>::mul_base` (`Blk13`, 167 insns, stack 1680). -/
abbrev edwardsBasepointTableMulBaseSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 : State) =>
      match x with
      | (out, table, scalar, out_bs, table_bs, scalar_bs) =>
        ⌜s0.readReg64 Reg.x8 = out ∧
              s0.readReg64 Reg.x0 = table ∧
                s0.readReg64 Reg.x1 = scalar ∧
                  out_bs.length = 160 ∧
                    fe51BasepointTable32Bounded table_bs (2 ^ 53) ∧
                      scalar_bs.length = 32 ∧ (scalar_bs.getD 31 0#8).toNat ≤ 127⌝ ∗
          table ↦ᵣ table_bs ∗
            scalar ↦ₛ scalar_bs ∗ fe51_one mpl ↦ᵣ fe51OneBytes ∗ out ↦ₛ out_bs ∗ stackFrame s0 1680,
    post :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 sf : State) =>
      match x with
      | (out, table, scalar, out_bs, table_bs, scalar_bs) =>
        table ↦ᵣ table_bs ∗
          scalar ↦ₛ scalar_bs ∗
            fe51_one mpl ↦ᵣ fe51OneBytes ∗
              stackFrame sf 1680 ∗
                ∃∗ res_bs : List (BitVec 8),
                  out ↦ₛ res_bs ∗
                    ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧ edExtOfBytes res_bs = edMulBase table_bs scalar_bs⌝ }

/-- `<EdwardsPoint>::mul_base_clamped` (`Blk14`, 11 insns, stack 1680). -/
abbrev edwardsPointMulBaseClampedSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
      match x with
      | (out, bytes, out_bs, bytes_bs) =>
        ⌜s0.readReg64 Reg.x8 = out ∧
              s0.readReg64 Reg.x0 = bytes ∧ out_bs.length = 160 ∧ bytes_bs.length = 32⌝ ∗
          ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes ∗
            fe51_one mpl ↦ᵣ fe51OneBytes ∗ out ↦ₛ out_bs ∗ bytes ↦ₛ bytes_bs ∗ stackFrame s0 1680,
    post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
      match x with
      | (out, bytes, out_bs, bytes_bs) =>
        ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes ∗
          fe51_one mpl ↦ᵣ fe51OneBytes ∗
            stackFrame sf 1680 ∗
              ∃∗ res_bs : List (BitVec 8),
                have clamped := clampScalarBytes bytes_bs;
                out ↦ₛ res_bs ∗
                  bytes ↦ₛ clamped ∗
                    ⌜fe51Point4Bounded res_bs (2 ^ 52) ∧
                        edExtOfBytes res_bs = edMulBase ed25519BasepointTableBytes clamped⌝ }

/-- `<&MontgomeryPoint as Mul<&Scalar>>::mul` (`Blk15`, 211 insns, stack 1680). -/
abbrev montgomeryPointMulSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 : State) =>
      match x with
      | (out, self, scalar, out_bs, self_bs, scalar_bs) =>
        ⌜s0.readReg64 Reg.x8 = out ∧
              s0.readReg64 Reg.x0 = self ∧
                s0.readReg64 Reg.x1 = scalar ∧ out_bs.length = 32 ∧ self_bs.length = 32 ∧ scalar_bs.length = 32⌝ ∗
          self ↦ₛ self_bs ∗
            scalar ↦ₛ scalar_bs ∗
              fe51_one mpl ↦ᵣ fe51OneBytes ∗
                fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗ out ↦ₛ out_bs ∗ stackFrame s0 1680,
    post :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 sf : State) =>
      match x with
      | (out, self, scalar, out_bs, self_bs, scalar_bs) =>
        self ↦ₛ self_bs ∗
          scalar ↦ₛ scalar_bs ∗
            fe51_one mpl ↦ᵣ fe51OneBytes ∗
              fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗
                stackFrame sf 1680 ∗
                  out ↦ₛ
                    natToLeBytes 32
                      (have u1 := decodeU255 self_bs % p25519;
                      have res :=
                        montLadderLoop 255 (leBytesToNat scalar_bs) u1
                          { U := 1, W := 0 } { U := u1, W := 1 };
                      fpMul res.U (fpInv res.W)) }

/-- `<MontgomeryPoint>::mul_clamped` (`Blk16`, 17 insns, stack 1728). -/
abbrev montgomeryPointMulClampedSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 : State) =>
      match x with
      | (out, self, bytes, out_bs, self_bs, bytes_bs) =>
        ⌜s0.readReg64 Reg.x8 = out ∧
              s0.readReg64 Reg.x0 = self ∧
                s0.readReg64 Reg.x1 = bytes ∧ out_bs.length = 32 ∧ self_bs.length = 32 ∧ bytes_bs.length = 32⌝ ∗
          self ↦ₛ self_bs ∗
            fe51_one mpl ↦ᵣ fe51OneBytes ∗
              fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗ out ↦ₛ out_bs ∗ bytes ↦ₛ bytes_bs ∗ stackFrame s0 1728,
    post :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 sf : State) =>
      match x with
      | (out, self, bytes, out_bs, self_bs, bytes_bs) =>
        self ↦ₛ self_bs ∗
          fe51_one mpl ↦ᵣ fe51OneBytes ∗
            fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗
              stackFrame sf 1728 ∗
                out ↦ₛ x25519 bytes_bs self_bs ∗
                  bytes ↦ₛ clampScalarBytes bytes_bs }

/-- `<StaticSecret>::diffie_hellman` (`Blk17`, 13 insns, stack 1808). -/
abbrev staticSecretDiffieHellmanSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 : State) =>
      match x with
      | (out, self, theirPublic, out_bs, self_bs, pub_bs) =>
        ⌜s0.readReg64 Reg.x8 = out ∧
              s0.readReg64 Reg.x0 = self ∧
                s0.readReg64 Reg.x1 = theirPublic ∧
                  out_bs.length = 32 ∧ self_bs.length = 32 ∧ pub_bs.length = 32⌝ ∗
          self ↦ₛ self_bs ∗
            theirPublic ↦ₛ pub_bs ∗
              fe51_one mpl ↦ᵣ fe51OneBytes ∗
                fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗ out ↦ₛ out_bs ∗ stackFrame s0 1808,
    post :=
      fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
        (s0 sf : State) =>
      match x with
      | (out, self, theirPublic, out_bs, self_bs, pub_bs) =>
        self ↦ₛ self_bs ∗
          theirPublic ↦ₛ pub_bs ∗
            fe51_one mpl ↦ᵣ fe51OneBytes ∗
              fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes ∗
                stackFrame sf 1808 ∗ out ↦ₛ x25519 self_bs pub_bs }

/-- `<PublicKey as From<&StaticSecret>>::from` (`Blk18`, 17 insns, stack 1904). -/
abbrev publicKeyFromSecretSpec : Obj.MultiPlacement →
  Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
fun (mpl : Obj.MultiPlacement) =>
  {
    pre := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 : State) =>
      match x with
      | (out, secret, out_bs, secret_bs) =>
        ⌜s0.readReg64 Reg.x8 = out ∧
              s0.readReg64 Reg.x0 = secret ∧ out_bs.length = 32 ∧ secret_bs.length = 32⌝ ∗
          secret ↦ₛ secret_bs ∗
            ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes ∗
              fe51_one mpl ↦ᵣ fe51OneBytes ∗ out ↦ₛ out_bs ∗ stackFrame s0 1904,
    post := fun (x : BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s0 sf : State) =>
      match x with
      | (out, secret, out_bs, secret_bs) =>
        secret ↦ₛ secret_bs ∗
          ed25519_basepoint_table mpl ↦ᵣ ed25519BasepointTableBytes ∗
            fe51_one mpl ↦ᵣ fe51OneBytes ∗
              stackFrame sf 1904 ∗ out ↦ₛ x25519Pubkey secret_bs }

end X25519Dalek


