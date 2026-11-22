-- Prove2me | Definitions.Def_Arm64_ISA_Float
-- name    : Arm64_ISA_Float
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:03:24.402151+00:00
-- url     : https://prove2.me/theorems/7b1fb954-828b-4678-9871-f4707ea197ea
-- title:
--   Arm64.Trusted.ISA.Float — IEEE-754 AArch64 Scalar Floating-Point Semantics
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/ISA/Float.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Float.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/ISA/Float.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/ISA/Float.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/ISA/Float.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_State

/-!
# IEEE-754 AArch64 Scalar Floating-Point Semantics

Computable, bit-exact IEEE-754 `binary32` (`BitVec 32`) and `binary64` (`BitVec 64`) scalar
floating-point semantics under default `FPCR = 0` (`FZ = 0`, `DN = 0`, untrapped `FPSR` exception
accumulation, tininess detected before rounding). Defines format-parametric unpacking
(`FpFormat.unpackFp`), dyadic rounding (`roundDyadic`) across all five `FpRoundMode` modes,
arithmetic, comparison, and conversion operations, and 32/64-bit instruction wrappers.
-/

@[expose] public section

namespace Arm64

/-- IEEE-754 / ARMv8-A floating-point rounding modes (`FPRounding`). -/
inductive FpRoundMode where
  /-- Round to Nearest, ties to Even (`RNE`, `rmode = 0b00`). -/
  | RNE
  /-- Round towards Plus Infinity (`RTP`, `rmode = 0b01`). -/
  | RTP
  /-- Round towards Minus Infinity (`RTN`, `rmode = 0b10`). -/
  | RTN
  /-- Round towards Zero (`RTZ`, `rmode = 0b11`). -/
  | RTZ
  /-- Round to Nearest, ties Away from zero (`RNA`, `FRINTA` / `FCVTAS` / `FCVTAU`). -/
  | RNA
  deriving DecidableEq, Repr

/-- Decode a 2-bit architectural rounding mode (`00=RNE, 01=RTP, 10=RTN, 11=RTZ`). -/
def FpRoundMode.ofBits2 (rmode : BitVec 2) : FpRoundMode :=
  match rmode.toNat with
  | 0 => .RNE
  | 1 => .RTP
  | 2 => .RTN
  | _ => .RTZ

/-- Format parameters for an IEEE-754 binary floating-point format. -/
structure FpFormat where
  expBits  : Nat
  fracBits : Nat
  deriving DecidableEq, Repr

/-- IEEE-754 single-precision (`binary32`: 8 exponent bits, 23 fraction bits). -/
def fpFormat32 : FpFormat := { expBits := 8, fracBits := 23 }

/-- IEEE-754 double-precision (`binary64`: 11 exponent bits, 52 fraction bits). -/
def fpFormat64 : FpFormat := { expBits := 11, fracBits := 52 }

/-- Architectural category of an unpacked IEEE-754 operand (`FPUnpack` with `FZ = 0`). -/
inductive UnpackedFp where
  | nan (signaling : Bool)
  | inf (sign : Bool)
  | zero (sign : Bool)
  | finite (sign : Bool) (sig : Nat) (exp2 : Int)
  deriving DecidableEq, Repr

namespace FpFormat

/-- Total bit width (`1 + expBits + fracBits`). -/
def width (fmt : FpFormat) : Nat := 1 + fmt.expBits + fmt.fracBits

/-- Maximum biased exponent (`2^expBits - 1`: `255` for binary32, `2047` for binary64). -/
def maxExp (fmt : FpFormat) : Nat := (1 <<< fmt.expBits) - 1

/-- Exponent bias (`2^(expBits - 1) - 1`: `127` for binary32, `1023` for binary64). -/
def bias (fmt : FpFormat) : Int := Int.ofNat ((1 <<< (fmt.expBits - 1)) - 1)

/-- Minimum ULP base-2 exponent (`1 - bias - fracBits`: `-149` for binary32, `-1074` for binary64). -/
def minExp2 (fmt : FpFormat) : Int := 1 - fmt.bias - Int.ofNat fmt.fracBits

/-- Maximum normal ULP base-2 exponent (`(maxExp - 1) - bias - fracBits`: `104` for binary32, `971` for binary64). -/
def maxExp2 (fmt : FpFormat) : Int := Int.ofNat (fmt.maxExp - 1) - fmt.bias - Int.ofNat fmt.fracBits

/-- Pack `(sign, biasedExp, frac)` into a raw `Nat` bit pattern. -/
def packNat (fmt : FpFormat) (sign : Bool) (biasedExp : Nat) (frac : Nat) : Nat :=
  let s := if sign then (1 <<< (fmt.expBits + fmt.fracBits)) else 0
  let e := (biasedExp % (1 <<< fmt.expBits)) <<< fmt.fracBits
  let m := frac % (1 <<< fmt.fracBits)
  s ||| e ||| m

/-- Pack signed zero (`±0.0`). -/
def packZero (fmt : FpFormat) (sign : Bool) : Nat :=
  fmt.packNat sign 0 0

/-- Pack signed infinity (`±Inf`). -/
def packInf (fmt : FpFormat) (sign : Bool) : Nat :=
  fmt.packNat sign fmt.maxExp 0

/-- Pack maximum finite float with given sign (`±maxFinite`). -/
def packMaxFinite (fmt : FpFormat) (sign : Bool) : Nat :=
  fmt.packNat sign (fmt.maxExp - 1) ((1 <<< fmt.fracBits) - 1)

/-- Architectural default quiet NaN (`FPDefaultNaN`, `DN = 0`): `0x7fc00000` or `0x7ff8000000000000`. -/
def defaultNaN (fmt : FpFormat) : Nat :=
  fmt.packNat false fmt.maxExp (1 <<< (fmt.fracBits - 1))

/-- Quiet a NaN bit pattern by setting the MSB of the fraction (`fracBits - 1`). -/
def quietNaN (fmt : FpFormat) (raw : Nat) : Nat :=
  raw ||| (1 <<< (fmt.fracBits - 1))

/-- Extract `(sign, biasedExp, frac)` from a raw `Nat` bit pattern. -/
def unpackRaw (fmt : FpFormat) (raw : Nat) : Bool × Nat × Nat :=
  let sign := ((raw >>> (fmt.expBits + fmt.fracBits)) &&& 1) != 0
  let exp := (raw >>> fmt.fracBits) &&& ((1 <<< fmt.expBits) - 1)
  let frac := raw &&& ((1 <<< fmt.fracBits) - 1)
  (sign, exp, frac)

/-- Check if raw bit pattern is a NaN (`exp == maxExp && frac != 0`). -/
def isNaNRaw (fmt : FpFormat) (raw : Nat) : Bool :=
  let (_, exp, frac) := fmt.unpackRaw raw
  exp == fmt.maxExp && frac != 0

/-- Check if raw bit pattern is a signaling NaN (`exp == maxExp && frac != 0 && quietBit == 0`). -/
def isSignalingNaNRaw (fmt : FpFormat) (raw : Nat) : Bool :=
  let (_, exp, frac) := fmt.unpackRaw raw
  exp == fmt.maxExp && frac != 0 && ((frac >>> (fmt.fracBits - 1)) &&& 1) == 0

/-- Check if raw bit pattern is a quiet NaN (`exp == maxExp && quietBit == 1`). -/
def isQuietNaNRaw (fmt : FpFormat) (raw : Nat) : Bool :=
  let (_, exp, frac) := fmt.unpackRaw raw
  exp == fmt.maxExp && ((frac >>> (fmt.fracBits - 1)) &&& 1) != 0

/-- Check if raw bit pattern is `±Inf` (`exp == maxExp && frac == 0`). -/
def isInfRaw (fmt : FpFormat) (raw : Nat) : Bool :=
  let (_, exp, frac) := fmt.unpackRaw raw
  exp == fmt.maxExp && frac == 0

/-- Check if raw bit pattern is `±0.0` (`exp == 0 && frac == 0`). -/
def isZeroRaw (fmt : FpFormat) (raw : Nat) : Bool :=
  let (_, exp, frac) := fmt.unpackRaw raw
  exp == 0 && frac == 0

/-- Extract `(sign, sig, exp2)` for a finite non-zero float such that value is `(-1)^sign * sig * 2^exp2`. -/
def unpackFinite (fmt : FpFormat) (raw : Nat) : Bool × Nat × Int :=
  let (sign, exp, frac) := fmt.unpackRaw raw
  if exp == 0 then
    (sign, frac, fmt.minExp2)
  else
    (sign, (1 <<< fmt.fracBits) ||| frac, Int.ofNat exp - fmt.bias - Int.ofNat fmt.fracBits)

/-- Unpack a `fmt.width`-bit IEEE-754 float into its exact architectural category (`FPUnpack`). -/
def unpackFp (fmt : FpFormat) (x : BitVec fmt.width) : UnpackedFp :=
  let raw := x.toNat
  let (sign, exp, frac) := fmt.unpackRaw raw
  if exp == fmt.maxExp then
    if frac == 0 then .inf sign
    else .nan (((frac >>> (fmt.fracBits - 1)) &&& 1) == 0)
  else if exp == 0 && frac == 0 then
    .zero sign
  else
    let (s, sig, exp2) := fmt.unpackFinite raw
    .finite s sig exp2

end FpFormat

/-- ARMv8-A `FPProcessNaNs` (`DN = 0`): propagates the first signaling `NaN` (quieting it and
    raising `fpsrIOC`), else the first quiet `NaN` (with `0#32`), or returns `none`. -/
def processNaNs2 (fmt : FpFormat) (a b : BitVec fmt.width) : Option (BitVec fmt.width × BitVec 32) :=
  let quietBit := BitVec.ofNat fmt.width (1 <<< (fmt.fracBits - 1))
  match fmt.unpackFp a, fmt.unpackFp b with
  | .nan true, _ => some (a ||| quietBit, fpsrIOC)
  | _, .nan true => some (b ||| quietBit, fpsrIOC)
  | .nan false, _ => some (a, 0#32)
  | _, .nan false => some (b, 0#32)
  | _, _ => none

/-- Decide whether to increment a rounded magnitude given `sign`, `rm`, `isOdd`, `roundBit`, and `stickyBit`. -/
def fpRoundIncrement (sign : Bool) (rm : FpRoundMode) (isOdd roundBit stickyBit : Bool) : Bool :=
  match rm with
  | .RNE => roundBit && (stickyBit || isOdd)
  | .RNA => roundBit
  | .RTP => !sign && (roundBit || stickyBit)
  | .RTN => sign && (roundBit || stickyBit)
  | .RTZ => false

/-- Shift `sig` right by `rshift ≥ 1` bits, returning `(quot, roundBit, stickyBit)` with `stickyIn`
    folded into `stickyBit` and shifts above `maxShift` clamped to `(0, false, (sig != 0) || stickyIn)`. -/
def rshiftWithRoundSticky (maxShift sig rshift : Nat) (stickyIn : Bool) : Nat × Bool × Bool :=
  if rshift > maxShift then
    (0, false, (sig != 0) || stickyIn)
  else
    let q := sig >>> rshift
    let rBit := ((sig >>> (rshift - 1)) &&& 1) != 0
    let sMask := (1 <<< (rshift - 1)) - 1
    let sBit := ((sig &&& sMask) != 0) || stickyIn
    (q, rBit, sBit)

/-- Round an exact dyadic magnitude `(-1)^sign * (sig + stickyIn) * 2^exp2` to `fmt` under `rm`,
    returning `(packedValue, fpsrFlags)` per ARMv8-A `FPRoundBase` (`FPCR = 0`: untrapped, `FZ = 0`,
    tininess detected before rounding). -/
def roundDyadic (fmt : FpFormat) (rm : FpRoundMode) (sign : Bool) (sig : Nat) (exp2 : Int)
    (stickyIn : Bool) : Nat × BitVec 32 :=
  if sig == 0 && !stickyIn then
    (fmt.packZero sign, 0#32)
  else
    let bits : Nat := if sig == 0 then 0 else Nat.log2 sig + 1
    let targetBits : Nat := fmt.fracBits + 1
    let exp2Norm : Int := exp2 + Int.ofNat bits - Int.ofNat targetBits
    let isTiny : Bool := exp2Norm < fmt.minExp2
    let ulpExp2 : Int := if isTiny then fmt.minExp2 else exp2Norm
    let shift : Int := exp2 - ulpExp2
    let (quot, roundBit, stickyBit) : Nat × Bool × Bool :=
      if shift ≥ 0 then
        (sig <<< shift.toNat, false, stickyIn)
      else
        rshiftWithRoundSticky (bits + 1) sig (-shift).toNat stickyIn
    let inexact : Bool := roundBit || stickyBit
    let inc := fpRoundIncrement sign rm ((quot &&& 1) != 0) roundBit stickyBit
    let qRounded := if inc then quot + 1 else quot
    let (qFinal, ulpExp2Final) : Nat × Int :=
      if qRounded ≥ (1 <<< (fmt.fracBits + 1)) then
        (qRounded >>> 1, ulpExp2 + 1)
      else
        (qRounded, ulpExp2)
    if ulpExp2Final > fmt.maxExp2 then
      let val :=
        match rm with
        | .RNE | .RNA => fmt.packInf sign
        | .RTZ => fmt.packMaxFinite sign
        | .RTP => if sign then fmt.packMaxFinite true else fmt.packInf false
        | .RTN => if sign then fmt.packInf true else fmt.packMaxFinite false
      (val, fpsrOFC ||| fpsrIXC)
    else
      let flags : BitVec 32 :=
        (if isTiny && inexact then fpsrUFC else 0#32) |||
        (if inexact then fpsrIXC else 0#32)
      if qFinal < (1 <<< fmt.fracBits) then
        (fmt.packNat sign 0 qFinal, flags)
      else
        let biasedExp := (ulpExp2Final - fmt.minExp2 + 1).toNat
        let frac := qFinal - (1 <<< fmt.fracBits)
        (fmt.packNat sign biasedExp frac, flags)

/-- Add two finite non-zero dyadic numbers `(-1)^signA * sigA * 2^expA` and `(-1)^signB * sigB * 2^expB`
    and round to `fmt` under `rm`, returning `(packedValue, fpsrFlags)`. -/
def addFiniteDyadic (fmt : FpFormat) (rm : FpRoundMode)
    (signA : Bool) (sigA : Nat) (expA : Int)
    (signB : Bool) (sigB : Nat) (expB : Int) : Nat × BitVec 32 :=
  let (s1, m1, e1, s2, m2, e2) :=
    if expA ≥ expB then (signA, sigA, expA, signB, sigB, expB)
    else (signB, sigB, expB, signA, sigA, expA)
  let diff : Nat := (e1 - e2).toNat
  let maxShift : Nat := 2 * fmt.fracBits + 6
  let (m1Aligned, m2Aligned, expAligned, sticky) : Nat × Nat × Int × Bool :=
    if diff ≤ maxShift then
      (m1 <<< diff, m2, e2, false)
    else
      let rshift := diff - maxShift
      let m2Shifted := if rshift > 256 then 0 else m2 >>> rshift
      let st := if rshift > 256 then (m2 != 0) else (m2 &&& ((1 <<< rshift) - 1)) != 0
      (m1 <<< maxShift, m2Shifted, e1 - Int.ofNat maxShift, st)
  if s1 == s2 then
    roundDyadic fmt rm s1 (m1Aligned + m2Aligned) expAligned sticky
  else if !sticky then
    if m1Aligned == m2Aligned then
      (fmt.packZero (rm == .RTN), 0#32)
    else if m1Aligned > m2Aligned then
      roundDyadic fmt rm s1 (m1Aligned - m2Aligned) expAligned false
    else
      roundDyadic fmt rm s2 (m2Aligned - m1Aligned) expAligned false
  else
    roundDyadic fmt rm s1 (m1Aligned - m2Aligned - 1) expAligned true

/-- Exact integer floor square root helper testing bits from `k - 1` down to `0`. -/
def natSqrtBits (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc =>
    let cand := acc + (1 <<< k)
    if cand * cand ≤ n then natSqrtBits n k cand else natSqrtBits n k acc

/-- Exact integer floor square root `⌊√n⌋`. -/
def natSqrt (n : Nat) : Nat :=
  if n == 0 then 0 else natSqrtBits n ((Nat.log2 n) / 2 + 1) 0

/-! ## Format-Generic Operations -/

/-- Format-generic floating-point absolute value (`FABS`). -/
def fpAbs (fmt : FpFormat) (x : BitVec fmt.width) : BitVec fmt.width :=
  x &&& BitVec.ofNat fmt.width ((1 <<< (fmt.expBits + fmt.fracBits)) - 1)

/-- Format-generic floating-point negation (`FNEG`). -/
def fpNeg (fmt : FpFormat) (x : BitVec fmt.width) : BitVec fmt.width :=
  x ^^^ BitVec.ofNat fmt.width (1 <<< (fmt.expBits + fmt.fracBits))

/-- Format-generic `NaN` test (`|x| > +Inf`). -/
def fpIsNaN (fmt : FpFormat) (x : BitVec fmt.width) : Bool :=
  fpAbs fmt x > BitVec.ofNat fmt.width (fmt.maxExp <<< fmt.fracBits)

/-- Format-generic signaling `NaN` test. -/
def fpIsSignalingNaN (fmt : FpFormat) (x : BitVec fmt.width) : Bool :=
  fpIsNaN fmt x && (x &&& BitVec.ofNat fmt.width (1 <<< (fmt.fracBits - 1))) == 0#(fmt.width)

/-- Format-generic `±Inf` test. -/
def fpIsInf (fmt : FpFormat) (x : BitVec fmt.width) : Bool :=
  fpAbs fmt x == BitVec.ofNat fmt.width (fmt.maxExp <<< fmt.fracBits)

/-- Format-generic `±0.0` test. -/
def fpIsZero (fmt : FpFormat) (x : BitVec fmt.width) : Bool :=
  fpAbs fmt x == 0#(fmt.width)

/-- Format-generic ordered IEEE-754 equality (`false` if either is `NaN`; `+0.0 == -0.0`). -/
def fpEq (fmt : FpFormat) (a b : BitVec fmt.width) : Bool :=
  !fpIsNaN fmt a && !fpIsNaN fmt b && ((fpIsZero fmt a && fpIsZero fmt b) || a == b)

/-- Format-generic ordered IEEE-754 strict less-than (`false` if either is `NaN`). -/
def fpLt (fmt : FpFormat) (a b : BitVec fmt.width) : Bool :=
  !fpIsNaN fmt a && !fpIsNaN fmt b && !(fpIsZero fmt a && fpIsZero fmt b) &&
    (if a.msb != b.msb then a.msb
     else if a.msb then fpAbs fmt b < fpAbs fmt a
     else fpAbs fmt a < fpAbs fmt b)

/-- Format-generic IEEE-754 addition (`FADD`) returning `(result, fpsrFlags)`. -/
def fpAdd (fmt : FpFormat) (rm : FpRoundMode) (a b : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  match processNaNs2 fmt a b with
  | some res => res
  | none =>
    match fmt.unpackFp a, fmt.unpackFp b with
    | .inf sA, .inf sB =>
      if sA == sB then (a, 0#32) else (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC)
    | .inf _, _ => (a, 0#32)
    | _, .inf _ => (b, 0#32)
    | .zero sA, .zero sB =>
      let sOut := if sA == sB then sA else (rm == .RTN)
      (BitVec.ofNat fmt.width (fmt.packZero sOut), 0#32)
    | _, .zero _ => (a, 0#32)
    | .zero _, _ => (b, 0#32)
    | .finite sA sigA expA, .finite sB sigB expB =>
      let (raw, flags) := addFiniteDyadic fmt rm sA sigA expA sB sigB expB
      (BitVec.ofNat fmt.width raw, flags)
    | _, _ => (0#(fmt.width), 0#32)

/-- Format-generic IEEE-754 subtraction (`FSUB`) returning `(result, fpsrFlags)`. -/
def fpSub (fmt : FpFormat) (rm : FpRoundMode) (a b : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  match processNaNs2 fmt a b with
  | some res => res
  | none => fpAdd fmt rm a (fpNeg fmt b)

/-- Format-generic IEEE-754 multiplication (`FMUL`) returning `(result, fpsrFlags)`. -/
def fpMul (fmt : FpFormat) (rm : FpRoundMode) (a b : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  match processNaNs2 fmt a b with
  | some res => res
  | none =>
    let signOut := a.msb != b.msb
    match fmt.unpackFp a, fmt.unpackFp b with
    | .inf _, .zero _ | .zero _, .inf _ =>
      (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC)
    | .inf _, _ | _, .inf _ =>
      (BitVec.ofNat fmt.width (fmt.packInf signOut), 0#32)
    | .zero _, _ | _, .zero _ =>
      (BitVec.ofNat fmt.width (fmt.packZero signOut), 0#32)
    | .finite _ sigA expA, .finite _ sigB expB =>
      let (raw, flags) := roundDyadic fmt rm signOut (sigA * sigB) (expA + expB) false
      (BitVec.ofNat fmt.width raw, flags)
    | _, _ => (0#(fmt.width), 0#32)

/-- Format-generic IEEE-754 negated multiplication (`FNMUL`) returning `(result, fpsrFlags)`. -/
def fpNMul (fmt : FpFormat) (rm : FpRoundMode) (a b : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  let res := fpMul fmt rm a b
  (fpNeg fmt res.1, res.2)

/-- Format-generic IEEE-754 division (`FDIV`) returning `(result, fpsrFlags)`. -/
def fpDiv (fmt : FpFormat) (rm : FpRoundMode) (a b : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  match processNaNs2 fmt a b with
  | some res => res
  | none =>
    let signOut := a.msb != b.msb
    match fmt.unpackFp a, fmt.unpackFp b with
    | .inf _, .inf _ | .zero _, .zero _ =>
      (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC)
    | .inf _, _ =>
      (BitVec.ofNat fmt.width (fmt.packInf signOut), 0#32)
    | _, .zero _ =>
      (BitVec.ofNat fmt.width (fmt.packInf signOut), fpsrDZC)
    | .zero _, _ | _, .inf _ =>
      (BitVec.ofNat fmt.width (fmt.packZero signOut), 0#32)
    | .finite _ sigA expA, .finite _ sigB expB =>
      let shift : Nat := 2 * fmt.fracBits + 4
      let num : Nat := sigA <<< shift
      let (raw, flags) := roundDyadic fmt rm signOut (num / sigB) (expA - expB - Int.ofNat shift) (num % sigB != 0)
      (BitVec.ofNat fmt.width raw, flags)
    | _, _ => (0#(fmt.width), 0#32)

/-- Format-generic IEEE-754 square root (`FSQRT`) returning `(result, fpsrFlags)`. -/
def fpSqrt (fmt : FpFormat) (rm : FpRoundMode) (a : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  match fmt.unpackFp a with
  | .nan true => (a ||| BitVec.ofNat fmt.width (1 <<< (fmt.fracBits - 1)), fpsrIOC)
  | .nan false | .zero _ | .inf false => (a, 0#32)
  | .inf true | .finite true _ _ => (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC)
  | .finite false sig exp2 =>
    let bits := Nat.log2 sig + 1
    let minRadBits := 2 * (fmt.fracBits + 3) + 2
    let baseShift := if bits < minRadBits then minRadBits - bits else 0
    let shift := if (exp2 - Int.ofNat baseShift) % 2 == 0 then baseShift else baseShift + 1
    let radicand := sig <<< shift
    let expEven := exp2 - Int.ofNat shift
    let q := natSqrt radicand
    let (raw, flags) := roundDyadic fmt rm false q (expEven / 2) (radicand - q * q != 0)
    (BitVec.ofNat fmt.width raw, flags)

/-- Format-generic IEEE-754 round-to-integral value (`FRINT*`). -/
def fpRintVal (fmt : FpFormat) (rm : FpRoundMode) (a : BitVec fmt.width) : BitVec fmt.width :=
  match fmt.unpackFp a with
  | .nan true => a ||| BitVec.ofNat fmt.width (1 <<< (fmt.fracBits - 1))
  | .nan false | .zero _ | .inf _ => a
  | .finite sign sig exp2 =>
    if exp2 ≥ 0 then a
    else
      let (quot, roundBit, stickyBit) := rshiftWithRoundSticky (fmt.fracBits + 2) sig (-exp2).toNat false
      let inc := fpRoundIncrement sign rm ((quot &&& 1) != 0) roundBit stickyBit
      let intMag := if inc then quot + 1 else quot
      let raw := if intMag == 0 then fmt.packZero sign else (roundDyadic fmt .RNE sign intMag 0 false).1
      BitVec.ofNat fmt.width raw

/-- Format-generic `FPSR` exception flags for `FRINT*` (`IOC` on `sNaN`; `IXC` when `exact` and non-integral). -/
def fpRintFlags (fmt : FpFormat) (exact : Bool) (a : BitVec fmt.width) : BitVec 32 :=
  match fmt.unpackFp a with
  | .nan true => fpsrIOC
  | .nan false | .zero _ | .inf _ => 0#32
  | .finite _ sig exp2 =>
    if !exact || exp2 ≥ 0 then 0#32
    else
      let (_, roundBit, stickyBit) := rshiftWithRoundSticky (fmt.fracBits + 2) sig (-exp2).toNat false
      if roundBit || stickyBit then fpsrIXC else 0#32

/-- Format-generic IEEE-754 round-to-integral (`FRINT*`) returning `(result, fpsrFlags)`. -/
def fpRint (fmt : FpFormat) (rm : FpRoundMode) (exact : Bool) (a : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  (fpRintVal fmt rm a, fpRintFlags fmt exact a)

/-- Format-generic `FMAX` / `FMIN` / `FMAXNM` / `FMINNM` value. -/
def fpMinMaxVal (fmt : FpFormat) (isMax isNum : Bool) (a b : BitVec fmt.width) : BitVec fmt.width :=
  let (a', b') :=
    if isNum && !fpIsSignalingNaN fmt a && !fpIsSignalingNaN fmt b then
      if fpIsNaN fmt a && !fpIsNaN fmt b then (b, b)
      else if fpIsNaN fmt b && !fpIsNaN fmt a then (a, a)
      else (a, b)
    else
      (a, b)
  match processNaNs2 fmt a' b' with
  | some (nan, _) => nan
  | none =>
    if fpIsZero fmt a' && fpIsZero fmt b' then
      let sOut := if isMax then (a'.msb && b'.msb) else (a'.msb || b'.msb)
      BitVec.ofNat fmt.width (fmt.packZero sOut)
    else if isMax then
      if fpLt fmt b' a' then a' else b'
    else
      if fpLt fmt a' b' then a' else b'

/-- Format-generic `FMAX` / `FMIN` / `FMAXNM` / `FMINNM` returning `(result, fpsrFlags)`. -/
def fpMinMax (fmt : FpFormat) (isMax isNum : Bool) (a b : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  (fpMinMaxVal fmt isMax isNum a b,
   if fpIsSignalingNaN fmt a || fpIsSignalingNaN fmt b then fpsrIOC else 0#32)

/-- Format-generic IEEE-754 single-rounding fused multiply-add (`addend + x * y`) returning `(result, fpsrFlags)`. -/
def fpFma (fmt : FpFormat) (rm : FpRoundMode) (addend x y : BitVec fmt.width) :
    BitVec fmt.width × BitVec 32 :=
  let quietBit := BitVec.ofNat fmt.width (1 <<< (fmt.fracBits - 1))
  let infZeroInvalid :=
    (fpIsInf fmt x && fpIsZero fmt y) || (fpIsZero fmt x && fpIsInf fmt y)
  if fpIsSignalingNaN fmt addend then
    (addend ||| quietBit, fpsrIOC)
  else if fpIsSignalingNaN fmt x then
    (x ||| quietBit, fpsrIOC)
  else if fpIsSignalingNaN fmt y then
    (y ||| quietBit, fpsrIOC)
  else if fpIsNaN fmt addend then
    if infZeroInvalid then (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC) else (addend, 0#32)
  else if fpIsNaN fmt x then
    (x, 0#32)
  else if fpIsNaN fmt y then
    (y, 0#32)
  else if infZeroInvalid then
    (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC)
  else
    let signP := x.msb != y.msb
    if fpIsInf fmt x || fpIsInf fmt y then
      if fpIsInf fmt addend then
        if addend.msb == signP then (BitVec.ofNat fmt.width (fmt.packInf signP), 0#32)
        else (BitVec.ofNat fmt.width fmt.defaultNaN, fpsrIOC)
      else
        (BitVec.ofNat fmt.width (fmt.packInf signP), 0#32)
    else if fpIsInf fmt addend then
      (addend, 0#32)
    else if fpIsZero fmt x || fpIsZero fmt y then
      if fpIsZero fmt addend then
        let sOut := if addend.msb == signP then addend.msb else (rm == .RTN)
        (BitVec.ofNat fmt.width (fmt.packZero sOut), 0#32)
      else
        (addend, 0#32)
    else if fpIsZero fmt addend then
      fpMul fmt rm x y
    else
      let (_, sig1, exp1) := fmt.unpackFinite x.toNat
      let (_, sig2, exp2) := fmt.unpackFinite y.toNat
      let (_, sigA, expA) := fmt.unpackFinite addend.toNat
      let (raw, flags) := addFiniteDyadic fmt rm addend.msb sigA expA signP (sig1 * sig2) (exp1 + exp2)
      (BitVec.ofNat fmt.width raw, flags)

/-- Format-generic floating-point precision conversion (`FCVT`, `src → dst`) returning `(result, fpsrFlags)`. -/
def fpConvert (src dst : FpFormat) (rm : FpRoundMode) (x : BitVec src.width) :
    BitVec dst.width × BitVec 32 :=
  let (sign, _, frac) := src.unpackRaw x.toNat
  match src.unpackFp x with
  | .nan signaling =>
    let qfrac :=
      if dst.fracBits ≥ src.fracBits then
        (frac ||| (1 <<< (src.fracBits - 1))) <<< (dst.fracBits - src.fracBits)
      else
        (frac >>> (src.fracBits - dst.fracBits)) ||| (1 <<< (dst.fracBits - 1))
    (BitVec.ofNat dst.width (dst.packNat sign dst.maxExp qfrac), if signaling then fpsrIOC else 0#32)
  | .inf _ => (BitVec.ofNat dst.width (dst.packInf sign), 0#32)
  | .zero _ => (BitVec.ofNat dst.width (dst.packZero sign), 0#32)
  | .finite _ sig exp2 =>
    let (rawOut, flags) := roundDyadic dst rm sign sig exp2 false
    (BitVec.ofNat dst.width rawOut, flags)

/-- Format-generic ARMv8-A `FPToFixed` returning `(result, fpsrFlags)` (`IOC` on `NaN`/`±Inf`/out-of-range
    without `IXC`; `IXC` when in-range and inexact). -/
def fpToInt (fmt : FpFormat) (intWidth : Nat) (unsigned : Bool) (rm : FpRoundMode)
    (fbits : Nat) (x : BitVec fmt.width) : BitVec intWidth × BitVec 32 :=
  let minInt : Int := if unsigned then 0 else -Int.ofNat (1 <<< (intWidth - 1))
  let maxInt : Int :=
    if unsigned then Int.ofNat ((1 <<< intWidth) - 1)
    else Int.ofNat ((1 <<< (intWidth - 1)) - 1)
  let clampToBv (v : Int) : BitVec intWidth :=
    let clamped : Int := if v < minInt then minInt else if v > maxInt then maxInt else v
    if unsigned then BitVec.ofNat intWidth clamped.toNat else BitVec.ofInt intWidth clamped
  match fmt.unpackFp x with
  | .nan _ => (0#(intWidth), fpsrIOC)
  | .inf sign => (clampToBv (if sign then minInt else maxInt), fpsrIOC)
  | .zero _ => (0#(intWidth), 0#32)
  | .finite sign sig exp2 =>
    let e : Int := exp2 + Int.ofNat fbits
    if e ≥ 0 then
      if e > 70 then
        (clampToBv (if sign then minInt else maxInt), fpsrIOC)
      else
        let mag : Nat := sig <<< e.toNat
        let val : Int := if sign then -Int.ofNat mag else Int.ofNat mag
        (clampToBv val, if val < minInt || val > maxInt then fpsrIOC else 0#32)
    else
      let (quot, roundBit, stickyBit) := rshiftWithRoundSticky 120 sig (-e).toNat false
      let inc := fpRoundIncrement sign rm ((quot &&& 1) != 0) roundBit stickyBit
      let mag := if inc then quot + 1 else quot
      let val : Int := if sign then -Int.ofNat mag else Int.ofNat mag
      let flags :=
        if val < minInt || val > maxInt then fpsrIOC
        else if roundBit || stickyBit then fpsrIXC
        else 0#32
      (clampToBv val, flags)

/-- Format-generic ARMv8-A `FixedToFP` (`SCVTF`/`UCVTF`) returning `(result, fpsrFlags)`. -/
def fixedToFp (fmt : FpFormat) {intWidth : Nat} (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat)
    (x : BitVec intWidth) : BitVec fmt.width × BitVec 32 :=
  if x == 0#(intWidth) then
    (BitVec.ofNat fmt.width (fmt.packZero false), 0#32)
  else
    let sign : Bool := if unsigned then false else x.msb
    let mag : Nat := if !unsigned && x.msb then (0#(intWidth) - x).toNat else x.toNat
    let (raw, flags) := roundDyadic fmt rm sign mag (-Int.ofNat fbits) false
    (BitVec.ofNat fmt.width raw, flags)

/-- Format-generic scalar floating-point comparison (`FCMP`/`FCMPE`, `FCCMP`/`FCCMPE`) returning `(PState, fpsrFlags)`. -/
def fpCmp (fmt : FpFormat) (signalNaN : Bool) (a b : BitVec fmt.width) : PState × BitVec 32 :=
  let pstate : PState :=
    if fpIsNaN fmt a || fpIsNaN fmt b then
      { n := false, z := false, c := true, v := true }
    else if fpEq fmt a b then
      { n := false, z := true, c := true, v := false }
    else if fpLt fmt a b then
      { n := true, z := false, c := false, v := false }
    else
      { n := false, z := false, c := true, v := false }
  let flags : BitVec 32 :=
    if signalNaN then
      if fpIsNaN fmt a || fpIsNaN fmt b then fpsrIOC else 0#32
    else
      if fpIsSignalingNaN fmt a || fpIsSignalingNaN fmt b then fpsrIOC else 0#32
  (pstate, flags)

/-- Format-generic 1-source scalar dispatch (`FMOV`, `FABS`, `FNEG`, `FSQRT`, `FRINT*`). -/
def fp1Op (fmt : FpFormat) (opcode : BitVec 6) (x : BitVec fmt.width) : BitVec fmt.width × BitVec 32 :=
  match opcode.toNat with
  | 0x00 => (x, 0#32)
  | 0x01 => (fpAbs fmt x, 0#32)
  | 0x02 => (fpNeg fmt x, 0#32)
  | 0x03 => fpSqrt fmt .RNE x
  | 0x08 => fpRint fmt .RNE false x
  | 0x09 => fpRint fmt .RTP false x
  | 0x0a => fpRint fmt .RTN false x
  | 0x0b => fpRint fmt .RTZ false x
  | 0x0c => fpRint fmt .RNA false x
  | 0x0e => fpRint fmt .RNE true x
  | 0x0f => fpRint fmt .RNE false x
  | _    => (x, 0#32)

/-- Format-generic 2-source scalar dispatch (`FMUL`, `FDIV`, `FADD`, `FSUB`, `FMAX*`, `FMIN*`, `FNMUL`). -/
def fp2Op (fmt : FpFormat) (opcode : BitVec 4) (a b : BitVec fmt.width) : BitVec fmt.width × BitVec 32 :=
  match opcode.toNat with
  | 0x0 => fpMul fmt .RNE a b
  | 0x1 => fpDiv fmt .RNE a b
  | 0x2 => fpAdd fmt .RNE a b
  | 0x3 => fpSub fmt .RNE a b
  | 0x4 => fpMinMax fmt true false a b
  | 0x5 => fpMinMax fmt false false a b
  | 0x6 => fpMinMax fmt true true a b
  | 0x7 => fpMinMax fmt false true a b
  | 0x8 => fpNMul fmt .RNE a b
  | _   => (0#(fmt.width), 0#32)

/-- Format-generic 3-source scalar dispatch (`FMADD`, `FMSUB`, `FNMADD`, `FNMSUB`). -/
def fp3Op (fmt : FpFormat) (o1 o0 : Bool) (vn vm va : BitVec fmt.width) : BitVec fmt.width × BitVec 32 :=
  let addend := if o1 then fpNeg fmt va else va
  let op1 := if o1 != o0 then fpNeg fmt vn else vn
  fpFma fmt .RNE addend op1 vm

/-! ## 32-bit and 64-bit Instruction Wrappers -/

def fpAbs32 (x : BitVec 32) : BitVec 32 := fpAbs fpFormat32 x
def fpAbs64 (x : BitVec 64) : BitVec 64 := fpAbs fpFormat64 x
def fpNeg32 (x : BitVec 32) : BitVec 32 := fpNeg fpFormat32 x
def fpNeg64 (x : BitVec 64) : BitVec 64 := fpNeg fpFormat64 x
def fpIsNaN32 (x : BitVec 32) : Bool := fpIsNaN fpFormat32 x
def fpIsNaN64 (x : BitVec 64) : Bool := fpIsNaN fpFormat64 x
def fpIsSignalingNaN32 (x : BitVec 32) : Bool := fpIsSignalingNaN fpFormat32 x
def fpIsSignalingNaN64 (x : BitVec 64) : Bool := fpIsSignalingNaN fpFormat64 x
def fpIsInf32 (x : BitVec 32) : Bool := fpIsInf fpFormat32 x
def fpIsInf64 (x : BitVec 64) : Bool := fpIsInf fpFormat64 x
def fpIsZero32 (x : BitVec 32) : Bool := fpIsZero fpFormat32 x
def fpIsZero64 (x : BitVec 64) : Bool := fpIsZero fpFormat64 x
def fpEq32 (a b : BitVec 32) : Bool := fpEq fpFormat32 a b
def fpEq64 (a b : BitVec 64) : Bool := fpEq fpFormat64 a b
def fpLt32 (a b : BitVec 32) : Bool := fpLt fpFormat32 a b
def fpLt64 (a b : BitVec 64) : Bool := fpLt fpFormat64 a b

def fpAdd32 (a b : BitVec 32) : BitVec 32 := (fpAdd fpFormat32 .RNE a b).1
def fpAdd64 (a b : BitVec 64) : BitVec 64 := (fpAdd fpFormat64 .RNE a b).1
def fpAdd32Flags (a b : BitVec 32) : BitVec 32 := (fpAdd fpFormat32 .RNE a b).2
def fpAdd64Flags (a b : BitVec 64) : BitVec 32 := (fpAdd fpFormat64 .RNE a b).2

def fpSub32 (a b : BitVec 32) : BitVec 32 := (fpSub fpFormat32 .RNE a b).1
def fpSub64 (a b : BitVec 64) : BitVec 64 := (fpSub fpFormat64 .RNE a b).1
def fpSub32Flags (a b : BitVec 32) : BitVec 32 := (fpSub fpFormat32 .RNE a b).2
def fpSub64Flags (a b : BitVec 64) : BitVec 32 := (fpSub fpFormat64 .RNE a b).2

def fpMul32 (a b : BitVec 32) : BitVec 32 := (fpMul fpFormat32 .RNE a b).1
def fpMul64 (a b : BitVec 64) : BitVec 64 := (fpMul fpFormat64 .RNE a b).1
def fpMul32Flags (a b : BitVec 32) : BitVec 32 := (fpMul fpFormat32 .RNE a b).2
def fpMul64Flags (a b : BitVec 64) : BitVec 32 := (fpMul fpFormat64 .RNE a b).2

def fpNMul32 (a b : BitVec 32) : BitVec 32 := (fpNMul fpFormat32 .RNE a b).1
def fpNMul64 (a b : BitVec 64) : BitVec 64 := (fpNMul fpFormat64 .RNE a b).1
def fpNMul32Flags (a b : BitVec 32) : BitVec 32 := (fpNMul fpFormat32 .RNE a b).2
def fpNMul64Flags (a b : BitVec 64) : BitVec 32 := (fpNMul fpFormat64 .RNE a b).2

def fpDiv32 (a b : BitVec 32) : BitVec 32 := (fpDiv fpFormat32 .RNE a b).1
def fpDiv64 (a b : BitVec 64) : BitVec 64 := (fpDiv fpFormat64 .RNE a b).1
def fpDiv32Flags (a b : BitVec 32) : BitVec 32 := (fpDiv fpFormat32 .RNE a b).2
def fpDiv64Flags (a b : BitVec 64) : BitVec 32 := (fpDiv fpFormat64 .RNE a b).2

def fpSqrt32 (a : BitVec 32) : BitVec 32 := (fpSqrt fpFormat32 .RNE a).1
def fpSqrt64 (a : BitVec 64) : BitVec 64 := (fpSqrt fpFormat64 .RNE a).1
def fpSqrt32Flags (a : BitVec 32) : BitVec 32 := (fpSqrt fpFormat32 .RNE a).2
def fpSqrt64Flags (a : BitVec 64) : BitVec 32 := (fpSqrt fpFormat64 .RNE a).2

def fpMax32 (a b : BitVec 32) : BitVec 32 := (fpMinMax fpFormat32 true false a b).1
def fpMax64 (a b : BitVec 64) : BitVec 64 := (fpMinMax fpFormat64 true false a b).1
def fpMin32 (a b : BitVec 32) : BitVec 32 := (fpMinMax fpFormat32 false false a b).1
def fpMin64 (a b : BitVec 64) : BitVec 64 := (fpMinMax fpFormat64 false false a b).1
def fpMaxNm32 (a b : BitVec 32) : BitVec 32 := (fpMinMax fpFormat32 true true a b).1
def fpMaxNm64 (a b : BitVec 64) : BitVec 64 := (fpMinMax fpFormat64 true true a b).1
def fpMinNm32 (a b : BitVec 32) : BitVec 32 := (fpMinMax fpFormat32 false true a b).1
def fpMinNm64 (a b : BitVec 64) : BitVec 64 := (fpMinMax fpFormat64 false true a b).1
def fpMinMax32Flags (a b : BitVec 32) : BitVec 32 := (fpMinMax fpFormat32 false false a b).2
def fpMinMax64Flags (a b : BitVec 64) : BitVec 32 := (fpMinMax fpFormat64 false false a b).2

def fpRint32 (rm : FpRoundMode) (a : BitVec 32) : BitVec 32 := (fpRint fpFormat32 rm false a).1
def fpRint64 (rm : FpRoundMode) (a : BitVec 64) : BitVec 64 := (fpRint fpFormat64 rm false a).1
def fpRint32Flags (exact : Bool) (a : BitVec 32) : BitVec 32 := (fpRint fpFormat32 .RNE exact a).2
def fpRint64Flags (exact : Bool) (a : BitVec 64) : BitVec 32 := (fpRint fpFormat64 .RNE exact a).2

def fpFma32 (addend x y : BitVec 32) : BitVec 32 := (fpFma fpFormat32 .RNE addend x y).1
def fpFma64 (addend x y : BitVec 64) : BitVec 64 := (fpFma fpFormat64 .RNE addend x y).1
def fpFma32Flags (addend x y : BitVec 32) : BitVec 32 := (fpFma fpFormat32 .RNE addend x y).2
def fpFma64Flags (addend x y : BitVec 64) : BitVec 32 := (fpFma fpFormat64 .RNE addend x y).2

def evalFp1Op32 (opcode : BitVec 6) (x : BitVec 32) : BitVec 32 := (fp1Op fpFormat32 opcode x).1
def evalFp1Op64 (opcode : BitVec 6) (x : BitVec 64) : BitVec 64 := (fp1Op fpFormat64 opcode x).1
def evalFp1OpFlags32 (opcode : BitVec 6) (x : BitVec 32) : BitVec 32 := (fp1Op fpFormat32 opcode x).2
def evalFp1OpFlags64 (opcode : BitVec 6) (x : BitVec 64) : BitVec 32 := (fp1Op fpFormat64 opcode x).2

def evalFp2Op32 (opcode : BitVec 4) (a b : BitVec 32) : BitVec 32 := (fp2Op fpFormat32 opcode a b).1
def evalFp2Op64 (opcode : BitVec 4) (a b : BitVec 64) : BitVec 64 := (fp2Op fpFormat64 opcode a b).1
def evalFp2OpFlags32 (opcode : BitVec 4) (a b : BitVec 32) : BitVec 32 := (fp2Op fpFormat32 opcode a b).2
def evalFp2OpFlags64 (opcode : BitVec 4) (a b : BitVec 64) : BitVec 32 := (fp2Op fpFormat64 opcode a b).2

def evalFpToIntRound32_32 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 32) : BitVec 32 :=
  (fpToInt fpFormat32 32 unsigned rm fbits x).1
def evalFpToIntRound64_32 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 32) : BitVec 64 :=
  (fpToInt fpFormat32 64 unsigned rm fbits x).1
def evalFpToIntRound32_64 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 64) : BitVec 32 :=
  (fpToInt fpFormat64 32 unsigned rm fbits x).1
def evalFpToIntRound64_64 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 64) : BitVec 64 :=
  (fpToInt fpFormat64 64 unsigned rm fbits x).1
def evalFpToIntRoundFlags32_32 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 32) : BitVec 32 :=
  (fpToInt fpFormat32 32 unsigned rm fbits x).2
def evalFpToIntRoundFlags64_32 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 32) : BitVec 32 :=
  (fpToInt fpFormat32 64 unsigned rm fbits x).2
def evalFpToIntRoundFlags32_64 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 64) : BitVec 32 :=
  (fpToInt fpFormat64 32 unsigned rm fbits x).2
def evalFpToIntRoundFlags64_64 (unsigned : Bool) (rm : FpRoundMode) (fbits : Nat) (x : BitVec 64) : BitVec 32 :=
  (fpToInt fpFormat64 64 unsigned rm fbits x).2

def evalFpToInt32_32 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 32) : BitVec 32 :=
  evalFpToIntRound32_32 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToInt64_32 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 32) : BitVec 64 :=
  evalFpToIntRound64_32 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToInt32_64 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 64) : BitVec 32 :=
  evalFpToIntRound32_64 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToInt64_64 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 64) : BitVec 64 :=
  evalFpToIntRound64_64 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToIntFlags32_32 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 32) : BitVec 32 :=
  evalFpToIntRoundFlags32_32 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToIntFlags64_32 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 32) : BitVec 32 :=
  evalFpToIntRoundFlags64_32 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToIntFlags32_64 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 64) : BitVec 32 :=
  evalFpToIntRoundFlags32_64 unsigned (FpRoundMode.ofBits2 rmode) 0 x
def evalFpToIntFlags64_64 (unsigned : Bool) (rmode : BitVec 2) (x : BitVec 64) : BitVec 32 :=
  evalFpToIntRoundFlags64_64 unsigned (FpRoundMode.ofBits2 rmode) 0 x

def evalFixedToFp32_32 (unsigned : Bool) (fbits : Nat) (x : BitVec 32) : BitVec 32 :=
  (fixedToFp fpFormat32 unsigned .RNE fbits x).1
def evalFixedToFp32_64 (unsigned : Bool) (fbits : Nat) (x : BitVec 64) : BitVec 32 :=
  (fixedToFp fpFormat32 unsigned .RNE fbits x).1
def evalFixedToFp64_32 (unsigned : Bool) (fbits : Nat) (x : BitVec 32) : BitVec 64 :=
  (fixedToFp fpFormat64 unsigned .RNE fbits x).1
def evalFixedToFp64_64 (unsigned : Bool) (fbits : Nat) (x : BitVec 64) : BitVec 64 :=
  (fixedToFp fpFormat64 unsigned .RNE fbits x).1
def evalFixedToFpFlags32_32 (unsigned : Bool) (fbits : Nat) (x : BitVec 32) : BitVec 32 :=
  (fixedToFp fpFormat32 unsigned .RNE fbits x).2
def evalFixedToFpFlags32_64 (unsigned : Bool) (fbits : Nat) (x : BitVec 64) : BitVec 32 :=
  (fixedToFp fpFormat32 unsigned .RNE fbits x).2
def evalFixedToFpFlags64_32 (unsigned : Bool) (fbits : Nat) (x : BitVec 32) : BitVec 32 :=
  (fixedToFp fpFormat64 unsigned .RNE fbits x).2
def evalFixedToFpFlags64_64 (unsigned : Bool) (fbits : Nat) (x : BitVec 64) : BitVec 32 :=
  (fixedToFp fpFormat64 unsigned .RNE fbits x).2

def evalIntToFp32_32 (unsigned : Bool) (x : BitVec 32) : BitVec 32 := evalFixedToFp32_32 unsigned 0 x
def evalIntToFp32_64 (unsigned : Bool) (x : BitVec 64) : BitVec 32 := evalFixedToFp32_64 unsigned 0 x
def evalIntToFp64_32 (unsigned : Bool) (x : BitVec 32) : BitVec 64 := evalFixedToFp64_32 unsigned 0 x
def evalIntToFp64_64 (unsigned : Bool) (x : BitVec 64) : BitVec 64 := evalFixedToFp64_64 unsigned 0 x
def evalIntToFpFlags32_32 (unsigned : Bool) (x : BitVec 32) : BitVec 32 := evalFixedToFpFlags32_32 unsigned 0 x
def evalIntToFpFlags32_64 (unsigned : Bool) (x : BitVec 64) : BitVec 32 := evalFixedToFpFlags32_64 unsigned 0 x
def evalIntToFpFlags64_32 (unsigned : Bool) (x : BitVec 32) : BitVec 32 := evalFixedToFpFlags64_32 unsigned 0 x
def evalIntToFpFlags64_64 (unsigned : Bool) (x : BitVec 64) : BitVec 32 := evalFixedToFpFlags64_64 unsigned 0 x

def evalFpCvt32To64 (x : BitVec 32) : BitVec 64 := (fpConvert fpFormat32 fpFormat64 .RNE x).1
def evalFpCvt32To64Flags (x : BitVec 32) : BitVec 32 := (fpConvert fpFormat32 fpFormat64 .RNE x).2
def evalFpCvt64To32 (x : BitVec 64) : BitVec 32 := (fpConvert fpFormat64 fpFormat32 .RNE x).1
def evalFpCvt64To32Flags (x : BitVec 64) : BitVec 32 := (fpConvert fpFormat64 fpFormat32 .RNE x).2

def evalFp3Op32 (o1 o0 : Bool) (vn vm va : BitVec 32) : BitVec 32 := (fp3Op fpFormat32 o1 o0 vn vm va).1
def evalFp3Op64 (o1 o0 : Bool) (vn vm va : BitVec 64) : BitVec 64 := (fp3Op fpFormat64 o1 o0 vn vm va).1
def evalFp3OpFlags32 (o1 o0 : Bool) (vn vm va : BitVec 32) : BitVec 32 := (fp3Op fpFormat32 o1 o0 vn vm va).2
def evalFp3OpFlags64 (o1 o0 : Bool) (vn vm va : BitVec 64) : BitVec 32 := (fp3Op fpFormat64 o1 o0 vn vm va).2

def evalFpCmp32 (signalNaN : Bool) (a b : BitVec 32) : PState := (fpCmp fpFormat32 signalNaN a b).1
def evalFpCmp64 (signalNaN : Bool) (a b : BitVec 64) : PState := (fpCmp fpFormat64 signalNaN a b).1
def evalFpCmpFlags32 (signalNaN : Bool) (a b : BitVec 32) : BitVec 32 := (fpCmp fpFormat32 signalNaN a b).2
def evalFpCmpFlags64 (signalNaN : Bool) (a b : BitVec 64) : BitVec 32 := (fpCmp fpFormat64 signalNaN a b).2

end Arm64


