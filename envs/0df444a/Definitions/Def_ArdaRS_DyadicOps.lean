-- Prove2me | Definitions.Def_ArdaRS_DyadicOps
-- name    : ArdaRS_DyadicOps
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:46:08.931229+00:00
-- url     : https://prove2.me/theorems/f555c358-0260-4562-9493-a9f38e8b9083
-- title:
--   Operations on dyadic intervals
-- statement:
--   Computable operations on dyadic intervals, including subtraction and outward rounding. These definitions make no assertion about a particular zeta value.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/DIntvCorrect.lean

/- Source: Arda, commit af4fde897, DIntvCorrect.lean; Apache-2.0. -/
/-  DIntvCorrect.lean -- the DIntv correctness surface (A1).

    Builds on `DIntvDef`'s proven `add_sound`/`mul_sound`.  Completes the op surface with
    Real mem-soundness proofs for every operation the evaluators need:

      * `neg`, `sub`               -- exact, same/aligned exponent
      * `abs`                      -- |·| envelope (sign split)
      * `scale2`                   -- exact power-of-two rescale (no rounding)
      * `ofInt`                    -- exact integer point
      * `roundTo`                  -- directed OUTWARD truncation (the width-control primitive):
                                      memR x I → memR x (I.roundTo p).  THE key lemma.
      * `union` / `hull`           -- interval hull: memR x I → memR x (hull I J) (and sym)
      * `nonneg` / `nonpos` / `isPos` / `isNeg` / `sign?`  -- sign-definite predicates with
                                      their Real meanings
      * `ltOf` / `sepR`            -- interval comparison: I.hi·2^eI < J.lo·2^eJ
                                      ⇒ ∀ x∈I, y∈J, x < y.

    Design: `DIntvDef.DIntv` stores `lo hi : Int` at a single exponent `e : Int`, mem
    `(lo:ℝ)·2^e ≤ x ≤ (hi:ℝ)·2^e`.  `roundTo` DROPS `d` low mantissa bits, flooring `lo`
    and ceiling `hi`, and raises the exponent by `d` -- so the denoted real interval only
    GROWS.  All arithmetic is pure `Int` (no `Rat`, no division, no WF recursion).

    conjecture1_proved = False.  Finite interval arithmetic, not a proof of RH.
-/
import Definitions.Def_ArdaRS_Dyadic

namespace DIntvProd
namespace DIntv

/-! ### Exact / structural ops (no rounding) -/

/-- Exact integer point `[n, n]` at exponent 0. -/
def ofInt (n : Int) : DIntv := ⟨n, n, 0⟩

/-- Exact multiply-by-`2^k`: keep mantissas, shift the exponent.  No rounding, no widening. -/
def scale2 (I : DIntv) (k : Int) : DIntv := ⟨I.lo, I.hi, I.e + k⟩

/-- Interval subtraction at a COMMON exponent: `x - y ∈ I - J`.  (Aligning widening is
    `roundTo`/`alignPair`'s job; here we assume shared exponent as `add` does.) -/
def sub (I J : DIntv) (h : I.e = J.e) : DIntv := add I (neg J) (by simp [neg, h])

/-- Absolute-value envelope.  If the interval is sign-definite this is exact; if it straddles
    0 the lower end becomes 0 and the upper end is `max |lo| |hi|`.  Same exponent. -/
def abs (I : DIntv) : DIntv :=
  if 0 ≤ I.lo then I                          -- wholly ≥ 0: |·| = identity
  else if I.hi ≤ 0 then neg I                 -- wholly ≤ 0: |·| = negation
  else ⟨0, max (-I.lo) I.hi, I.e⟩             -- straddles 0

/-- Interval hull (union bound): the smallest common-exponent box containing both.
    Requires the shared exponent (evaluators align first). -/
def hull (I J : DIntv) (_h : I.e = J.e) : DIntv := ⟨min I.lo J.lo, max I.hi J.hi, I.e⟩

/-! ### Directed OUTWARD truncation -- the width-control primitive -/

/-- Floor of `m / 2^d` for `m : Int`, `d : Nat` (arithmetic right shift = floor division). -/
def floorShift (m : Int) (d : Nat) : Int := m >>> d

/-- Ceil of `m / 2^d`: `-(floor (-m / 2^d))`.  Pure Int, structural. -/
def ceilShift (m : Int) (d : Nat) : Int := -((-m) >>> d)

/-- Round OUTWARD, dropping `d` low mantissa bits: floor the lo endpoint, ceil the hi
    endpoint, and raise the exponent by `d`.  The denoted real interval only GROWS, so
    membership is preserved.  This is the primitive that keeps kernel mantissas bounded
    on long folds. -/
def roundTo (I : DIntv) (d : Nat) : DIntv :=
  ⟨floorShift I.lo d, ceilShift I.hi d, I.e + (d : Int)⟩

/-! ### Sign-definite predicates -/

/-- Wholly `≥ 0`?  (`lo ≥ 0`.) -/
def nonneg (I : DIntv) : Bool := 0 ≤ I.lo

/-- Wholly `≤ 0`?  (`hi ≤ 0`.) -/
def nonpos (I : DIntv) : Bool := I.hi ≤ 0

/-- Strictly positive?  (`lo > 0`.) -/
def isPos (I : DIntv) : Bool := 0 < I.lo

/-- Strictly negative?  (`hi < 0`.) -/
def isNeg (I : DIntv) : Bool := I.hi < 0

/-- Definite sign if 0 is excluded: `some true` = strictly +, `some false` = strictly −,
    `none` = straddles/touches 0. -/
def sign? (I : DIntv) : Option Bool :=
  if isPos I then some true
  else if isNeg I then some false
  else none

/-! ### Comparison -/

/-- Kernel-checkable strict separation: `hi_I·2^{eI} < lo_J·2^{eJ}` decides `I` entirely
    below `J`.  Compared as `Int` after aligning to the min exponent (so still Int-only).
    We encode the real inequality directly as a `Prop` here; the Bool decider lives with
    the checker in CheckBand.  This lemma is the soundness bridge. -/
def belowR (I J : DIntv) : Prop :=
  (I.hi : ℝ) * (2 : ℝ) ^ I.e < (J.lo : ℝ) * (2 : ℝ) ^ J.e

/-! ### Soundness proofs -/















/-! #### roundTo soundness -- the width-control primitive

`floorShift m d = m >>> d = ⌊m / 2^d⌋` and `ceilShift m d = ⌈m / 2^d⌉` as `Int`.  We first
establish the two integer facts `floorShift m d · 2^d ≤ m ≤ ceilShift m d · 2^d`, cast them
to ℝ, and combine with `2^e ≥ 0` and `2^(e+d) = 2^e · 2^d`. -/







/-! #### Predicate meanings -/













/-! #### Comparison soundness -/



end DIntv
end DIntvProd

def ArdaRS_DyadicOps : Nat := 0


