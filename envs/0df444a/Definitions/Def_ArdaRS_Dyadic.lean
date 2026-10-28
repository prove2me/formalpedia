-- Prove2me | Definitions.Def_ArdaRS_Dyadic
-- name    : ArdaRS_Dyadic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:45:53.181315+00:00
-- url     : https://prove2.me/theorems/a09c4085-9d11-464c-b973-413e955249ab
-- title:
--   Dyadic intervals
-- statement:
--   Dyadic intervals with integer endpoints and a shared power-of-two exponent, together with basic interval operations.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/DIntvDef.lean

/- Source: Arda, commit af4fde897, DIntvDef.lean; Apache-2.0. -/
/-  DIntvDef.lean -- production-intended dyadic interval definitions + mem-soundness.

    This is the cleaner, production sibling of `Spike/DIntvMini.lean`.  It carries the
    SAME computable ops (add, mul, neg) and, crucially, PROVES that they are sound with
    respect to the real interval they denote:

        I.memR x  :=  (I.lo : ℝ) * 2^I.e ≤ x ∧ x ≤ (I.hi : ℝ) * 2^I.e

    We prove `add_sound` and `mul_sound` ONLY (the A0 remit): if `x ∈ I` and `y ∈ J`
    then `x + y ∈ I.add J` and `x * y ∈ I.mul J`.  These validate the Real-bridging
    proof style that the full A1 correctness surface will scale up.

    Design note for A1: to keep the soundness proofs clean we store BOTH endpoints at a
    COMMON exponent (add aligns to the shared exponent; mul adds exponents).  `roundTo`
    (outward widening) is a separate, monotone op whose soundness is a one-liner from
    `add`/`mul` monotonicity and is deferred to A1.

    conjecture1_proved = False.  This is finite interval arithmetic, not a proof of RH.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace DIntvProd

/-- Dyadic interval `[lo * 2^e, hi * 2^e]`. -/
structure DIntv where
  lo : Int
  hi : Int
  e  : Int
deriving Repr, DecidableEq

namespace DIntv

/-- The real interval denoted by `I`: `x` lies in `[lo·2^e, hi·2^e]`.
    `2^e` is the real `zpow`, so `e : Int` (may be negative) is handled directly. -/
noncomputable def memR (x : ℝ) (I : DIntv) : Prop :=
  (I.lo : ℝ) * (2 : ℝ) ^ I.e ≤ x ∧ x ≤ (I.hi : ℝ) * (2 : ℝ) ^ I.e

/-- Interval negation `[-hi, -lo]` at the same exponent. -/
def neg (I : DIntv) : DIntv := ⟨-I.hi, -I.lo, I.e⟩

/-- Interval addition at a COMMON exponent `e` (production form assumes aligned inputs;
    the aligning `scaleMantissa` widening is the spike file's job and A1 will fold its
    monotone soundness in).  Here `add` requires the shared exponent and adds mantissas. -/
def add (I J : DIntv) (_h : I.e = J.e) : DIntv := ⟨I.lo + J.lo, I.hi + J.hi, I.e⟩

/-- Interval multiplication: 4 corner products, min/max envelope; exponents add. -/
def mul (I J : DIntv) : DIntv :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨min (min a b) (min c d), max (max a b) (max c d), I.e + J.e⟩

/-! ### Soundness -/











end DIntv
end DIntvProd

def ArdaRS_Dyadic : Nat := 0


