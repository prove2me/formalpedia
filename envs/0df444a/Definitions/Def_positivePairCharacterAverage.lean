-- Prove2me | Definitions.Def_positivePairCharacterAverage
-- name    : positivePairCharacterAverage
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T08:55:29.012588+00:00
-- url     : https://prove2.me/theorems/8969e33e-0425-4c97-87c7-7219ed9dff0c
-- title:
--   Normalized positive-pair Syracuse character averages
-- statement:
--   Let e_N(t) = exp(2π i t/N). For N ≥ 1 and x ∈ Z/NZ, define the conditional expectation E[e_N(x(2^{A₂}+3)) | A₁ + A₂ = 3], where A₁ and A₂ are independent positive geometric variables. The associated Syracuse white-point average evaluates this conditional average at x = −2⁻¹P. These are definitions only; no support-mass, pair-factorization, or cancellation theorem is included.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 7.1, equations (7.4), (7.7)–(7.10), https://arxiv.org/html/1909.03562v7.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

import Definitions.Def_syracuseOffsetMod
import Definitions.Def_syracuseDyadicPhase
import Definitions.Def_positivePairSumThree

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable section

def positivePairCharacterAverage {N : ℕ} [NeZero N] (x : ZMod N) : ℂ :=
  (((positiveGeomTwoVector 2).real positivePairSumThreeEvent : ℝ) : ℂ)⁻¹ *
    ∑ a ∈ positivePairSumThree,
      (((positiveGeomTwoVector 2).real ({a} : Set (Fin 2 → ℕ)) : ℝ) : ℂ) *
        ZMod.stdAddChar
          (x * ((2 ^ (a 1) + 3 : ℕ) : ZMod N))

def syracuseWhitePointAverage
    (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) : ℂ :=
  letI : NeZero (3 ^ n) := ⟨by positivity⟩
  positivePairCharacterAverage
    (-((2 : ZMod (3 ^ n))⁻¹ * syracuseDyadicPhase n ξ j l))


