-- Prove2me | Definitions.Def_OAI_PiExponent_ApproximationDefinitions
-- name    : OAI_PiExponent_ApproximationDefinitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-07T06:57:39.94273+00:00
-- url     : https://prove2.me/theorems/036f42cc-1c09-4e3b-b6c0-81e678bf7d9d
-- title:
--   Rational approximation and the irrationality exponent
-- statement:
--   For a real number $x$ and real exponent $\nu$, good rational approximations are rational numbers $r$ with reduced denominator $q\ge2$ and $0<|x-r|<q^{-\nu}$. Approximation exponents are positive $\nu$ for which this set is infinite; the irrationality exponent $\mu(x)$ is their supremum in $\mathbb R$.
--
--   The eventual lower-bound predicate asserts that for every $\nu>2$ there is a natural $Q\ge2$ such that $q^{-\nu}\le |x-p/q|$ for every integer numerator $p$ and every natural denominator $q\ge Q$. A companion predicate uses integer thresholds and denominators, still constrained by $Q\ge2$; the $\pi$ predicate specializes the natural formulation to $x=\pi$. These are the six original definitions from the pinned OpenAI source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Statement.lean#L7-L23

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Cast.Order

namespace OAI

namespace PiExponent

def GoodRationalApproximations (x ν : ℝ) : Set ℚ :=
  {r | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}

def ApproximationExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧ (GoodRationalApproximations x ν).Infinite}

noncomputable def irrationalityExponent (x : ℝ) : ℝ := sSup (ApproximationExponents x)

def EventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

def PiEventualLowerBound : Prop := EventualLowerBound Real.pi

def IntegerEventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ (p q : ℤ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

end PiExponent

end OAI


