-- Prove2me | Definitions.Def_eulerMascheroni_p2Approximation
-- name    : eulerMascheroni_p2Approximation
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T23:57:14.621013+00:00
-- url     : https://prove2.me/theorems/141b7d16-0bb6-4737-a466-4000e9a699f6
-- title:
--   Explicit second-order Euler approximants and saddle models
-- statement:
--   The rational binomial coefficients, numerator and denominator of the p=2 higher-order Euler approximants, together with explicit real saddle models. SaddleLimits and SharpRate are propositions recording research targets; this definition asserts neither of them.
-- source:
--   Van Assche–Wolfs, arXiv:2404.09799v3, section 5, higher-order construction. Explicit p=2 saddle models derived in local research draft SADDLE_DRAFT.md (11 September 2026), not attributed to a proved theorem in the source.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators

namespace EulerMascheroni.P2

/-- The published p=2 binomial summand, over the rationals. -/
def coefficient (n k : ℕ) : ℚ :=
  (n.choose k : ℚ)^2 * ((n+k).choose k : ℚ)^2 / (k.factorial : ℚ)

def Q (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n+1), coefficient n k

def P (n : ℕ) : ℚ := - ∑ k ∈ Finset.range (n+1),
  coefficient n k * (2 * harmonic (n+k) + 2 * harmonic (n-k) - 5 * harmonic k)

noncomputable def F (n : ℕ) : ℝ :=
  (Q n : ℝ) * Real.eulerMascheroniConstant - (P n : ℝ)

noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) ^ (4 / 5 : ℝ)
noncomputable def subscale (n : ℕ) : ℝ := (n : ℝ) ^ (2 / 5 : ℝ)
noncomputable def theta : ℝ := 2 * Real.pi / 5
noncomputable def rate : ℝ := 5 * (1 - Real.cos theta)

noncomputable def phase (n : ℕ) : ℝ :=
  5 * scale n * Real.sin theta - (2/3 : ℝ) * subscale n * Real.sin (3*theta)
    - 2*theta

noncomputable def qModel (n : ℕ) : ℝ :=
  Real.exp (5 * scale n - (2/3 : ℝ) * subscale n + 1/5) /
    (4 * Real.pi^2 * Real.sqrt 5 * scale n^2)

noncomputable def fModel (n : ℕ) : ℝ :=
  Real.exp (5 * scale n * Real.cos theta -
    (2/3 : ℝ) * subscale n * Real.cos (3*theta) + 1/5) /
    (Real.pi * Real.sqrt 5 * scale n^2)

/-- The two analytic assertions required by the relative-error reduction.
They are a proposition, not axioms or claimed theorems. Indices start at 1. -/
def SaddleLimits : Prop :=
  Filter.Tendsto (fun n : ℕ => (Q (n+1) : ℝ) / qModel (n+1) - 1)
    Filter.atTop (nhds 0) ∧
  Filter.Tendsto (fun n : ℕ => F (n+1) / fModel (n+1) - Real.sin (phase (n+1)))
    Filter.atTop (nhds 0)

/-- A zero-safe formulation of the predicted sharp exponential rate.
Unlike a real-valued log convention, this does not assign log(0)=0. -/
def SharpRate : Prop := ∀ ε : ℝ, 0 < ε →
  (∀ᶠ n : ℕ in Filter.atTop,
    |Real.eulerMascheroniConstant - (P (n+1) : ℝ) / (Q (n+1) : ℝ)| ≤
      Real.exp ((-rate + ε) * scale (n+1))) ∧
  (∃ᶠ n : ℕ in Filter.atTop,
    Real.exp ((-rate - ε) * scale (n+1)) ≤
      |Real.eulerMascheroniConstant - (P (n+1) : ℝ) / (Q (n+1) : ℝ)|)

end EulerMascheroni.P2


