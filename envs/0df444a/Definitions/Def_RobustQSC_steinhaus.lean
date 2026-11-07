-- Prove2me | Definitions.Def_RobustQSC_steinhaus
-- name    : RobustQSC_steinhaus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:25.93696+00:00
-- url     : https://prove2.me/theorems/8036a113-bd62-4c20-97a7-79908c7bd30d
-- title:
--   The Steinhaus law on the unit circle
-- statement:
--   A Steinhaus random variable is a uniform (Haar) draw from $\{z\in\mathbb C:|z|=1\}$; here it is the law of $e^{2\pi i\theta}$ with $\theta$ uniform on $[0,1]$. It is the law of the phases of a Haar-random vector, given the moduli.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §3.1, p.19

import Mathlib

namespace RobustQSC

open MeasureTheory

/-- The Steinhaus law: the uniform (Haar) law on the unit circle `{z ∈ ℂ : |z| = 1}`, the law of
`e^{2πiθ}` with `θ` uniform on `[0, 1]`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §3.1, p.19 ("A Steinhaus random
variable is a uniform (Haar) draw from the set {z ∈ C : |z| = 1}"). -/
noncomputable def steinhaus : Measure ℂ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map fun θ : ℝ =>
    Complex.exp (2 * Real.pi * Complex.I * θ)

/-! ### Sanity tests -/

instance : IsProbabilityMeasure steinhaus := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  unfold steinhaus
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Steinhaus variables have modulus one almost surely. -/
example : ∀ᵐ z ∂steinhaus, ‖z‖ = 1 := by
  unfold steinhaus
  rw [ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine Filter.Eventually.of_forall fun θ => ?_
  rw [Complex.norm_exp]
  simp

end RobustQSC


