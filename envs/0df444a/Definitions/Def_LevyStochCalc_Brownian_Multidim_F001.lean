-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_Multidim_F001
-- name    : LevyStochCalc_Brownian_Multidim_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:32:59.363685+00:00
-- url     : https://prove2.me/theorems/162e0e8e-f0fe-4056-a5cc-aa179554ad5f
-- title:
--   Source declarations: LevyStochCalc.Brownian.Multidim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.Multidim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Multidim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# d-dimensional Brownian motion

A `d`-dimensional Brownian motion is a `Fin d`-tuple of independent 1-D
Brownian motions on the same probability space. Constructed on the finite
product `MeasureTheory.Measure.pi` of copies of a space carrying one, whose
coordinates are independent by `ProbabilityTheory.iIndepFun_pi`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.1.

## Contents

* `MultidimBrownianMotion` — the structure; `components_independent` is
  stated with `iIndepFun`, and `joint_continuous_paths` makes the almost-sure
  continuity of the vector-valued path explicit.
* `MultidimBrownianMotion.exists` — existence, via `MeasureTheory.Measure.pi` (finite
  product of probability spaces) and the independence of coordinate
  evaluations on a product measure; each coordinate is a 1-D Brownian motion
  lifted along the corresponding projection.
* `MultidimBrownianMotion.joint_increment_gaussian_diagonal` — each
  coordinate increment is Gaussian and the coordinate increments are
  independent.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim

universe u

section Definition
variable {Ω : Type u} [MeasurableSpace Ω]

end Definition

section MeasurePreserving
variable {Ω : Type u} [MeasurableSpace Ω]

end MeasurePreserving

section Existence
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Joint increment Gaussianity with diagonal covariance.**

For a multidim Brownian motion `W`, the joint vector of component increments
`(ω ↦ fun i => (W i).W t ω − (W i).W s ω) : Ω → (Fin d → ℝ)` has joint
distribution that satisfies BOTH:

* per-component: each scalar increment `(W i).W t − (W i).W s` has law
  `gaussianReal 0 (t − s)`;
* mutual independence across `i ∈ Fin d`.

This is the multivariate-Gaussian-with-diagonal-covariance `(t − s) · I_d`
in spelled-out form (per Karatzas-Shreve §2.5 / Le Gall Def 2.12). -/
theorem MultidimBrownianMotion.joint_increment_gaussian_diagonal
    {Ω : Type u} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {d : ℕ} (W : MultidimBrownianMotion P d)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    -- Per-component Gaussian law of each increment:
    (∀ i : Fin d,
      P.map (fun ω => (W.W i).W t ω - (W.W i).W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) ∧
    -- Joint independence of the increments across i:
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Ω) => (W.W i).W t ω - (W.W i).W s ω) P := by
  refine ⟨fun i => (W.W i).increment_gaussian hs hst, ?_⟩
  -- Apply iIndepFun.comp to components_independent with `g i := fun path => path t - path s`.
  -- Each `g i` is measurable (eval_t and eval_s are measurable on ℝ → ℝ,
  --   and sub is measurable).
  have h_g_meas : ∀ _ : Fin d,
      Measurable (fun (path : ℝ → ℝ) => path t - path s) := by
    intro _
    exact (measurable_pi_apply t).sub (measurable_pi_apply s)
  exact W.components_independent.comp
    (fun (_ : Fin d) (path : ℝ → ℝ) => path t - path s) h_g_meas
end Existence

end LevyStochCalc.Brownian.Multidim


