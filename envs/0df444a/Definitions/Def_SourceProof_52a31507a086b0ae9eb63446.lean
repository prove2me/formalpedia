-- Prove2me | Definitions.Def_SourceProof_52a31507a086b0ae9eb63446
-- name    : SourceProof_52a31507a086b0ae9eb63446
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:34:30.063051+00:00
-- url     : https://prove2.me/theorems/a7e44092-bfae-428c-aad7-5f7e9f9639b1
-- title:
--   LevyStochCalc source module: SourceProof_52a31507a086b0ae9eb63446
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_memLp_at` comes from the `LevyStochCalc.Poisson.CompensatedMartingaleQuadratic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Quadratic-variation martingale of the compensated simple integral

The set-level weighted isometry `∫ g·(Iₜ − Iₛ)² = ∑_i ν̂(Rᵢ).toReal · ∫ g·ξᵢ²` over the
increment boxes `Rᵢ = timeRect i t \ timeRect i s`, membership of `simpleIntegral N φ t` in
`L²(P)` at every running time, its vanishing at nonpositive times, and the resulting
martingale property of the compensated square
`t ↦ (simpleIntegral N φ t)² − ∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` with respect to a Poisson
filtration; also the joint measurability of the simple integrand `eval` in `(s, e, ω)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_52a31507a086b0ae9eb63446
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ t ω) 2 P := by
  have h_unfold : (fun ω => LevyStochCalc.Poisson.Compensated.simpleIntegral N φ t ω)
      = ∑ i : Fin φ.N, fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω := by
    funext ω; rw [Finset.sum_apply]; rfl
  rw [h_unfold]
  refine MeasureTheory.memLp_finsetSum' _ (fun i _ => ?_)
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have hmeas : MeasurableSet (φ.timeRect i t) := measurableSet_Ioc.prod (φ.A_measurable i)
  have hÑ_aesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => N.compensated (φ.timeRect i t) ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hmeas)).sub_const _).aestronglyMeasurable
  have hÑ_memLp : MeasureTheory.MemLp (fun ω => N.compensated (φ.timeRect i t) ω) 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hÑ_aesm).mpr
      (_root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hmeas (LevyStochCalc.Poisson.Compensated.referenceIntensity_timeRect_ne_top φ i t))
  refine MeasureTheory.MemLp.mono' (hÑ_memLp.norm.const_mul |M|)
    ((φ.ξ_measurable i).aestronglyMeasurable.mul hÑ_aesm) ?_
  filter_upwards with ω
  change ‖φ.ξ i ω * N.compensated (φ.timeRect i t) ω‖
    ≤ |M| * ‖N.compensated (φ.timeRect i t) ω‖
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self M)
end LevyStochCalc.Poisson.Compensated


