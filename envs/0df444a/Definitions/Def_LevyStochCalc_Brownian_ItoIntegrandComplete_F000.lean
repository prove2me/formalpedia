-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000
-- name    : LevyStochCalc_Brownian_ItoIntegrandComplete_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:12:45.960679+00:00
-- url     : https://prove2.me/theorems/2e585bbc-0cf3-4d4f-87ed-e0895e8f314e
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIntegrandComplete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIntegrandComplete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The product of the sample measure with Lebesgue measure on the horizon `[0, T]`. -/
noncomputable def energyMeasure (P : Measure Ω) (T : ℝ) : Measure (Ω × ℝ) :=
  P.prod (volume.restrict (Set.Icc (0 : ℝ) T))
/-- The energy of an integrand over the horizon `[0, T]`. -/
noncomputable def energy (P : Measure Ω) (T : ℝ) (H : Ω → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
/-- The square of the `L²`-seminorm as an extended integral of squares. -/
theorem eLpNorm_sq_eq_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by simp
  rw [h2, ← ENNReal.rpow_natCast ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul]
  norm_num
  rfl
omit [IsProbabilityMeasure P] in
/-- The energy is the square of the `L²`-seminorm on the product space. -/
theorem energy_eq_eLpNorm_sq {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) (T : ℝ) :
    energy P T H = eLpNorm (fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) ^ 2 := by
  have hme : AEMeasurable (fun p : Ω × ℝ => (‖H p.1 p.2‖₊ : ℝ≥0∞) ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2).aemeasurable
  rw [eLpNorm_sq_eq_lintegral, energyMeasure, energy,
    lintegral_prod (fun p : Ω × ℝ => (‖H p.1 p.2‖₊ : ℝ≥0∞) ^ 2) hme]
omit [IsProbabilityMeasure P] in
/-- An integrand of finite energy is square integrable on the product space. -/
theorem memLp_of_energy_ne_top {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) {T : ℝ}
    (hfin : energy P T H ≠ ⊤) :
    MemLp (fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) := by
  refine ⟨hm.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  refine lt_top_iff_ne_top.mpr fun hcon => hfin ?_
  rw [energy_eq_eLpNorm_sq hm T, hcon]
  simp
section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

end Complete

end LevyStochCalc.Brownian.Ito


