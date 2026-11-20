-- Prove2me | Definitions.Def_SourceProof_839c3c586f330ad57afd5326
-- name    : SourceProof_839c3c586f330ad57afd5326
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:25:01.125318+00:00
-- url     : https://prove2.me/theorems/78c03a62-9105-487c-97ad-bcc977fb380a
-- title:
--   LevyStochCalc source module: SourceProof_839c3c586f330ad57afd5326
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_cross_integrable` comes from the `LevyStochCalc.Poisson.CompensatedMartingaleIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Clamped compensator and increment boxes of the compensated simple integral

The compensator `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` of the quadratic variation in its explicit
clamped form `∑_i ν̂(timeRect i t) · ξᵢ²`, the a.e. decomposition of the increment
`simpleIntegral t − simpleIntegral s` over the increment rectangles
`timeRect i t \ timeRect i s` (each a clean box `Ioc a b ×ˢ Aᵢ`), and the box-level moment
identities behind the set-level isometry: independence of a future box increment from the
past, the weighted diagonal second moment, the vanishing of the weighted off-diagonal cross
terms, and cross-integrability of two compensated masses.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Clamped compensator

The compensator of the quadratic variation, `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds`, in its
explicit clamped form `∑_i (referenceIntensity ν (timeRect i t)) · ξᵢ²`. -/

/-! ### Increment decomposition

The increment `simpleIntegral t − simpleIntegral s` decomposes (a.e.) over the
increment rectangles `timeRect i t \ timeRect i s`, the basis for the set-level
quadratic-variation isometry. -/

/-! ### Set-level quadratic-variation isometry

The increment squares onto the increment boxes; off-diagonal cross terms vanish
(independence + zero mean), and diagonal terms give the box intensities
(independence + `compensated_second_moment`). -/


theorem _root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBf : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => N.compensated B ω * N.compensated C ω) P := by
  have hBsq := _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hB hBf
  have hCsq := _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N hC hCf
  have hmeas : Measurable (fun ω => N.compensated B ω * N.compensated C ω) := by
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    exact ((ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _).mul
      ((ENNReal.measurable_toReal.comp (N.measurable_eval hC)).sub_const _)
  refine MeasureTheory.Integrable.mono'
    (hBsq.add hCsq) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  change ‖N.compensated B ω * N.compensated C ω‖ ≤ (N.compensated B ω)^2 + (N.compensated C ω)^2
  rw [Real.norm_eq_abs]
  rcases abs_cases (N.compensated B ω * N.compensated C ω) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    nlinarith [two_mul_le_add_sq (N.compensated B ω) (N.compensated C ω),
      two_mul_le_add_sq (N.compensated B ω) (-N.compensated C ω),
      sq_nonneg (N.compensated B ω), sq_nonneg (N.compensated C ω)]
end LevyStochCalc.Poisson.Compensated


