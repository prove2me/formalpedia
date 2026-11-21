-- Prove2me | Definitions.Def_SourceProof_bfc6836a0f0c399780ee75a6
-- name    : SourceProof_bfc6836a0f0c399780ee75a6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:12:25.212189+00:00
-- url     : https://prove2.me/theorems/33568895-5795-4270-ad86-0c0453717c10
-- title:
--   LevyStochCalc source module: SourceProof_bfc6836a0f0c399780ee75a6
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.lintegral_nnnorm_sq_brownian` comes from the `NonvacuityDrivers` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_LevyStochCalc_Poisson_L2Isometry_F000
import Definitions.Def_SourceProof_0d5475ecda5b11387d030812

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the drivers and of their stochastic integrals

The basic objects of the library carry the second moments prescribed by the classical theory,
and are therefore distinct from the trivial process, the zero measure and the zero integral.

## Main statements

* `lintegral_nnnorm_sq_brownian` — `𝔼‖W_t‖² = t`, and `brownian_not_ae_zero` — `W_t ≠ 0`
  almost surely for `t > 0`.
* `lintegral_count_box` — `𝔼[N((0, T] × A)] = T · ν A`, and `count_not_ae_zero`.
* `lintegral_sq_itoIntegral_one` — the Itô integral of the constant integrand `1` over `[0, T]`
  has second moment `T`, and `itoIntegral_one_not_ae_zero`.
* `lintegral_sq_itoLevyIntegral_indicator` — the Itô–Lévy integral of the mark indicator `1_A`
  over `[0, T]` has second moment `ν A · T`, and `itoLevyIntegral_indicator_not_ae_zero`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.2, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.2.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

universe u v

section BrownianValue

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 (W : Brownian.BrownianMotion P) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖W.W t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal t := by
  have hmeas : Measurable fun ω => W.W t ω - W.W 0 ω :=
    (W.measurable_eval t).sub (W.measurable_eval 0)
  have hmem : MemLp (fun ω => W.W t ω - W.W 0 ω) 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
      (_root_.Prove2MeSourceProof.h_0d5475ecda5b11387d030812 W le_rfl ht)
  have hae : (fun ω => (‖W.W t ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖W.W t ω - W.W 0 ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [W.initial_zero] with ω hω
    rw [hω, sub_zero]
  rw [lintegral_congr_ae hae, Brownian.Ito.lintegral_nnnorm_sq_eq_ofReal_integral hmem,
    Brownian.Ito.brownian_incr_sq_integral W le_rfl ht, sub_zero]
end BrownianValue

section PoissonCount

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end PoissonCount

section ItoIntegralOne

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end ItoIntegralOne

section ItoLevyIntegralIndicator

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end ItoLevyIntegralIndicator

end LevyStochCalc.Examples.Nonvacuity

section Audit

open LevyStochCalc.Examples.Nonvacuity

-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_nnnorm_sq_brownian
-- P2M_SOURCE_AUDIT_ONLY: #print axioms brownian_not_ae_zero
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_nnnorm_sq_multidimBrownian
-- P2M_SOURCE_AUDIT_ONLY: #print axioms multidimBrownian_not_ae_zero
-- P2M_SOURCE_AUDIT_ONLY: #print axioms referenceIntensity_box
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_count_box
-- P2M_SOURCE_AUDIT_ONLY: #print axioms count_not_ae_zero
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_one
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_one_lt_top
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_itoIntegral_one
-- P2M_SOURCE_AUDIT_ONLY: #print axioms itoIntegral_one_not_ae_zero
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_itoIntegral_one_natural
-- P2M_SOURCE_AUDIT_ONLY: #print axioms itoIntegral_one_natural_not_ae_zero
-- P2M_SOURCE_AUDIT_ONLY: #print axioms measurable_indicator_mark
-- P2M_SOURCE_AUDIT_ONLY: #print axioms markedProgressivelyMeasurable_indicator_mark
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_indicator_mark
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_indicator_mark_lt_top
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_itoLevyIntegral_indicator
-- P2M_SOURCE_AUDIT_ONLY: #print axioms itoLevyIntegral_indicator_not_ae_zero
-- P2M_SOURCE_AUDIT_ONLY: #print axioms lintegral_sq_itoLevyIntegral_indicator_natural
-- P2M_SOURCE_AUDIT_ONLY: #print axioms itoLevyIntegral_indicator_natural_not_ae_zero

end Audit


