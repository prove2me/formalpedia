-- Prove2me | Definitions.Def_SourceProof_041f540df3d22dd188af52e6
-- name    : SourceProof_041f540df3d22dd188af52e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:15.333687+00:00
-- url     : https://prove2.me/theorems/349208d9-725a-4eeb-99b0-719c19c7eca5
-- title:
--   LevyStochCalc source module: SourceProof_041f540df3d22dd188af52e6
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.itoLevyIntegral_indicator_not_ae_zero` comes from the `NonvacuityDrivers` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityDrivers_F001

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


theorem _root_.Prove2MeSourceProof.h_041f540df3d22dd188af52e6 (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hApos : 0 < ν A) {T : ℝ} (hT : 0 < T) :
    ¬ Poisson.Compensated.stochasticIntegral N ℱ hℱ
        (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e) (measurable_indicator_mark hA)
        (_root_.Prove2MeSourceProof.h_d5966f17bb5aa768e87c164d ℱ hA)
        (lintegral_sq_indicator_mark_lt_top hA hAν) T
      =ᵐ[P] fun _ => (0 : ℝ) := by
  intro h
  have hzero : (fun ω => (‖Poisson.Compensated.stochasticIntegral N ℱ hℱ
        (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e) (LevyStochCalc.Examples.Nonvacuity.measurable_indicator_mark hA)
        (_root_.Prove2MeSourceProof.h_d5966f17bb5aa768e87c164d ℱ hA)
        (LevyStochCalc.Examples.Nonvacuity.lintegral_sq_indicator_mark_lt_top hA hAν) T ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 := (LevyStochCalc.Examples.Nonvacuity.lintegral_sq_itoLevyIntegral_indicator N ℱ hℱ hA hAν hT).symm.trans
    ((lintegral_congr_ae hzero).trans lintegral_zero)
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hApos.ne' h1
  · exact (ENNReal.ofReal_pos.mpr hT).ne' h1
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


