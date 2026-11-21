-- Prove2me | Definitions.Def_NonvacuityDrivers_F001
-- name    : NonvacuityDrivers_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:50.789854+00:00
-- url     : https://prove2.me/theorems/ee1ec862-7fc4-4041-8790-5b68befa9c9e
-- title:
--   Source declarations: NonvacuityDrivers
-- statement:
--   Source-preserving extracted declarations from NonvacuityDrivers. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityDrivers_F000
import Definitions.Def_SourceProof_d5966f17bb5aa768e87c164d

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

omit [SigmaFinite ν] in
/-- The `L²` energy of the mark indicator `1_A` on the window `[0, T]`. -/
theorem lintegral_sq_indicator_mark {A : Set E} (hA : MeasurableSet A) (T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖A.indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ν A * ENNReal.ofReal T := by
  have hpt : (fun e : E => (‖A.indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2)
      = A.indicator fun _ => (1 : ℝ≥0∞) := by
    funext e
    by_cases he : e ∈ A <;> simp [he]
  have hinner : ∫⁻ e, (‖A.indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν = ν A := by
    rw [hpt, lintegral_indicator hA]
    simp
  simp [hinner, Real.volume_Icc]
omit [SigmaFinite ν] in
/-- The mark indicator of a set of finite intensity has finite energy on every bounded
window. -/
theorem lintegral_sq_indicator_mark_lt_top {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) :
    ∀ T : ℝ, 0 < T →
      ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖A.indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T _
  rw [lintegral_sq_indicator_mark (P := P) hA T]
  exact (ENNReal.mul_ne_top hAν ENNReal.ofReal_ne_top).lt_top
variable (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- The Itô–Lévy integral of the mark indicator `1_A` on `[0, T]` has second moment
`ν A · T`. -/
theorem lintegral_sq_itoLevyIntegral_indicator (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖Poisson.Compensated.stochasticIntegral N ℱ hℱ
          (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e) (measurable_indicator_mark hA)
          (_root_.Prove2MeSourceProof.h_d5966f17bb5aa768e87c164d ℱ hA)
          (lintegral_sq_indicator_mark_lt_top hA hAν) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ν A * ENNReal.ofReal T := by
  rw [Poisson.L2Isometry.itoLevyIsometry N ℱ hℱ
      (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e) (measurable_indicator_mark hA)
      (_root_.Prove2MeSourceProof.h_d5966f17bb5aa768e87c164d ℱ hA)
      (lintegral_sq_indicator_mark_lt_top hA hAν) T hT,
    lintegral_sq_indicator_mark (P := P) hA T]
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


