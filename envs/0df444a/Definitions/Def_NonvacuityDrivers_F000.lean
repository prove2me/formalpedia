-- Prove2me | Definitions.Def_NonvacuityDrivers_F000
-- name    : NonvacuityDrivers_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:18.414431+00:00
-- url     : https://prove2.me/theorems/2d0d1925-628a-4e6a-a64e-5ebdf8592a3c
-- title:
--   Source declarations: NonvacuityDrivers
-- statement:
--   Source-preserving extracted declarations from NonvacuityDrivers. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_LevyStochCalc_Poisson_L2Isometry_F000
import Definitions.Def_SourceProof_9d62612e2dce26cbc374ccfb
import Definitions.Def_SourceProof_bfc6836a0f0c399780ee75a6

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

/-- A Brownian motion is not almost surely `0` at any time `t > 0`. -/
theorem brownian_not_ae_zero (W : Brownian.BrownianMotion P) {t : ℝ} (ht : 0 < t) :
    ¬ (fun ω => W.W t ω) =ᵐ[P] fun _ => (0 : ℝ) := by
  intro h
  have hzero : (fun ω => (‖W.W t ω‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 : ∫⁻ ω, (‖W.W t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rw [lintegral_congr_ae hzero, lintegral_zero]
  rw [_root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 W ht] at h0
  exact (ENNReal.ofReal_pos.mpr ht).ne' h0
/-- Each coordinate of a `d`-dimensional Brownian motion has second moment `t` at time
`t > 0`. -/
theorem lintegral_nnnorm_sq_multidimBrownian {d : ℕ}
    (W : Brownian.Multidim.MultidimBrownianMotion P d) (j : Fin d) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖(W.W j).W t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal t :=
  _root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 (W.W j) ht
/-- No coordinate of a `d`-dimensional Brownian motion is almost surely `0` at a time
`t > 0`. -/
theorem multidimBrownian_not_ae_zero {d : ℕ}
    (W : Brownian.Multidim.MultidimBrownianMotion P d) (j : Fin d) {t : ℝ} (ht : 0 < t) :
    ¬ (fun ω => (W.W j).W t ω) =ᵐ[P] fun _ => (0 : ℝ) :=
  brownian_not_ae_zero (W.W j) ht
end BrownianValue

section PoissonCount

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The reference intensity of the time-space box `(0, T] × A` is `T · ν A`. -/
theorem referenceIntensity_box (ν : Measure E) [SigmaFinite ν] (A : Set E) (T : ℝ) :
    Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) = ENNReal.ofReal T * ν A := by
  rw [Poisson.referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self),
    Real.volume_Ioc, sub_zero]
/-- The mean count of a Poisson random measure on the box `(0, T] × A` is `T · ν A`. -/
theorem lintegral_count_box (N : Poisson.PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∫⁻ ω, N.N ω (Set.Ioc (0 : ℝ) T ×ˢ A) ∂P = ENNReal.ofReal T * ν A := by
  have hfin : Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ := by
    rw [referenceIntensity_box ν A T]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAν
  rw [_root_.Prove2MeSourceProof.h_9d62612e2dce26cbc374ccfb N
      (measurableSet_Ioc.prod hA) hfin, referenceIntensity_box ν A T]
/-- The count of a Poisson random measure on a box of positive finite intensity is not almost
surely `0`. -/
theorem count_not_ae_zero (N : Poisson.PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hApos : 0 < ν A) {T : ℝ} (hT : 0 < T) :
    ¬ ∀ᵐ ω ∂P, N.N ω (Set.Ioc (0 : ℝ) T ×ˢ A) = 0 := by
  intro h
  have h0 : ∫⁻ ω, N.N ω (Set.Ioc (0 : ℝ) T ×ˢ A) ∂P = 0 := by
    rw [lintegral_congr_ae h, lintegral_zero]
  rw [lintegral_count_box N hA hAν T] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact (ENNReal.ofReal_pos.mpr hT).ne' h1
  · exact hApos.ne' h1
end PoissonCount

section ItoIntegralOne

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `L²` energy of the constant integrand `1` on the window `[0, T]`. -/
theorem lintegral_sq_one (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖(1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ENNReal.ofReal T := by
  simp [Real.volume_Icc]
/-- The constant integrand `1` has finite energy on every bounded window. -/
theorem lintegral_sq_one_lt_top (P : Measure Ω) [IsProbabilityMeasure P] :
    ∀ T : ℝ, 0 < T →
      ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖(1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _
  rw [lintegral_sq_one P T]
  exact ENNReal.ofReal_lt_top
variable (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- The Itô integral of the constant integrand `1` on `[0, T]` has second moment `T`. -/
theorem lintegral_sq_itoIntegral_one (hℱ : Brownian.IsBrownianFiltration W ℱ) {T : ℝ}
    (hT : 0 < T) :
    ∫⁻ ω, (‖Brownian.Ito.stochasticIntegral W ℱ hℱ (fun _ _ => (1 : ℝ)) measurable_const
          (Probability.progressivelyMeasurable_const ℱ (1 : ℝ))
          (lintegral_sq_one_lt_top P) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal T := by
  rw [Brownian.Ito.itoIsometry W ℱ hℱ (fun _ _ => (1 : ℝ)) T hT measurable_const
      (Probability.progressivelyMeasurable_const ℱ (1 : ℝ)) (lintegral_sq_one_lt_top P),
    lintegral_sq_one P T]
/-- The Itô integral of the constant integrand `1` on `[0, T]`, `T > 0`, is not almost surely
`0`. -/
theorem itoIntegral_one_not_ae_zero (hℱ : Brownian.IsBrownianFiltration W ℱ) {T : ℝ}
    (hT : 0 < T) :
    ¬ Brownian.Ito.stochasticIntegral W ℱ hℱ (fun _ _ => (1 : ℝ)) measurable_const
        (Probability.progressivelyMeasurable_const ℱ (1 : ℝ))
        (lintegral_sq_one_lt_top P) T
      =ᵐ[P] fun _ => (0 : ℝ) := by
  intro h
  have hzero : (fun ω => (‖Brownian.Ito.stochasticIntegral W ℱ hℱ (fun _ _ => (1 : ℝ))
        measurable_const (Probability.progressivelyMeasurable_const ℱ (1 : ℝ))
        (lintegral_sq_one_lt_top P) T ω‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 := (lintegral_sq_itoIntegral_one W ℱ hℱ hT).symm.trans
    ((lintegral_congr_ae hzero).trans lintegral_zero)
  exact (ENNReal.ofReal_pos.mpr hT).ne' h0
/-- The Itô integral of the constant integrand `1` against `W`, taken on the natural filtration
of `W`, has second moment `T` on `[0, T]`. -/
theorem lintegral_sq_itoIntegral_one_natural {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖Brownian.Ito.stochasticIntegral W (Brownian.Martingale.naturalFiltration W)
          (Brownian.isBrownianFiltration_natural W) (fun _ _ => (1 : ℝ)) measurable_const
          (Probability.progressivelyMeasurable_const
            (Brownian.Martingale.naturalFiltration W) (1 : ℝ))
          (lintegral_sq_one_lt_top P) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal T :=
  lintegral_sq_itoIntegral_one W _ (Brownian.isBrownianFiltration_natural W) hT
/-- The Itô integral of the constant integrand `1` against `W`, taken on the natural filtration
of `W`, is not almost surely `0` for `T > 0`. -/
theorem itoIntegral_one_natural_not_ae_zero {T : ℝ} (hT : 0 < T) :
    ¬ Brownian.Ito.stochasticIntegral W (Brownian.Martingale.naturalFiltration W)
        (Brownian.isBrownianFiltration_natural W) (fun _ _ => (1 : ℝ)) measurable_const
        (Probability.progressivelyMeasurable_const
          (Brownian.Martingale.naturalFiltration W) (1 : ℝ))
        (lintegral_sq_one_lt_top P) T
      =ᵐ[P] fun _ => (0 : ℝ) :=
  itoIntegral_one_not_ae_zero W _ (Brownian.isBrownianFiltration_natural W) hT
end ItoIntegralOne

section ItoLevyIntegralIndicator

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- Joint measurability of the mark indicator `1_A`, constant in time and in the sample
point. -/
theorem measurable_indicator_mark {A : Set E} (hA : MeasurableSet A) :
    Measurable fun p : Ω × ℝ × E => A.indicator (fun _ => (1 : ℝ)) p.2.2 :=
  (measurable_const.indicator hA).comp measurable_snd.snd
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


