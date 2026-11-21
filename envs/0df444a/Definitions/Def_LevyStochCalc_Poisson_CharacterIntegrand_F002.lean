-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F002
-- name    : LevyStochCalc_Poisson_CharacterIntegrand_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:33:13.892446+00:00
-- url     : https://prove2.me/theorems/73a0e4a8-3563-407b-9175-db3838a248c5
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterIntegrand_F001
import Definitions.Def_SourceProof_099fb631e9952e9258da9935

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)

theorem charRe_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {s : ℝ} {e : E}
    (he : (s, e) ∉ Set.Ioc (0 : ℝ) T ×ˢ A) : charRe N w Bfam A T ω s e = 0 := by
  rw [charRe, charIntegrand_eq_zero N w hBsub ω he, Complex.zero_re]
theorem charIm_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {s : ℝ} {e : E}
    (he : (s, e) ∉ Set.Ioc (0 : ℝ) T ×ˢ A) : charIm N w Bfam A T ω s e = 0 := by
  rw [charIm, charIntegrand_eq_zero N w hBsub ω he, Complex.zero_im]
omit [SigmaFinite ν] in
/-- A bounded integrand carried by a window of finite mark measure has finite energy. -/
theorem lintegral_sq_of_bounded {φ : Ω → ℝ → E → ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hbd : ∀ ω s e, ‖φ ω s e‖ ≤ 2) (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0)
    (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω s e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ≤ A.indicator (fun _ => (4 : ℝ≥0∞)) e := by
    intro ω s e
    by_cases he : e ∈ A
    · rw [Set.indicator_of_mem he]
      have h2 : (‖φ ω s e‖₊ : ℝ≥0∞) ≤ 2 := by
        rw [show ((2 : ℝ≥0∞)) = ((2 : ℝ≥0) : ℝ≥0∞) from by norm_num]
        exact ENNReal.coe_le_coe.mpr (by
          rw [← NNReal.coe_le_coe]
          simpa using hbd ω s e)
      calc (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ≤ (2 : ℝ≥0∞) ^ 2 := pow_le_pow_left' h2 2
        _ = 4 := by norm_num
    · rw [Set.indicator_of_notMem he, hsupp ω s e he]
      simp
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s =>
    lintegral_mono fun e => hpt ω s e) ?_
  rw [show (fun s : ℝ => ∫⁻ e, A.indicator (fun _ => (4 : ℝ≥0∞)) e ∂ν)
      = fun _ : ℝ => 4 * ν A from by
    funext s
    rw [lintegral_indicator hA, setLIntegral_const]]
  rw [setLIntegral_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hAν))
    measure_Icc_lt_top
theorem sq_charRe (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖charRe N w Bfam A T ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_of_bounded hA hAν
    (fun ω s e => le_trans (by
      rw [charRe, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _) (_root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w Bfam A T ω s e))
    (fun ω s e he => charRe_eq_zero N w hBsub ω fun hmem => he hmem.2) T'
theorem sq_charIm (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖charIm N w Bfam A T ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_of_bounded hA hAν
    (fun ω s e => le_trans (by
      rw [charIm, Real.norm_eq_abs]
      exact Complex.abs_im_le_norm _) (_root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w Bfam A T ω s e))
    (fun ω s e he => charIm_eq_zero N w hBsub ω fun hmem => he hmem.2) T'
end Integrand

section Assembly

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The character's increment is the integral of the predictable integrand against the random
measure.** -/
theorem ae_char_sub_one_eq_setIntegral (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P,
      Complex.exp (Complex.I * (windowSum N (⋃ j, Bfam j) (simpleMark w Bfam) T ω : ℂ)) - 1
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, charIntegrand N w Bfam A T ω q.1 q.2 ∂(N.N ω) := by
  classical
  have hBm' : MeasurableSet (⋃ j, Bfam j) := MeasurableSet.iUnion hBm
  have hBsub' : (⋃ j, Bfam j) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := Set.iUnion_subset hBsub
  have hBfin : referenceIntensity ν (⋃ j, Bfam j) ≠ ⊤ :=
    ne_top_of_le_ne_top (referenceIntensity_Ioc_prod_ne_top hAν T) (measure_mono hBsub')
  have hBinter : (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ = ⋃ j, Bfam j :=
    Set.inter_eq_self_of_subset_left fun p hp => ⟨(hBsub' hp).1, Set.mem_univ _⟩
  filter_upwards [ae_exp_windowSum_sub_one N hBm' hBfin (simpleMark w Bfam) T,
    ae_windowSum_simple N hAν w hBm hBsub] with ω hchain hsim
  have hpt : Set.EqOn (fun q : ℝ × E => charIntegrand N w Bfam A T ω q.1 q.2)
      ((⋃ j, Bfam j).indicator (fun p : ℝ × E =>
        Complex.exp (Complex.I *
            (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) p.1 ω : ℂ))
          * (Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1)))
      (Set.Ioc (0 : ℝ) T ×ˢ A) := by
    intro q hq
    have hq1 : (0 : ℝ) < q.1 := hq.1.1
    have hq2 : q.1 ≤ T := hq.1.2
    have hq3 : q.2 ∈ A := hq.2
    simp only [charIntegrand]
    rw [predStrict_eq N w Bfam hq1 hq2 hq3 ω, ← (hsim q.1).2]
    by_cases hmem : q ∈ ⋃ j, Bfam j
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  rw [hchain, setIntegral_congr_fun (measurableSet_Ioc.prod hA) hpt, setIntegral_indicator hBm',
    Set.inter_eq_self_of_subset_right hBsub', hBinter]
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem measurable_charRe (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Measurable fun p : Ω × ℝ × E => charRe N w Bfam A T p.1 p.2.1 p.2.2 :=
  (markedPredictable_charRe N hℱ w hBm hA hAν hBsub).mono
    (Probability.markedPredictableSigma_le ℱ ν) le_rfl
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem measurable_charIm (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Measurable fun p : Ω × ℝ × E => charIm N w Bfam A T p.1 p.2.1 p.2.2 :=
  (markedPredictable_charIm N hℱ w hBm hA hAν hBsub).mono
    (Probability.markedPredictableSigma_le ℱ ν) le_rfl
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The complex integral splits into its real and imaginary parts. -/
theorem setIntegral_complex_split {μ : Measure (ℝ × E)} {g : ℝ × E → ℂ} {W : Set (ℝ × E)}
    (hg : IntegrableOn g W μ) :
    ∫ q in W, g q ∂μ
      = ((∫ q in W, (g q).re ∂μ : ℝ) : ℂ) + ((∫ q in W, (g q).im ∂μ : ℝ) : ℂ) * Complex.I := by
  have h1 : ∫ q in W, (g q).re ∂μ = (∫ q in W, g q ∂μ).re := integral_re hg
  have h2 : ∫ q in W, (g q).im ∂μ = (∫ q in W, g q ∂μ).im := integral_im hg
  rw [h1, h2, Complex.re_add_im]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The chain rule's integrand is integrable over the window against any finite measure. -/
theorem integrableOn_charIntegrand (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {μ : Measure (ℝ × E)}
    [IsFiniteMeasure (μ.restrict (Set.Ioc (0 : ℝ) T ×ˢ A))] :
    IntegrableOn (fun q : ℝ × E => charIntegrand N w Bfam A T ω q.1 q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ A) μ := by
  have hm : Measurable fun q : ℝ × E => charIntegrand N w Bfam A T ω q.1 q.2 :=
    ((_root_.Prove2MeSourceProof.h_ac442bc7d640aae9c9b7360e N hℱ w hBm hA hAν hBsub).mono
      (Probability.markedPredictableSigma_le ℱ ν) le_rfl).comp measurable_prodMk_left
  refine Integrable.mono' (integrable_const (2 : ℝ)) hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun q => _root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w Bfam A T ω q.1 q.2
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charIntegrand_re (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    (charIntegrand N w Bfam A T ω s e).re = charRe N w Bfam A T ω s e := rfl
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem charIntegrand_im (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    (charIntegrand N w Bfam A T ω s e).im = charIm N w Bfam A T ω s e := rfl
end Assembly

end LevyStochCalc.Poisson


