-- Prove2me | Definitions.Def_Malliavin_KernelIdentification
-- name    : Malliavin_KernelIdentification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:41:08.173835+00:00
-- url     : https://prove2.me/theorems/671e6e60-6363-594f-a756-488e0e1d5a49
-- title:
--   Kernel Identification
-- statement:
--   Definitions and structural lemmas for Kernel Identification, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean

import Definitions.Def_Malliavin_PredictableKernel
import Definitions.Def_Malliavin_TimewiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Mathlib.MeasureTheory.Function.Floor
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_ae_pos_finiteHorizonTimeMeasure
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_condExpKernel_predictable_ae_same_time
import Theorems.Thm_Malliavin_condExp_natural_filtrationPred_ae_eq
import Theorems.Thm_Malliavin_condExp_timeSection_ae_eq_integral_condExpKernel
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_finiteHorizonProductMeasure_eq_restrict
import Theorems.Thm_Malliavin_memLp_timeSection_ae
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_predictableProjection_ae_eq_integral_predictableSectionKernel_Iic
import Theorems.Thm_Malliavin_secondCountableTopology_randomL2_of_isWienerGenerated
import Theorems.Thm_Malliavin_timeSection_predictableProjection_ae_eq_condExp
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
theorem timeSection_predictableProjection_ae_eq_integral_condExpKernel_natural
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      (fun w ↦ (predictableProjection (Filtration.natural B hm) U : ℝ≥0 × W → ℝ) (t, w))
        =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (Filtration.natural B hm t) w := by
  have _i : SecondCountableTopology (RandomL2 P) :=
    secondCountableTopology_randomL2_of_isWienerGenerated hB hgen
  set 𝓕 := Filtration.natural B hm with h𝓕
  have hmeas : AEStronglyMeasurable[𝓕.predictable]
      ((predictableProjection 𝓕 U : TimeProcessL2 P) : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := lpMeas.aestronglyMeasurable _
  have hlit := timeSection_predictableProjection_ae_eq_condExp 𝓕 U
    hmeas.stronglyMeasurable_mk hmeas.ae_eq_mk
  have hsec := Measure.ae_ae_of_ae_prod hmeas.ae_eq_mk
  filter_upwards [hlit, hsec, memLp_timeSection_ae U,
    condExp_timeSection_ae_eq_integral_condExpKernel 𝓕 U] with t hlt hst hUt hker hat
  have hint : Integrable (fun w ↦ U (t, w)) P := hUt.integrable one_le_two
  calc (fun w ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, w))
      =ᵐ[P] fun w ↦ hmeas.mk _ (t, w) := hst
    _ =ᵐ[P] P[(fun w ↦ U (t, w)) | filtrationPred 𝓕 t] := hlt hat
    _ =ᵐ[P] P[(fun w ↦ U (t, w)) | 𝓕 t] :=
        condExp_natural_filtrationPred_ae_eq hB hm t hat _ hint
    _ =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) w := hker
theorem integral_predictableSectionKernel_ae_eq_integral_condExpKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      ∀ᵐ w ∂P,
        ∫ y, U (t, y)
            ∂predictableSectionKernel (finiteHorizonProductMeasure P T)
              (Filtration.natural B hm) (t, w)
          = ∫ y, U (t, y) ∂condExpKernel P (Filtration.natural B hm t) w := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  have hpsk := predictableProjection_ae_eq_integral_predictableSectionKernel_Iic 𝓕 U T
  have hpsk' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, ∀ᵐ w ∂P,
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, w)
        = ∫ y, U (t, y)
            ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w) :=
    Measure.ae_ae_of_ae_prod hpsk
  have hker :=
    timeSection_predictableProjection_ae_eq_integral_condExpKernel_natural hB hm hgen U
  have hker' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      (fun w ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, w))
        =ᵐ[P] fun w ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) w :=
    ae_restrict_of_ae hker
  filter_upwards [hpsk', hker'] with t hpt hkt hat
  filter_upwards [hpt, hkt hat] with w hw1 hw2
  rw [← hw1]
  exact hw2
section KernelNull
variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
theorem condExpKernel_ae_null (hm : m ≤ mΩ) {N : Set Ω} (hN : MeasurableSet N)
    (h0 : μ N = 0) :
    ∀ᵐ ω ∂μ, condExpKernel μ m ω N = 0 := by
  have h := condExpKernel_ae_eq_condExp (μ := μ) hm hN
  have hind : (Set.indicator N (fun _ ↦ (1 : ℝ))) =ᵐ[μ] 0 := by
    have hmem : ∀ᵐ ω ∂μ, ω ∉ N := by
      rw [ae_iff]
      simpa using h0
    filter_upwards [hmem] with ω hω
    simp only [Set.indicator_of_notMem hω, Pi.zero_apply]
  have hzero : μ⟦N | m⟧ =ᵐ[μ] 0 := by
    refine (condExp_congr_ae hind).trans ?_
    rw [condExp_zero]
  filter_upwards [h, hzero] with ω h1 h2
  have hreal : (condExpKernel μ m ω).real N = 0 := by
    rw [h1, h2]
    rfl
  have hne : condExpKernel μ m ω N ≠ ∞ := measure_ne_top _ _
  rw [Measure.real] at hreal
  exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hne
theorem integral_condExpKernel_congr_ae (hm : m ≤ mΩ) {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    ∀ᵐ ω ∂μ, ∫ y, f y ∂condExpKernel μ m ω = ∫ y, g y ∂condExpKernel μ m ω := by
  have h0 : μ {x | f x ≠ g x} = 0 := hfg
  obtain ⟨N, hsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h0
  filter_upwards [condExpKernel_ae_null hm hNmeas hN0] with ω hω
  apply integral_congr_ae
  have : condExpKernel μ m ω {x | f x ≠ g x} = 0 :=
    measure_mono_null hsub hω
  exact this
end KernelNull
theorem predictableSectionKernel_ae_eq_condExpKernel_apply
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (T : ℝ≥0) {A : Set W} (hA : MeasurableSet A) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T)
            (Filtration.natural B hm) (t, w) A
          = condExpKernel P (Filtration.natural B hm t) w A := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  set μT := finiteHorizonProductMeasure P T with hμT
  -- the elementary test process `1_{Iic T × A}`
  have hR : MeasurableSet (Set.Iic T ×ˢ A) := measurableSet_Iic.prod hA
  have hRne : (nonnegativeLebesgueMeasure.prod P) (Set.Iic T ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (nonnegativeLebesgueMeasure_Iic_ne_top T) (measure_ne_top P A)
  set UA : TimeProcessL2 P := indicatorConstLp 2 hR hRne (1 : ℝ) with hUA
  have hcoe : (UA : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) := indicatorConstLp_coeFn
  -- a fixed measurable product-null discrepancy set
  have h0 : (nonnegativeLebesgueMeasure.prod P)
      {p | (UA : ℝ≥0 × W → ℝ) p ≠ (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) p} = 0 := hcoe
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h0
  have hμTN : μT N = 0 := by
    refine le_antisymm ?_ bot_le
    calc μT N ≤ (nonnegativeLebesgueMeasure.prod P) N := by
          rw [hμT, finiteHorizonProductMeasure_eq_restrict]
          exact Measure.restrict_le_self N
      _ = 0 := hN0
  -- main integral identification for `UA`
  have hmain := integral_predictableSectionKernel_ae_eq_integral_condExpKernel hB hm hgen UA T
  -- sections of the coefficient
  have hsec : ∀ᵐ t ∂finiteHorizonTimeMeasure T,
      (fun y ↦ (UA : ℝ≥0 × W → ℝ) (t, y)) =ᵐ[P]
        fun y ↦ (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) (t, y) :=
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hcoe)
  -- null and same-time facts for the product kernel
  have hnull := condExpKernel_ae_null (μ := μT) (predictable_le_prod 𝓕) hNmeas hμTN
  have hnull' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, ∀ᵐ w ∂P,
      condExpKernel μT 𝓕.predictable (t, w) N = 0 :=
    Measure.ae_ae_of_ae_prod hnull
  have hsame := condExpKernel_predictable_ae_same_time μT 𝓕
  have hsame' : ∀ᵐ t ∂finiteHorizonTimeMeasure T, ∀ᵐ w ∂P,
      ∀ᵐ q ∂condExpKernel μT 𝓕.predictable (t, w), q.1 = t :=
    Measure.ae_ae_of_ae_prod hsame
  filter_upwards [hmain, hsec, hnull', hsame', ae_restrict_mem measurableSet_Iic]
    with t hmt hst hnt hsamet htT hat
  -- fixed-time side: the kernel integral of the section is the kernel mass of `A`
  have hsecA : (fun y ↦ (UA : ℝ≥0 × W → ℝ) (t, y)) =ᵐ[P]
      fun y ↦ A.indicator (1 : W → ℝ) y := by
    refine hst.trans (Filter.Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ A <;> simp [Set.indicator, hy, htT]
  have hker := integral_condExpKernel_congr_ae (μ := P) (𝓕.le t) hsecA
  filter_upwards [hmt hat, hnt, hsamet, hker] with w hw1 hw2 hw3 hw4
  -- convert the fixed-time side
  have hRHS : ∫ y, (UA : ℝ≥0 × W → ℝ) (t, y) ∂condExpKernel P (𝓕 t) w
      = (condExpKernel P (𝓕 t) w).real A := by
    rw [hw4, integral_indicator_one hA]
  -- convert the predictable side
  have hLHS : ∫ y, (UA : ℝ≥0 × W → ℝ) (t, y)
      ∂predictableSectionKernel μT 𝓕 (t, w)
      = (predictableSectionKernel μT 𝓕 (t, w)).real A := by
    have hstep1 : ∫ y, (UA : ℝ≥0 × W → ℝ) (t, y)
        ∂predictableSectionKernel μT 𝓕 (t, w)
        = ∫ q, (UA : ℝ≥0 × W → ℝ) (t, q.2) ∂condExpKernel μT 𝓕.predictable (t, w) := by
      rw [predictableSectionKernel, Kernel.map_apply _ measurable_snd]
      exact integral_map measurable_snd.aemeasurable
        ((Lp.stronglyMeasurable UA).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [hstep1]
    have hcongr : ∫ q, (UA : ℝ≥0 × W → ℝ) (t, q.2)
        ∂condExpKernel μT 𝓕.predictable (t, w)
        = ∫ q, A.indicator (fun _ ↦ (1 : ℝ)) q.2
          ∂condExpKernel μT 𝓕.predictable (t, w) := by
      apply integral_congr_ae
      have hNzero : condExpKernel μT 𝓕.predictable (t, w) {q | q ∈ N} = 0 := hw2
      have hNae : ∀ᵐ q ∂condExpKernel μT 𝓕.predictable (t, w), q ∉ N := by
        rw [ae_iff]
        simpa using hNzero
      filter_upwards [hw3, hNae] with q hq1 hq2
      have hqval : (UA : ℝ≥0 × W → ℝ) q
          = (Set.Iic T ×ˢ A).indicator (fun _ ↦ (1 : ℝ)) q := by
        by_contra hne
        exact hq2 (hNsub hne)
      have : (UA : ℝ≥0 × W → ℝ) (t, q.2) = (UA : ℝ≥0 × W → ℝ) q := by
        congr 1
        exact Prod.ext hq1.symm rfl
      rw [this, hqval]
      by_cases hy : q.2 ∈ A
      · have hqmem : q ∈ Set.Iic T ×ˢ A := ⟨hq1 ▸ htT, hy⟩
        simp only [Set.indicator_of_mem hqmem, Set.indicator_of_mem hy]
      · have hqmem : q ∉ Set.Iic T ×ˢ A := fun hmem ↦ hy hmem.2
        simp only [Set.indicator_of_notMem hqmem, Set.indicator_of_notMem hy]
    rw [hcongr]
    have hint : ∫ q, A.indicator (fun _ ↦ (1 : ℝ)) q.2
        ∂condExpKernel μT 𝓕.predictable (t, w)
        = (condExpKernel μT 𝓕.predictable (t, w)).real (Prod.snd ⁻¹' A) := by
      have hfun : (fun q : ℝ≥0 × W ↦ A.indicator (fun _ ↦ (1 : ℝ)) q.2)
          = fun q ↦ (Prod.snd ⁻¹' A).indicator (1 : ℝ≥0 × W → ℝ) q := by
        funext q
        by_cases hy : q.2 ∈ A <;> simp [Set.indicator, hy]
      rw [hfun, integral_indicator_one (measurable_snd hA)]
    rw [hint, predictableSectionKernel, Kernel.map_apply _ measurable_snd]
    unfold Measure.real
    rw [Measure.map_apply measurable_snd hA]
  -- conclude: equal real masses of finite measures
  have hreal : (predictableSectionKernel μT 𝓕 (t, w)).real A
      = (condExpKernel P (𝓕 t) w).real A := by
    rw [← hLHS, ← hRHS, hw1]
  have hne1 : predictableSectionKernel μT 𝓕 (t, w) A ≠ ∞ := by
    rw [predictableSectionKernel, Kernel.map_apply' _ measurable_snd _ hA]
    exact measure_ne_top _ _
  have hne2 : condExpKernel P (𝓕 t) w A ≠ ∞ := measure_ne_top _ _
  unfold Measure.real at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp hreal
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] in
/-- A finite measure and another measure on `W` agreeing on the rational sub-level sets of a
measurable embedding into `ℝ`, and on `univ`, are equal. -/
theorem measure_ext_of_measurableEmbedding_Iic_rat {μ₁ μ₂ : Measure W} {f : W → ℝ}
    (hf : MeasurableEmbedding f) [IsFiniteMeasure μ₁]
    (h : ∀ q : ℚ, μ₁ (f ⁻¹' Set.Iic (q : ℝ)) = μ₂ (f ⁻¹' Set.Iic (q : ℝ)))
    (huniv : μ₁ Set.univ = μ₂ Set.univ) : μ₁ = μ₂ := by
  have hmap : μ₁.map f = μ₂.map f := by
    have h1 : IsFiniteMeasure (μ₁.map f) := by
      refine ⟨?_⟩
      rw [Measure.map_apply hf.measurable MeasurableSet.univ]
      exact measure_lt_top _ _
    refine ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat
      Real.isPiSystem_Iic_rat ?_ ?_
    · intro s hs
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
      obtain ⟨q, rfl⟩ := hs
      rw [Measure.map_apply hf.measurable measurableSet_Iic,
        Measure.map_apply hf.measurable measurableSet_Iic]
      exact h q
    · rw [Measure.map_apply hf.measurable MeasurableSet.univ,
        Measure.map_apply hf.measurable MeasurableSet.univ]
      simpa using huniv
  ext A hA
  have h1 : μ₁ A = (μ₁.map f) (f '' A) := by
    rw [Measure.map_apply hf.measurable (hf.measurableSet_image' hA),
      hf.injective.preimage_image]
  have h2 : μ₂ A = (μ₂.map f) (f '' A) := by
    rw [Measure.map_apply hf.measurable (hf.measurableSet_image' hA),
      hf.injective.preimage_image]
  rw [h1, h2, hmap]
theorem predictableSectionKernel_ae_eq_condExpKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T)
            (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real (α := W)
  have hall : ∀ q : ℚ, ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t → ∀ᵐ w ∂P,
      predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)
          (f ⁻¹' Set.Iic (q : ℝ))
        = condExpKernel P (𝓕 t) w (f ⁻¹' Set.Iic (q : ℝ)) := fun q ↦
    predictableSectionKernel_ae_eq_condExpKernel_apply hB hm hgen T
      (hf.measurable measurableSet_Iic)
  have huniv := predictableSectionKernel_ae_eq_condExpKernel_apply hB hm hgen T
    (MeasurableSet.univ (α := W))
  have hall' := ae_all_iff.mpr hall
  filter_upwards [hall', huniv] with t ht hu hat
  have hq : ∀ᵐ w ∂P, ∀ q : ℚ,
      predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)
          (f ⁻¹' Set.Iic (q : ℝ))
        = condExpKernel P (𝓕 t) w (f ⁻¹' Set.Iic (q : ℝ)) :=
    ae_all_iff.mpr fun q ↦ ht q hat
  filter_upwards [hq, hu hat] with w hwq hwu
  have hfin1 : IsFiniteMeasure
      (predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w)) := by
    refine ⟨?_⟩
    rw [hwu]
    exact measure_lt_top _ _
  exact measure_ext_of_measurableEmbedding_Iic_rat hf hwq hwu
noncomputable def globalPredictableSectionKernelFun (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) : ℝ≥0 × W → Measure W :=
  (fun q : ℕ × (ℝ≥0 × W) ↦
      predictableSectionKernel (finiteHorizonProductMeasure P (q.1 : ℝ≥0)) 𝓕 q.2)
    ∘ fun p ↦ ((⌈p.1⌉₊ : ℕ), p)
theorem measurable_globalPredictableSectionKernelFun (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Measurable (ℝ≥0 × W) (Measure W) 𝓕.predictable inferInstance
      (globalPredictableSectionKernelFun P 𝓕) := by
  have h2 : @Measurable (ℕ × (ℝ≥0 × W)) (Measure W)
      (@Prod.instMeasurableSpace ℕ (ℝ≥0 × W) inferInstance 𝓕.predictable) inferInstance
      (fun q ↦ predictableSectionKernel (finiteHorizonProductMeasure P (q.1 : ℝ≥0)) 𝓕 q.2) :=
    measurable_from_prod_countable_right
      fun n ↦ (predictableSectionKernel (finiteHorizonProductMeasure P (n : ℝ≥0)) 𝓕).measurable
  have h1 : @Measurable (ℝ≥0 × W) (ℕ × (ℝ≥0 × W)) 𝓕.predictable
      (@Prod.instMeasurableSpace ℕ (ℝ≥0 × W) inferInstance 𝓕.predictable)
      (fun p ↦ ((⌈p.1⌉₊ : ℕ), p)) :=
    (Measurable.comp Nat.measurable_ceil (measurable_fst_predictable 𝓕)).prodMk measurable_id
  exact h2.comp h1
noncomputable def globalPredictableSectionKernel (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Kernel (ℝ≥0 × W) W 𝓕.predictable inferInstance :=
  @Kernel.mk (ℝ≥0 × W) W 𝓕.predictable inferInstance
    (globalPredictableSectionKernelFun P 𝓕)
    (measurable_globalPredictableSectionKernelFun P 𝓕)
@[simp]
theorem globalPredictableSectionKernel_apply (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (p : ℝ≥0 × W) :
    globalPredictableSectionKernel P 𝓕 p =
      predictableSectionKernel (finiteHorizonProductMeasure P ((⌈p.1⌉₊ : ℕ) : ℝ≥0)) 𝓕 p := rfl
instance instIsMarkovKernelGlobalPredictableSectionKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    IsMarkovKernel (globalPredictableSectionKernel P 𝓕) := by
  constructor
  intro p
  rw [globalPredictableSectionKernel_apply]
  exact IsMarkovKernel.isProbabilityMeasure p
theorem globalPredictableSectionKernel_ae_eq_condExpKernel_of_pos
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      ∀ᵐ w ∂P,
        globalPredictableSectionKernel P (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by
  have hn : ∀ n : ℕ, ∀ᵐ t ∂nonnegativeLebesgueMeasure, t ∈ Set.Iic ((n : ℕ) : ℝ≥0) →
      0 < t → ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P ((n : ℕ) : ℝ≥0))
            (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := fun n ↦
    ae_imp_of_ae_restrict
      (predictableSectionKernel_ae_eq_condExpKernel hB hm hgen ((n : ℕ) : ℝ≥0))
  have hall := ae_all_iff.mpr hn
  filter_upwards [hall] with t ht hat
  have hceil : t ≤ ((⌈t⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil t
  have hkey := ht ⌈t⌉₊ (Set.mem_Iic.mpr hceil) hat
  filter_upwards [hkey] with w hw
  rw [globalPredictableSectionKernel_apply]
  exact hw
theorem stronglyMeasurable_integral_globalPredictableSectionKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) :
    StronglyMeasurable[𝓕.predictable]
      (fun p ↦ ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p) := by
  exact StronglyMeasurable.integral_kernel_prod_right'
    (κ := globalPredictableSectionKernel P 𝓕)
    ((Lp.stronglyMeasurable U).comp_measurable
      (((measurable_fst_predictable 𝓕).comp measurable_fst).prodMk measurable_snd))
theorem integral_predictableSectionKernel_ae_eq_integral_globalPredictableSectionKernel_Iic
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (fun p ↦ ∫ y, U (p.1, y)
        ∂predictableSectionKernel (finiteHorizonProductMeasure P T)
          (Filtration.natural B hm) p)
      =ᵐ[finiteHorizonProductMeasure P T]
    fun p ↦ ∫ y, U (p.1, y)
        ∂globalPredictableSectionKernel P (Filtration.natural B hm) p := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  -- both functions are product measurable
  have hm1 : Measurable (fun p ↦ ∫ y, U (p.1, y)
      ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p) :=
    ((StronglyMeasurable.integral_kernel_prod_right'
      (κ := predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕)
      ((Lp.stronglyMeasurable U).comp_measurable
        (((measurable_fst_predictable 𝓕).comp measurable_fst).prodMk measurable_snd))).mono
      (predictable_le_prod 𝓕)).measurable
  have hm2 : Measurable (fun p ↦ ∫ y, U (p.1, y)
      ∂globalPredictableSectionKernel P 𝓕 p) :=
    ((stronglyMeasurable_integral_globalPredictableSectionKernel 𝓕 U).mono
      (predictable_le_prod 𝓕)).measurable
  have hE : MeasurableSet {p : ℝ≥0 × W |
      (∫ y, U (p.1, y) ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p)
        ≠ ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p} :=
    (measurableSet_eq_fun hm1 hm2).compl
  -- almost every time, almost every sample the kernels agree
  have hker1 := predictableSectionKernel_ae_eq_condExpKernel hB hm hgen T
  have hker2 : ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t → ∀ᵐ w ∂P,
      globalPredictableSectionKernel P 𝓕 (t, w) = condExpKernel P (𝓕 t) w :=
    ae_restrict_of_ae (globalPredictableSectionKernel_ae_eq_condExpKernel_of_pos hB hm hgen)
  rw [Filter.EventuallyEq, ae_iff]
  change ((finiteHorizonTimeMeasure T).prod P) _ = 0
  apply Measure.measure_prod_null_of_ae_null hE
  filter_upwards [hker1, hker2, ae_pos_finiteHorizonTimeMeasure T] with t h1 h2 hat
  have hsec : ∀ᵐ w ∂P,
      (∫ y, U (t, y) ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 (t, w))
        = ∫ y, U (t, y) ∂globalPredictableSectionKernel P 𝓕 (t, w) := by
    filter_upwards [h1 hat, h2 hat] with w hw1 hw2
    rw [hw1, hw2]
  rw [ae_iff] at hsec
  exact hsec
theorem predictableProjection_ae_eq_integral_globalPredictableSectionKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    (predictableProjection (Filtration.natural B hm) U : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p ↦ ∫ y, U (p.1, y)
          ∂globalPredictableSectionKernel P (Filtration.natural B hm) p := by
  set 𝓕 := Filtration.natural B hm with h𝓕
  -- almost everywhere on each horizon
  have hn : ∀ n : ℕ,
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
        =ᵐ[finiteHorizonProductMeasure P ((n : ℕ) : ℝ≥0)]
      fun p ↦ ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p := fun n ↦
    (predictableProjection_ae_eq_integral_predictableSectionKernel_Iic 𝓕 U ((n : ℕ) : ℝ≥0)).trans
      (integral_predictableSectionKernel_ae_eq_integral_globalPredictableSectionKernel_Iic
        hB hm hgen U ((n : ℕ) : ℝ≥0))
  -- pass from all finite horizons to the full time axis
  rw [Filter.EventuallyEq, ae_iff]
  set S := {p : ℝ≥0 × W | ¬(predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) p
      = ∫ y, U (p.1, y) ∂globalPredictableSectionKernel P 𝓕 p} with hS
  have hcover : S ⊆ ⋃ n : ℕ, S ∩ (Set.Iic ((n : ℕ) : ℝ≥0) ×ˢ Set.univ) := by
    intro p hp
    obtain ⟨n, hn'⟩ := exists_nat_ge p.1
    exact Set.mem_iUnion.mpr ⟨n, hp, Set.mem_Iic.mpr hn', Set.mem_univ _⟩
  refine le_antisymm (le_trans (measure_mono hcover) (le_trans (measure_iUnion_le _) ?_)) bot_le
  have hzero : ∀ n : ℕ,
      (nonnegativeLebesgueMeasure.prod P) (S ∩ (Set.Iic ((n : ℕ) : ℝ≥0) ×ˢ Set.univ)) = 0 := by
    intro n
    have hres := hn n
    rw [Filter.EventuallyEq, ae_iff] at hres
    rw [finiteHorizonProductMeasure_eq_restrict,
      Measure.restrict_apply' (measurableSet_Iic.prod MeasurableSet.univ)] at hres
    exact hres
  simp only [hzero, tsum_zero, Std.le_refl]
theorem memLp_integral_globalPredictableSectionKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    MemLp (fun p ↦ ∫ y, U (p.1, y)
        ∂globalPredictableSectionKernel P (Filtration.natural B hm) p) 2
      (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp (predictableProjection (Filtration.natural B hm) U : TimeProcessL2 P)).ae_eq
    (predictableProjection_ae_eq_integral_globalPredictableSectionKernel hB hm hgen U)
section ClarkOcone
end ClarkOcone
end Malliavin


