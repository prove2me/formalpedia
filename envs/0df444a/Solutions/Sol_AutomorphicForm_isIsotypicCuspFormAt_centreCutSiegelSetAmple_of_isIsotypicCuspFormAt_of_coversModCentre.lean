-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5e1606fe-b3d1-527d-bac2-f35ccdd68d5c

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

noncomputable section

namespace WindowMultiplicity

variable (F : Type) [Field F] [NumberField F]

private abbrev ratGroup : Subgroup (AdelicGL2 (𝓞 F) F) := (AutomorphicForm.globalPoints (𝓞 F) F).range

private def detBand (α β : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

section countability

private theorem countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem countable_matrix : Countable (Matrix (Fin 2) (Fin 2) F) :=
  haveI : Countable F := countable_numberField F
  (Matrix.of (m := Fin 2) (n := Fin 2) (α := F)).symm.injective.countable

private theorem countable_GL : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
  haveI := countable_matrix F
  Units.val_injective.countable

private theorem countable_ratGroup : Countable (ratGroup F) :=
  haveI := countable_GL F
  (Set.countable_range (AutomorphicForm.globalPoints (𝓞 F) F)).to_subtype

end countability

variable {F}

private theorem smul_mem_detBand_iff (α β : ℝ) (γ : ratGroup F) (g : AdelicGL2 (𝓞 F) F) :
    γ • g ∈ detBand F α β ↔ g ∈ detBand F α β := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  have hdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ← hγ₀, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  show (γ : AdelicGL2 (𝓞 F) F) * g ∈ detBand F α β ↔ g ∈ detBand F α β
  simp only [detBand, Set.mem_setOf_eq, hdet]

private theorem preimage_smul_detBand (α β : ℝ) (γ : ratGroup F) :
    (fun g : AdelicGL2 (𝓞 F) F => γ • g) ⁻¹' detBand F α β = detBand F α β := by
  ext g
  exact smul_mem_detBand_iff α β γ g

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem measurableConstSMul_ratGroup : MeasurableConstSMul (ratGroup F) (AdelicGL2 (𝓞 F) F) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  exact ⟨fun γ => ((continuous_const (y := (γ : AdelicGL2 (𝓞 F) F))).mul continuous_id).measurable⟩

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem smulInvariantMeasure_restrict_detBand (α β : ℝ) :
    SMulInvariantMeasure (ratGroup F) (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detBand F α β)) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨?_⟩
  intro γ s hs
  have hmeas : MeasurableSet ((fun g : AdelicGL2 (𝓞 F) F => γ • g) ⁻¹' s) :=
    ((continuous_const (y := (γ : AdelicGL2 (𝓞 F) F))).mul continuous_id).measurable hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs, ← preimage_smul_detBand α β γ, ← Set.preimage_inter,
    preimage_smul_detBand α β γ]
  show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * g) ⁻¹'
    (s ∩ detBand F α β)) = adelicGLHaar (Fin 2) (𝓞 F) F (s ∩ detBand F α β)
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) _

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem setLIntegral_le_mul_of_forall_ncard_le
    (α β : ℝ) (W S : Set (AdelicGL2 (𝓞 F) F)) (hWm : MeasurableSet W) (hW : W ⊆ detBand F α β)
    (hS : IsFundamentalDomain (ratGroup F) S ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detBand F α β)))
    (N : ℕ)
    (hN : ∀ h : AdelicGL2 (𝓞 F) F,
      {γ : Matrix.GeneralLinearGroup (Fin 2) F | AutomorphicForm.globalPoints (𝓞 F) F γ * h ∈ W}.Finite ∧
        {γ : Matrix.GeneralLinearGroup (Fin 2) F | AutomorphicForm.globalPoints (𝓞 F) F γ * h ∈ W}.ncard ≤ N)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφm : Measurable φ)
    (hφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g) :
    ∫⁻ g in W, ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ (N : ENNReal) * ∫⁻ g in S, ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : Countable (ratGroup F) := countable_ratGroup F
  haveI : MeasurableConstSMul (ratGroup F) (AdelicGL2 (𝓞 F) F) := measurableConstSMul_ratGroup
  haveI : SMulInvariantMeasure (ratGroup F) (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detBand F α β)) := smulInvariantMeasure_restrict_detBand α β
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set f : AdelicGL2 (𝓞 F) F → ENNReal := fun g => (‖φ g‖₊ : ENNReal) ^ 2 with hf
  have hfm : Measurable f := (hφm.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hfinv : ∀ (γ : ratGroup F) (g : AdelicGL2 (𝓞 F) F), f (γ • g) = f g := by
    intro γ g
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    show (‖φ ((γ : AdelicGL2 (𝓞 F) F) * g)‖₊ : ENNReal) ^ 2 = (‖φ g‖₊ : ENNReal) ^ 2
    rw [← hγ₀, hφ]

  have hcount : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' γ : ratGroup F, {γ' : ratGroup F | γ' • g ∈ W}.indicator (fun _ => f g) γ) ≤ (N : ENNReal) * f g := by
    intro g
    rw [← tsum_subtype, ENNReal.tsum_set_const]
    refine mul_le_mul' ?_ le_rfl
    obtain ⟨hfin, hcard⟩ := hN g
    have hsub : {γ' : ratGroup F | γ' • g ∈ W} ⊆
        (fun γ₀ : Matrix.GeneralLinearGroup (Fin 2) F =>
            (⟨AutomorphicForm.globalPoints (𝓞 F) F γ₀, MonoidHom.mem_range.mpr ⟨γ₀, rfl⟩⟩ : ratGroup F)) ''
          {γ₀ : Matrix.GeneralLinearGroup (Fin 2) F | AutomorphicForm.globalPoints (𝓞 F) F γ₀ * g ∈ W} := by
      intro γ' hγ'
      obtain ⟨γ₀, hγ₀⟩ := γ'.2
      refine ⟨γ₀, ?_, Subtype.ext hγ₀⟩
      show AutomorphicForm.globalPoints (𝓞 F) F γ₀ * g ∈ W
      rw [hγ₀]
      exact hγ'
    have hle : {γ' : ratGroup F | γ' • g ∈ W}.encard ≤ (N : ℕ∞) :=
      calc {γ' : ratGroup F | γ' • g ∈ W}.encard
          ≤ ((fun γ₀ : Matrix.GeneralLinearGroup (Fin 2) F =>
              (⟨AutomorphicForm.globalPoints (𝓞 F) F γ₀, MonoidHom.mem_range.mpr ⟨γ₀, rfl⟩⟩ : ratGroup F)) ''
            {γ₀ : Matrix.GeneralLinearGroup (Fin 2) F | AutomorphicForm.globalPoints (𝓞 F) F γ₀ * g ∈ W}).encard :=
            Set.encard_le_encard hsub
        _ ≤ {γ₀ : Matrix.GeneralLinearGroup (Fin 2) F | AutomorphicForm.globalPoints (𝓞 F) F γ₀ * g ∈ W}.encard :=
            Set.encard_image_le _ _
        _ = ({γ₀ : Matrix.GeneralLinearGroup (Fin 2) F |
              AutomorphicForm.globalPoints (𝓞 F) F γ₀ * g ∈ W}.ncard : ℕ∞) := (hfin.cast_ncard_eq).symm
        _ ≤ (N : ℕ∞) := by exact_mod_cast hcard
    calc ({γ' : ratGroup F | γ' • g ∈ W}.encard : ENNReal) ≤ ((N : ℕ∞) : ENNReal) := ENat.toENNReal_le.mpr hle
      _ = (N : ENNReal) := ENat.toENNReal_coe N

  have hterm : ∀ (γ : ratGroup F) (g : AdelicGL2 (𝓞 F) F),
      W.indicator f (γ • g) = {γ' : ratGroup F | γ' • g ∈ W}.indicator (fun _ => f g) γ := by
    intro γ g
    by_cases hg : γ • g ∈ W
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show γ ∈ {γ' : ratGroup F | γ' • g ∈ W} from hg), hfinv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show γ ∉ {γ' : ratGroup F | γ' • g ∈ W} from hg)]
  calc ∫⁻ g in W, f g ∂μ
      = ∫⁻ g, W.indicator f g ∂(μ.restrict (detBand F α β)) := by
        rw [lintegral_indicator hWm, Measure.restrict_restrict hWm, Set.inter_eq_left.mpr hW]
    _ = ∑' γ : ratGroup F, ∫⁻ g in S, W.indicator f (γ • g) ∂(μ.restrict (detBand F α β)) :=
        hS.lintegral_eq_tsum'' _
    _ = ∫⁻ g in S, (∑' γ : ratGroup F, W.indicator f (γ • g)) ∂(μ.restrict (detBand F α β)) := by
        rw [lintegral_tsum]
        intro γ
        exact ((hfm.indicator hWm).comp (measurable_const_smul γ)).aemeasurable
    _ ≤ ∫⁻ g in S, (N : ENNReal) * f g ∂(μ.restrict (detBand F α β)) := by
        refine lintegral_mono fun g => ?_
        simp only [hterm]
        exact hcount g
    _ = (N : ENNReal) * ∫⁻ g in S, f g ∂(μ.restrict (detBand F α β)) :=
        lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)
    _ ≤ (N : ENNReal) * ∫⁻ g in S, f g ∂μ := by
        refine mul_le_mul' le_rfl ?_
        exact lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl

section ample

open NumberField.AdelicVolume NumberField.TateGlobal

variable (F)

private def detLo (d₁ : ℝ) : ℝ := ∏ w : InfinitePlace F, d₁ ^ w.mult

private def detHi (d₂ : ℝ) : ℝ := ∏ w : InfinitePlace F, d₂ ^ w.mult

variable {F}

private theorem detLo_pos {d₁ : ℝ} (hd₁ : 0 < d₁) : 0 < detLo F d₁ :=
  Finset.prod_pos fun _ _ => pow_pos hd₁ _

private theorem ideleNorm_det_mem_Icc_of_mem_ample {c u d₁ d₂ κ : ℝ} (hd₁ : 0 < d₁) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ) :
    ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (detLo F d₁) (detHi F d₂) := by
  obtain ⟨h1, -, -, h4⟩ := mem_centreCutSiegelSet_iff.1 (centreCutSiegelSetAmple_subset c u d₁ d₂ κ hg)
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult F g h1]
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _)
      (fun w _ => pow_le_pow_left₀ hd₁.le (h4 w).1 _)
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w g).le _)
      (fun w _ => pow_le_pow_left₀ (archDetNorm_pos w g).le (h4 w).2 _)

private theorem image_mul_right_ample_subset_detBand {c u d₁ d₂ κ : ℝ} (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 F) F) :
    (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ ⊆
      detBand F (detLo F d₁ * ideleNorm F (Matrix.GeneralLinearGroup.det x))
        (detHi F d₂ * ideleNorm F (Matrix.GeneralLinearGroup.det x)) := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hlo, hhi⟩ := ideleNorm_det_mem_Icc_of_mem_ample hd₁ hg
  have hx : 0 ≤ ideleNorm F (Matrix.GeneralLinearGroup.det x) := (ideleNorm_pos _).le
  show ideleNorm F (Matrix.GeneralLinearGroup.det (g * x)) ∈ Set.Icc _ _
  rw [map_mul, ideleNorm_mul]
  exact ⟨mul_le_mul_of_nonneg_right hlo hx, mul_le_mul_of_nonneg_right hhi hx⟩

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem measurableSet_image_mul_right_ample (c u d₁ d₂ κ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    MeasurableSet ((· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  rw [Set.image_mul_right]
  exact (continuous_id.mul (continuous_const (y := x⁻¹))).measurable
    (measurableSet_centreCutSiegelSetAmple c u d₁ d₂ κ)

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem setLIntegral_ample_iUnion_lt_top
    (c' u' d₁' d₂' κ : ℝ) (hκ : 1 ≤ κ) (hc' : 0 < c') (hd₁' : 0 < d₁') (T' : Finset (AdelicGL2 (𝓞 F) F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφm : Measurable φ)
    (hφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g)
    (hdom : ∀ α β : ℝ, 0 < α → ∃ S : Set (AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain (ratGroup F) S ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (detBand F α β)) ∧
        ∫⁻ g in S, ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤) :
    ∫⁻ g in (⋃ x ∈ T', (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ),
      ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  obtain ⟨N, hN⟩ :=
    AutomorphicForm.exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
      F c' u' d₁' d₂' κ hκ hc' hd₁' T'

  have hx : ∀ x ∈ T', ∫⁻ g in (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ,
      ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    intro x hxT
    have hpos : 0 < detLo F d₁' * ideleNorm F (Matrix.GeneralLinearGroup.det x) :=
      mul_pos (detLo_pos hd₁') (ideleNorm_pos _)
    obtain ⟨S, hS, hSfin⟩ := hdom _ _ hpos
    have hsub : (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ ⊆
        ⋃ y ∈ T', (· * y) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ :=
      Set.subset_biUnion_of_mem (u := fun y => (· * y) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ) hxT
    have hNx : ∀ h : AdelicGL2 (𝓞 F) F,
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          AutomorphicForm.globalPoints (𝓞 F) F γ * h ∈ (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ}.Finite ∧
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          AutomorphicForm.globalPoints (𝓞 F) F γ * h ∈ (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ}.ncard
            ≤ N := by
      intro h
      obtain ⟨hfin, hcard⟩ := hN h
      have hss : {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          AutomorphicForm.globalPoints (𝓞 F) F γ * h ∈ (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ} ⊆
          {γ : Matrix.GeneralLinearGroup (Fin 2) F | AutomorphicForm.globalPoints (𝓞 F) F γ * h ∈
            ⋃ y ∈ T', (· * y) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ} :=
        fun γ hγ => hsub hγ
      exact ⟨hfin.subset hss, (Set.ncard_le_ncard hss hfin).trans hcard⟩
    calc ∫⁻ g in (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ,
          ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ (N : ENNReal) * ∫⁻ g in S, ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          setLIntegral_le_mul_of_forall_ncard_le _ _ _ S (measurableSet_image_mul_right_ample c' u' d₁' d₂' κ x)
            (image_mul_right_ample_subset_detBand hd₁' x) hS N hNx φ hφm hφ
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) hSfin

  rw [← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion]
  haveI : Fintype (↑T' : Set (AdelicGL2 (𝓞 F) F)) := inferInstanceAs (Fintype T')
  refine (lintegral_iUnion_le _ _).trans_lt ?_
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun x _ => hx x.1 (Finset.mem_coe.1 x.2)

end ample

section

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem memLp_two_restrict_iff_lintegral_lt_top {φ : AdelicGL2 (𝓞 F) F → ℂ} (hcont : Continuous φ)
    (S : Set (AdelicGL2 (𝓞 F) F)) :
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) ↔
      ∫⁻ g in S, ((‖φ g‖₊ : ENNReal) ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have h2 : ((2 : ENNReal)) ≠ 0 := by norm_num
  have h2' : ((2 : ENNReal)) ≠ ⊤ := by norm_num
  constructor
  · intro h
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2 h2').1 h.eLpNorm_lt_top
    simpa [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm] using this
  · intro h
    refine ⟨hcont.aestronglyMeasurable, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2 h2').2 ?_⟩
    simpa [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm] using h

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem memLp_two_ample_iUnion
    (c' u' d₁' d₂' κ : ℝ) (hκ : 1 ≤ κ) (hc' : 0 < c') (hd₁' : 0 < d₁') (T' : Finset (AdelicGL2 (𝓞 F) F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g)
    (hdom : ∀ α β : ℝ, 0 < α → ∃ S : Set (AdelicGL2 (𝓞 F) F),
      S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range S
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) ∧
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) :
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T', (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ)) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  rw [memLp_two_restrict_iff_lintegral_lt_top hcont]
  refine setLIntegral_ample_iUnion_lt_top c' u' d₁' d₂' κ hκ hc' hd₁' T' φ hcont.measurable hφ ?_
  intro α β hα
  obtain ⟨S, -, hS, hL2⟩ := hdom α β hα
  exact ⟨S, hS, (memLp_two_restrict_iff_lintegral_lt_top hcont S).1 hL2⟩

end

end WindowMultiplicity

end

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsIsotypicCuspFormAt CarrierPins productionPinsOf AdelicGL2 globalPoints IsLsXiFunction finiteAdelicGL2Subgroup lsXiMemberAt_iff IsAutomorphicFnAt HeckeEigensystem exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le ideleNorm_det_globalPoints isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc"
p2m_open "AutomorphicForm"

private theorem isAutomorphicFnAt_iff_pins (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsAutomorphicFnAt F pins ξ φ ↔ IsLsXiFunction (𝓞 F) F pins.Z ξ φ ∧ MemLp φ 2 (pins.μ.restrict pins.D) :=
  @AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ

end AutomorphicForm

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsIsotypicCuspFormAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (c' u' d₁' d₂' κ : ℝ) (hκ : 1 ≤ κ) (hc' : 0 < c') (hd₁' : 0 < d₁') (T' : Finset (AdelicGL2 (𝓞 F) F)) :
    IsIsotypicCuspFormAt F
      (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSetAmple F c' u' d₁' d₂' κ)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ := by
  obtain ⟨hsc, hcont, hlev, hhecke, hcen⟩ := hφ
  obtain ⟨⟨haut, hcusp⟩, hKf⟩ := hsc
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hLs := ((AutomorphicForm.isAutomorphicFnAt_iff_pins F _ _ φ).1 haut).1

  have hdom : ∀ α β : ℝ, 0 < α → ∃ S' : Set (AdelicGL2 (𝓞 F) F),
      S' ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∧
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range S'
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) ∧
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S') := by
    intro α β hα
    obtain ⟨S', hSs, hS⟩ :=
      AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F α β
    have h' := AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov α β hα S' hSs hS ξ φ haut
    exact ⟨S', hSs, hS, ((AutomorphicForm.isAutomorphicFnAt_iff_pins F _ _ φ).1 h').2⟩
  have hL2 := WindowMultiplicity.memLp_two_ample_iUnion c' u' d₁' d₂' κ hκ hc' hd₁' T' φ hcont
    hLs.left_invariant hdom
  exact ⟨⟨⟨(AutomorphicForm.isAutomorphicFnAt_iff_pins F _ _ φ).2 ⟨hLs, hL2⟩, hcusp⟩, hKf⟩, hcont, hlev,
    hhecke, hcen⟩

end S_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre (solution)
