-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/85424831-61f0-5ab6-9038-09a835452f7d

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat
import Theorems.Thm_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2
open NumberField.AdelicHaar
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace Ws47
namespace C8

section Transport

variable {F : Type} [Field F] [NumberField F]

theorem regular_adelicGLHaar :
    (adelicGLHaar (Fin 2) (𝓞 F) F).Regular := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  unfold adelicGLHaar
  infer_instance

theorem memLp_comp_mul_right_restrict (φ : AdelicGL2 (𝓞 F) F → ℂ) (D : Set (AdelicGL2 (𝓞 F) F))
    (r : AdelicGL2 (𝓞 F) F)
    (h : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict ((fun y => y * r) '' D))) :
    MemLp (fun y => φ (y * r)) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).Regular := regular_adelicGLHaar
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  let e : AdelicGL2 (𝓞 F) F ≃ᵐ AdelicGL2 (𝓞 F) F := (Homeomorph.mulRight r).toMeasurableEquiv
  have he : (e : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) = fun y => y * r := rfl

  haveI : (Measure.map (fun y => y * r) μ).Regular := Measure.Regular.map (Homeomorph.mulRight r)
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, Measure.map (fun y => y * r) μ = c • μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul_of_regular (Measure.map (fun y => y * r) μ) μ⟩
  have hc' : Measure.map e μ = (c : ℝ≥0∞) • μ := by
    rw [he, hc]; ext s hs
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

  have hpre : (e : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F) ⁻¹' ((fun y => y * r) '' D) = D := by
    rw [he]; exact Set.preimage_image_eq D (mul_left_injective r)
  have hmapres : Measure.map e (μ.restrict D) = ((c : ℝ≥0∞) • μ).restrict ((fun y => y * r) '' D) := by
    rw [← hc', MeasurableEquiv.restrict_map e μ, hpre]
  have h1 : MemLp φ 2 (Measure.map e (μ.restrict D)) := by
    rw [hmapres, Measure.restrict_smul]
    exact h.smul_measure ENNReal.coe_ne_top
  have h2 := (MeasurableEquiv.memLp_map_measure_iff e).mp h1
  rw [he] at h2
  exact h2

end Transport

section SmoothCuspSpan

open FLT.SmoothVectors HeckeIntegralSeam

variable {F : Type} [Field F] [NumberField F]

theorem integrable_slice_cond {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (x : AdelicGL2 (𝓞 F) F) :
    @Integrable _ _ _ _ (adeleBorel (𝓞 F) F) (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hcont : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> fun_prop
    · have hinv : ∀ q : AdeleRing (𝓞 F) F, ((unipotentGL2 q)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F))
          = unipotentGL2 (-q) := fun q =>
        inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
      simp_rw [hinv]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [unipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
        fun_prop
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hIC : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) C
      (adelicAddHaar (𝓞 F) F) := hcont.continuousOn.integrableOn_compact hC
  have hIB : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := hIC.mono_set hsub
  unfold ProbabilityTheory.cond
  refine Integrable.smul_measure hIB ?_
  exact ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne'

theorem isCuspidalFn_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ)
    (hψ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 ψ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (φ + ψ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  intro g
  have h1 := hφ g
  have h2 := hψ g
  unfold constantTerm constantTermIntegrand at h1 h2 ⊢
  simp only [Pi.add_apply]
  rw [integral_add (integrable_slice_cond hφc g) (integrable_slice_cond hψc g), h1, h2, add_zero]

theorem isCuspidalFn_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (a • φ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  intro g
  have h1 := hφ g
  unfold constantTerm constantTermIntegrand at h1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h1, mul_zero]

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ hψ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  obtain ⟨V₂, hV₂o, hV₂⟩ := hψ
  refine ⟨V₁ ⊓ V₂, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hV₁o.inter hV₂o
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu1)
    have h2 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₂ u hu2)
    refine RightTranslationFn.ext fun y => ?_
    simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
      Pi.add_apply] at h1 h2 ⊢
    rw [h1 y, h2 y]

theorem isKfSmooth_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ) (hφ : IsKfSmooth F φ) :
    IsKfSmooth F (a • φ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  refine ⟨V₁, hV₁o, fun u hu => ?_⟩
  have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu)
  refine RightTranslationFn.ext fun y => ?_
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
    Pi.smul_apply] at h1 ⊢
  rw [h1 y]

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

abbrev pp : CarrierPins F := productionPinsOf F D U gen (adelicBox F)

theorem isSmoothCuspAutomorphicFnAt_add (ξ : (pp D U gen).Z →* ℂˣ)
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ)
    (hψ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (φ + ψ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hψm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ ψ).mp hψ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (φ + ψ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.add_apply, hφm.1.left_invariant γ g, hψm.1.left_invariant γ g]
    · simp only [Pi.add_apply, hφm.1.central_transform z g, hψm.1.central_transform z g, mul_add]
  have hL2 : MemLp (φ + ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := hφm.2.add hψm.2
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (φ + ψ)).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_add hφc hψc hφ.1.2 hψ.1.2
  · exact isKfSmooth_add hφ.2 hψ.2

theorem isSmoothCuspAutomorphicFnAt_smul (ξ : (pp D U gen).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (a • φ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (a • φ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.smul_apply, hφm.1.left_invariant γ g]
    · simp only [Pi.smul_apply, smul_eq_mul, hφm.1.central_transform z g]
      ring
  have hL2 : MemLp (a • φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
    have := hφm.2.const_mul a
    exact this
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (a • φ)).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_smul a hφ.1.2
  · exact isKfSmooth_smul a hφ.2

end SmoothCuspSpan

section Rat

open AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel FLT.SmoothVectors
open scoped Classical

theorem coversModCentre_classRepSiegelSet_rat :
    CoversModCentre ℚ (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) := by
  have hfin : FiniteIntegralCovering ℚ := fun g =>
    NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat g
  have h3 : (1 / 2 : ℝ) ≤ Real.sqrt 3 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have h := coversModCentre_centreCutSiegelSet_rat hfin (c := (1/2 : ℝ)) (u := (1 : ℝ)) (d₁ := (1/2 : ℝ))
    (d₂ := (2 : ℝ)) h3 (by norm_num) (by norm_num) (by norm_num)
  exact h.mono (centreCutSiegelSet_subset_classRepSiegelSet ℚ _ _ _ _)

theorem image_mul_right_classRepSiegelSet (r : AdelicGL2 (𝓞 ℚ) ℚ) (c u d₁ d₂ : ℝ) :
    (fun y => y * r) '' classRepSiegelSet ℚ c u d₁ d₂ =
      ⋃ x ∈ (classRepTranslates ℚ).image (· * r), (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂ := by
  classical
  rw [Finset.set_biUnion_finset_image]
  unfold classRepSiegelSet
  rw [Set.image_iUnion₂]
  refine Set.iUnion₂_congr fun x _ => ?_
  rw [Set.image_image]
  congr 1
  funext y
  simp only [mul_assoc]

theorem smoothCusp_translate
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (r : AdelicGL2 (𝓞 ℚ) ℚ) (hr : r ∈ finiteAdelicGL2Subgroup ℚ) :
    IsSmoothCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun y => φ (y * r)) ∧
      Continuous (fun y => φ (y * r)) := by
  have hsc := hiso.smoothCusp
  have hm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ ξ _ φ).mp hsc.1.1

  have hiso' := AutomorphicForm.isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
    ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) coversModCentre_classRepSiegelSet_rat ξ N S Φ φ hiso
    (1/2 : ℝ) 1 (1/2) 2 1 le_rfl (by norm_num) (by norm_num) ((classRepTranslates ℚ).image (· * r))
  have hm' := (AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ ξ _ φ).mp hiso'.smoothCusp.1.1
  have hset : (⋃ x ∈ (classRepTranslates ℚ).image (· * r),
      (· * x) '' centreCutSiegelSetAmple ℚ (1/2 : ℝ) 1 (1/2) 2 1) =
      (fun y => y * r) '' classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2 := by
    rw [centreCutSiegelSetAmple_eq_of_subsingleton le_rfl, image_mul_right_classRepSiegelSet]
  have hL2 : MemLp (fun y => φ (y * r)) 2
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)) :=
    memLp_comp_mul_right_restrict φ _ r (by rw [← hset]; exact hm'.2)
  have hLs : IsLsXiFunction (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).Z ξ (fun y => φ (y * r)) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 ℚ) ℚ γ * g * r) = φ (g * r)
      rw [mul_assoc]; exact hm.1.left_invariant γ (g * r)
    · show φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g * r) = _ * φ (g * r)
      rw [mul_assoc]; exact hm.1.central_transform z (g * r)
  refine ⟨⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ ξ _ _).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    intro g
    have h0 := hsc.1.2 (g * r)
    unfold constantTerm constantTermIntegrand at h0 ⊢
    simpa only [mul_assoc] using h0
  ·
    exact hsc.2.smul (⟨r, hr⟩ : finiteAdelicGL2Subgroup ℚ)
  · exact hiso.continuous.comp (continuous_id.mul continuous_const)

theorem smoothCusp_sum_translate
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    {m : ℕ} (r : Fin m → AdelicGL2 (𝓞 ℚ) ℚ) (hr : ∀ i, r i ∈ finiteAdelicGL2Subgroup ℚ) :
    IsSmoothCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun y => ∑ i, φ (y * r i)) ∧
      Continuous (fun y => ∑ i, φ (y * r i)) := by
  classical
  have key : ∀ s : Finset (Fin m),
      IsSmoothCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun y => ∑ i ∈ s, φ (y * r i)) ∧
        Continuous (fun y => ∑ i ∈ s, φ (y * r i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨isSmoothCuspAutomorphicFnAt_zero ℚ _ ξ, continuous_const⟩
    | insert a s ha ih =>
      have hta := smoothCusp_translate ξ N S Φ φ hiso (r a) (hr a)
      have hfun : (fun y => ∑ i ∈ insert a s, φ (y * r i)) =
          (fun y => φ (y * r a)) + fun y => ∑ i ∈ s, φ (y * r i) := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact ⟨isSmoothCuspAutomorphicFnAt_add (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) ξ
          hta.2 ih.2 hta.1 ih.1, hta.2.add ih.2⟩
  exact key Finset.univ

end Rat

section Coset

open HeckeIntegralSeam

variable {G : Type*} [Group G] {U : Subgroup G}

theorem isHeckeCosetSystem_mul_right {g : G} {ι : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps)
    (k : ι → G) (hk : ∀ i, k i ∈ U) : IsHeckeCosetSystem U g (fun i => reps i * k i) where
  mem_doubleCoset i := HeckePair.doubleCoset_mul_mem (h.mem_doubleCoset i) (hk i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    refine ⟨i, hi.trans ?_⟩
    exact QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hk i)
  mk_injective i j hij := by
    apply h.mk_injective
    have hi : (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps i * k i) :=
      QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hk i)
    have hj : (QuotientGroup.mk (reps j) : G ⧸ U) = QuotientGroup.mk (reps j * k j) :=
      QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hk j)
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [hi, hj]
    exact hij

theorem sum_apply_mul_mul_eq_of_mem {ι : Type*} [Fintype ι] {reps : ι → G} {g₀ : G}
    (hsys : IsHeckeCosetSystem U g₀ reps) {φ : G → ℂ} (hinv : ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g)
    (g u : G) (hu : u ∈ U) :
    ∑ i, φ (g * u * reps i) = ∑ i, φ (g * reps i) := by
  obtain ⟨π, hπ, hk⟩ := hsys.exists_bijective_forall_exists_mul_eq_mul_of_mem u hu
  have h1 : ∀ i, φ (g * u * reps i) = φ (g * reps (π i)) := fun i => by
    obtain ⟨u', hu', he⟩ := hk i
    rw [mul_assoc, he, ← mul_assoc, hinv _ _ hu']
  simp only [h1]
  exact (Equiv.ofBijective π hπ).sum_comp (fun j => φ (g * reps j))

end Coset

section Components

variable (F : Type) [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem eq_of_glArch_eq_of_glFin_eq' {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem coe_finComponent (w : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ((finComponent (𝓞 F) F w x : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))
      = (finAdeleEval (𝓞 F) F w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

theorem eq_of_forall_finComponent_eq {x y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w x = finComponent (𝓞 F) F w y) : x = y := by
  apply Units.ext
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
  rw [← coe_finComponent, ← coe_finComponent, h w]

theorem mul_finEmbed_localEmbed_comm (g : AdelicGL2 (𝓞 F) F)
    (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) (m : GL (Fin 2) (v.adicCompletion F)) :
    g * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) * g := by
  refine eq_of_glArch_eq_of_glFin_eq' F ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_finEmbed]
    refine eq_of_forall_finComponent_eq F fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hg, one_mul, mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F v m hw, one_mul, mul_one]

theorem mem_generalU_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ (productionPinsGeneral F).U N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      exact (mem_localLevelOne_iff (𝓞 F) F w (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
        (hfin w)
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · show _ ∈ finiteAdelicGL2Subgroup F
    rw [finiteAdelicGL2Subgroup, MonoidHom.mem_ker]
    exact harch

theorem components_of_mem_generalU {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ (productionPinsGeneral F).U N) :
    glArch (𝓞 F) F h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

theorem finEmbed_localEmbed_mem_generalU_of_mem_localLevelOne {N : Ideal (𝓞 F)}
    {k : GL (Fin 2) (v.adicCompletion F)} (hk : k ∈ localLevelOne (𝓞 F) F v N) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k) ∈ (productionPinsGeneral F).U N := by
  refine mem_generalU_of_components F (glArch_finEmbed (𝓞 F) F _) fun w => ?_
  rw [glFin_finEmbed]
  by_cases hw : w = v
  · subst hw
    rw [finComponent_localEmbed_self]
    exact hk
  · rw [finComponent_localEmbed_of_ne _ _ _ _ hw]
    exact one_mem _

theorem finComponent_glFin_heckeGen_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (heckeGen (𝓞 F) F v)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, glFin_apply, Units.val_one]
  exact heckeGenAt_snd_apply_of_ne _ hw i j

theorem finComponent_mem_localLevelOne_of_mem_doubleCoset {N : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ HeckePair.doubleCoset ((productionPinsGeneral F).U N) (heckeGen (𝓞 F) F v)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F x) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, map_mul, map_mul, finComponent_glFin_heckeGen_of_ne F hw, mul_one]
  exact mul_mem ((components_of_mem_generalU F hu).2 w) ((components_of_mem_generalU F hu').2 w)

end Components

section HeckeTransfer

open AutomorphicForm.SmoothCusp HeckeIntegralSeam

theorem isHeckeCosetEigenfunctionAt_sum_translate (N : Ideal (𝓞 ℚ)) (v v' : HeightOneSpectrum (𝓞 ℚ))
    (hvv' : v' ≠ v) {m : ℕ} (loc : Fin m → GL (Fin 2) (v.adicCompletion ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hinv : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ (productionPinsGeneral ℚ).U N, φ (g * u) = φ g)
    (a : ℂ)
    (h : IsHeckeCosetEigenfunctionAt ℚ ((productionPinsGeneral ℚ).U N) ((productionPinsGeneral ℚ).gen v') v' φ a) :
    IsHeckeCosetEigenfunctionAt ℚ ((productionPinsGeneral ℚ).U N) ((productionPinsGeneral ℚ).gen v') v'
      (fun x => ∑ i, φ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)))) a := by
  obtain ⟨ρ, hρ, heig⟩ := h

  let c : Fin (Ideal.absNorm v'.asIdeal + 1) → GL (Fin 2) (v.adicCompletion ℚ) :=
    fun j => finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (ρ j))
  let k : Fin (Ideal.absNorm v'.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ :=
    fun j => finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (c j)⁻¹)
  have hc : ∀ j, c j ∈ localLevelOne (𝓞 ℚ) ℚ v N := fun j =>
    finComponent_mem_localLevelOne_of_mem_doubleCoset ℚ hvv'.symm (hρ.mem_doubleCoset j)
  have hk : ∀ j, k j ∈ (productionPinsGeneral ℚ).U N := fun j =>
    finEmbed_localEmbed_mem_generalU_of_mem_localLevelOne ℚ (inv_mem (hc j))
  have hρ' := isHeckeCosetSystem_mul_right hρ k hk
  have htriv : ∀ j, finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (ρ j * k j)) = 1 := fun j => by
    rw [map_mul, map_mul]
    show c j * finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (c j)⁻¹))) = 1
    rw [glFin_finEmbed, finComponent_localEmbed_self, mul_inv_cancel]
  have hcomm : ∀ i j, (ρ j * k j) * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i))
      = finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)) * (ρ j * k j) := fun i j =>
    mul_finEmbed_localEmbed_comm ℚ (ρ j * k j) (htriv j) (loc i)
  refine ⟨fun j => ρ j * k j, hρ', fun g => ?_⟩
  unfold heckeCosetSum
  calc ∑ j, ∑ i, φ (g * (ρ j * k j) * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)))
      = ∑ j, ∑ i, φ (g * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)) * ρ j) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hcomm i j, ← mul_assoc, ← mul_assoc, hinv _ _ (hk j)]
    _ = ∑ i, ∑ j, φ (g * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)) * ρ j) := Finset.sum_comm
    _ = ∑ i, a * φ (g * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i))) :=
        Finset.sum_congr rfl fun i _ => heig _
    _ = a * ∑ i, φ (g * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i))) := by rw [Finset.mul_sum]

end HeckeTransfer

end Ws47.C8

end

open Ws47.C8 in
open scoped Classical in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) (loc : Fin m → GL (Fin 2) (v.adicCompletion ℚ))
    (h : AdelicGL2 (𝓞 ℚ) ℚ)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem ((productionPinsGeneral ℚ).U N) h
      (fun i => finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)))) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N
      (S ∪ {v} ∪ (N.finite_factors hN).toFinset) Φ
      (fun x => ∑ i, φ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)))) := by
  classical
  have hrfin : ∀ i : Fin m, finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i)) ∈ finiteAdelicGL2Subgroup ℚ :=
    fun i => (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_finEmbed (𝓞 ℚ) ℚ _)
  have hsc := smoothCusp_sum_translate ξ N S Φ φ hiso
    (fun i => finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (loc i))) hrfin
  have hS : ∀ v' : HeightOneSpectrum (𝓞 ℚ), v' ∉ S ∪ {v} ∪ (N.finite_factors hN).toFinset → v' ∉ S ∧ v' ≠ v := by
    intro v' hv'
    refine ⟨fun h' => hv' (Finset.mem_union_left _ (Finset.mem_union_left _ h')), fun h' => hv' ?_⟩
    subst h'
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  refine ⟨hsc.1, hsc.2, ?_, ?_, ?_⟩
  · intro g u hu
    exact sum_apply_mul_mul_eq_of_mem hsys hiso.level_invariant g u hu
  · intro v' hv'
    exact isHeckeCosetEigenfunctionAt_sum_translate N v v' (hS v' hv').2 loc φ hiso.level_invariant (Φ.a v')
      (hiso.hecke_eigen v' (hS v' hv').1)
  · intro v' hv' g
    show ∑ i, φ (_ * g * _) = _ * ∑ i, φ (g * _)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]; exact hiso.central_eigen v' (hS v' hv').1 _

end S_AutomorphicForm_isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem (solution)
