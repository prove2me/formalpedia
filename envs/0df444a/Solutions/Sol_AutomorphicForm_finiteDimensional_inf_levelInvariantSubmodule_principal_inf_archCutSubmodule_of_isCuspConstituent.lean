-- Prove2me | solution 1 for AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/de182c19-c75e-5751-948f-cdd1443d12d1

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

import Theorems.Thm_AutomorphicForm_finiteDimensional_of_forall_mem_rightConv_eq_smul
import Theorems.Thm_AutomorphicForm_eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_coversModCentre_of_le_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_productionPinsOf_mono
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.SiegelVolume
p2m_open "AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent.AutomorphicForm.CuspidalConstituent"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchTypeFamily archCutSubmodule CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup isKfSmooth_iff IsSmoothCuspAutomorphicFnAt isSmoothCuspAutomorphicFnAt_zero lsXiMemberAt_iff unipotentGL2 constantTermIntegrand constantTerm rightConv finiteDimensional_of_forall_mem_rightConv_eq_smul eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre coversModCentre_of_le_of_lt_of_coversModCentre CuspidalConstituent.isCuspConstituent_productionPinsOf_mono CuspidalConstituent.exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "rightTranslate rightTranslate_apply cuspKFiniteSubmodule IsCuspSubrep IsCuspConstituent levelInvariantSubmodule isCuspConstituent_productionPinsOf_mono exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent"
namespace C8Lin
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

open FLT.SmoothVectors

variable {F : Type} [Field F] [NumberField F]

noncomputable abbrev stdPins (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

noncomputable abbrev l1Pins (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

theorem isCuspSubrep_stdPins_iff (D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (l1Pins (F := F) D).Z →* ℂˣ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    IsCuspSubrep F (stdPins D) ξ W ↔ IsCuspSubrep F (l1Pins D) ξ W :=
  ⟨fun h => ⟨h.le, h.rightTranslate_fin_mem, h.rightTranslate_arch_mem, h.rightConv_mem⟩,
    fun h => ⟨h.le, h.rightTranslate_fin_mem, h.rightTranslate_arch_mem, h.rightConv_mem⟩⟩

theorem isCuspConstituent_stdPins_iff (D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (l1Pins (F := F) D).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    IsCuspConstituent F (stdPins D) ξ V ↔ IsCuspConstituent F (l1Pins D) ξ V := by
  unfold IsCuspConstituent
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isCuspSubrep_stdPins_iff D ξ V).mp h1, h2, fun W hW hle => h3 W ((isCuspSubrep_stdPins_iff D ξ W).mpr hW) hle⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isCuspSubrep_stdPins_iff D ξ V).mpr h1, h2, fun W hW hle => h3 W ((isCuspSubrep_stdPins_iff D ξ W).mp hW) hle⟩

theorem continuous_unipotentGL2_mul (g : AdelicGL2 (𝓞 F) F) :
    Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q * g := by
  have hu : Continuous fun q : AdeleRing (𝓞 F) F => unipotentGL2 (R := AdeleRing (𝓞 F) F) q := by
    refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_id
      · exact continuous_const
      · exact continuous_const
    · fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_id.neg
      · exact continuous_const
      · exact continuous_const
  exact hu.mul continuous_const

theorem integrable_cond_adelicBox {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    (letI := adeleBorel (𝓞 F) F
     Integrable (fun q => φ (unipotentGL2 (R := AdeleRing (𝓞 F) F) q * g))
       (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hc : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 (R := AdeleRing (𝓞 F) F) q * g) :=
    hφ.comp (continuous_unipotentGL2_mul g)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hint : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 (R := AdeleRing (𝓞 F) F) q * g))
      (adelicBox F) (adelicAddHaar (𝓞 F) F) :=
    (hc.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hint.integrable.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

theorem isSmoothCuspAutomorphicFnAt_add {D : Set (AdelicGL2 (𝓞 F) F)} {ξ : (stdPins D).Z →* ℂˣ}
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ φ) (hφc : Continuous φ)
    (hψ : IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ ψ) (hψc : Continuous ψ) :
    IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ (φ + ψ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨hA, hcusp⟩, hsm⟩ := hφ
  obtain ⟨⟨hA', hcusp'⟩, hsm'⟩ := hψ
  have h1 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D φ).mp hA
  have h2 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D ψ).mp hA'
  refine ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D (φ + ψ)).mpr
    ⟨⟨fun γ g => ?_, fun z g => ?_⟩, h1.2.add h2.2⟩, fun g => ?_⟩, ?_⟩
  · simp only [Pi.add_apply, h1.1.left_invariant, h2.1.left_invariant]
  · simp only [Pi.add_apply, h1.1.central_transform, h2.1.central_transform, mul_add]
  ·
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
    have e : constantTerm (stdPins D).ν unipotentGL2 (φ + ψ) g =
        constantTerm (stdPins D).ν unipotentGL2 φ g + constantTerm (stdPins D).ν unipotentGL2 ψ g := by
      simp only [constantTerm, constantTermIntegrand, Pi.add_apply]
      exact integral_add (integrable_cond_adelicBox hφc g) (integrable_cond_adelicBox hψc g)
    rw [e, hcusp g, hcusp' g, add_zero]
  · exact hsm.add hsm'

theorem isSmoothCuspAutomorphicFnAt_smul {D : Set (AdelicGL2 (𝓞 F) F)} {ξ : (stdPins D).Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ φ) (a : ℂ) :
    IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ (a • φ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨hA, hcusp⟩, hsm⟩ := hφ
  have h1 := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D φ).mp hA
  refine ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D (a • φ)).mpr
    ⟨⟨fun γ g => ?_, fun z g => ?_⟩, h1.2.const_smul a⟩, fun g => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, h1.1.left_invariant]
  · simp only [Pi.smul_apply, smul_eq_mul, h1.1.central_transform]; ring
  · letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
    have e : constantTerm (stdPins D).ν unipotentGL2 (a • φ) g = a * constantTerm (stdPins D).ν unipotentGL2 φ g := by
      simp only [constantTerm, constantTermIntegrand, Pi.smul_apply, smul_eq_mul]
      exact integral_const_mul a _
    rw [e, hcusp g, mul_zero]
  ·
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hsm ⊢
    refine Subgroup.isOpen_mono (fun k hk => ?_) hsm
    rw [MulAction.mem_stabilizer_iff] at hk ⊢
    refine RightTranslationFn.ext fun y => ?_
    have := congrArg (fun f => RightTranslationFn.toFun f y) hk
    simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at this ⊢
    simp only [Pi.smul_apply, this]

theorem isSmoothCuspAutomorphicFnAt_and_continuous_of_mem_cuspKFiniteSubmodule {D : Set (AdelicGL2 (𝓞 F) F)}
    {ξ : (stdPins D).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F (stdPins D) ξ) :
    IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ φ ∧ Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ φ ∧ Continuous φ)
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    have e : rightTranslate F 1 φ = φ := funext fun x => by rw [rightTranslate_apply, mul_one]
    rw [e] at h1
    exact ⟨h1, hcont⟩
  · exact ⟨isSmoothCuspAutomorphicFnAt_zero F _ ξ, continuous_const⟩
  · intro φ ψ _ _ hφ hψ
    exact ⟨isSmoothCuspAutomorphicFnAt_add hφ.1 hφ.2 hψ.1 hψ.2, hφ.2.add hψ.2⟩
  · intro a φ _ hφ
    exact ⟨isSmoothCuspAutomorphicFnAt_smul hφ.1 a, hφ.2.const_smul a⟩

end AutomorphicForm.CuspidalConstituent.C8Lin

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchTypeFamily archCutSubmodule CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup isKfSmooth_iff IsSmoothCuspAutomorphicFnAt isSmoothCuspAutomorphicFnAt_zero lsXiMemberAt_iff unipotentGL2 constantTermIntegrand constantTerm rightConv finiteDimensional_of_forall_mem_rightConv_eq_smul eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre coversModCentre_of_le_of_lt_of_coversModCentre CuspidalConstituent.isCuspConstituent_productionPinsOf_mono CuspidalConstituent.exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "rightTranslate rightTranslate_apply cuspKFiniteSubmodule IsCuspSubrep IsCuspConstituent levelInvariantSubmodule isCuspConstituent_productionPinsOf_mono exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent"
namespace C8W4
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

open AutomorphicForm.CuspidalConstituent.C8Lin NumberField.AdelicVolume

theorem isSmoothCuspAutomorphicFnAt_mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D)
    {ξ : (stdPins D).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (stdPins D) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (stdPins D') ξ φ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨⟨hA, hcusp⟩, hsm⟩ := h
  have hA' := (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D φ).mp hA
  exact ⟨⟨(lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) (stdPins D).Z ξ D' φ).mpr
    ⟨hA'.1, hA'.2.mono_measure (Measure.restrict_mono hD le_rfl)⟩, hcusp⟩, hsm⟩

theorem cuspKFiniteSubmodule_antitone {D D' : Set (AdelicGL2 (𝓞 F) F)} (hD : D' ⊆ D) (ξ : (stdPins D).Z →* ℂˣ) :
    cuspKFiniteSubmodule F (stdPins D) ξ ≤ cuspKFiniteSubmodule F (stdPins D') ξ := by
  refine Submodule.span_mono ?_
  rintro φ ⟨hsat, hcont, tys, htys⟩
  exact ⟨fun g => isSmoothCuspAutomorphicFnAt_mono hD (hsat g), hcont, tys, htys⟩

theorem centreCutSiegelSet_mono_left {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') :
    centreCutSiegelSet F c u d₁' d₂ ⊆ centreCutSiegelSet F c u d₁ d₂ := fun g hg => by
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  exact ⟨hg.1, hg.2.1, hg.2.2.1, fun w => Set.Icc_subset_Icc hle le_rfl (hg.2.2.2 w)⟩

theorem window_mono_left {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') (T : Finset (AdelicGL2 (𝓞 F) F)) :
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
  Set.iUnion₂_mono fun _ _ => Set.image_mono (centreCutSiegelSet_mono_left hle)

theorem pos_of_coversModCentre {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) : 0 < d₂ := by
  obtain ⟨γ, z, hmem⟩ := hcov 1
  obtain ⟨x, -, h, hh, -⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact (archDetNorm_pos w h).trans_le ((mem_centreCutSiegelSet_iff.mp hh).2.2.2 w).2

theorem finiteDimensional_cut_of_pos
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (stdPins (F := F) (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (stdPins (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) ξ V) :
    FiniteDimensional ℂ ↥(V ⊓ levelInvariantSubmodule F (stdPins (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) N
        ⊓ archCutSubmodule F tys) := by
  classical
  by_cases hX : V ⊓ levelInvariantSubmodule F (stdPins (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) N
      ⊓ archCutSubmodule F tys = ⊥
  · rw [hX]; infer_instance
  obtain ⟨f, hf, n, lam, hlam, E, hE, hle⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
      F c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV hX
  haveI : ∀ i, FiniteDimensional ℂ ↥(E i) := fun i =>
    AutomorphicForm.finiteDimensional_of_forall_mem_rightConv_eq_smul F c u d₁ d₂ T hc hd₁ hd hcov ξ f hf
      (lam i) (hlam i) (E i) fun φ hφ =>
      ⟨(isSmoothCuspAutomorphicFnAt_and_continuous_of_mem_cuspKFiniteSubmodule (hE i φ hφ).1).1,
        (isSmoothCuspAutomorphicFnAt_and_continuous_of_mem_cuspKFiniteSubmodule (hE i φ hφ).1).2, (hE i φ hφ).2⟩
  haveI : FiniteDimensional ℂ ↥(⨆ i, E i) := Submodule.finiteDimensional_iSup _
  exact Submodule.finiteDimensional_of_le hle

end AutomorphicForm.CuspidalConstituent.C8W4

open AutomorphicForm.CuspidalConstituent.C8Lin AutomorphicForm.CuspidalConstituent.C8W4 in

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V) :
    FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) N ⊓ archCutSubmodule F tys) := by

  rcases le_or_gt c 0 with hc | hc
  · exfalso
    refine hV.2.1 (le_bot_iff.mp (hV.1.le.trans (Submodule.span_le.mpr ?_)))
    rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    have e : rightTranslate F 1 φ = φ := funext fun x => by rw [rightTranslate_apply, mul_one]
    rw [e] at h1
    exact AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre
      F c u d₁ d₂ T hc hd hcov ξ φ h1.1.1 hcont

  have hd₂ : 0 < d₂ := pos_of_coversModCentre hcov
  set d₁' : ℝ := max d₁ (d₂ / 2) with hd₁'
  have hle : d₁ ≤ d₁' := le_max_left _ _
  have hlt : d₁' < d₂ := max_lt hd (by linarith)
  have hpos : 0 < d₁' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hcov' := AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre F c u d₁ d₂ d₁' T hle hlt hcov
  have hV' : IsCuspConstituent F (stdPins (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)) ξ V :=
    (isCuspConstituent_stdPins_iff _ ξ V).mpr
      (AutomorphicForm.CuspidalConstituent.isCuspConstituent_productionPinsOf_mono F
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂)
        (window_mono_left hle T) (adelicBox F) ξ V ((isCuspConstituent_stdPins_iff _ ξ V).mp hV))

  exact finiteDimensional_cut_of_pos c u d₁' d₂ T hc hpos hlt hcov' ξ N hN tys V hV'

end S_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_of_isCuspConstituent (solution)
