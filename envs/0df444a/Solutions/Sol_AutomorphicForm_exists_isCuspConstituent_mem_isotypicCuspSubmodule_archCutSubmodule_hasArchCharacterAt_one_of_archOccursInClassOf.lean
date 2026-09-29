-- Prove2me | solution 1 for AutomorphicForm.exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5b1f3f7b-c34e-55e9-94fd-9a2f1647624a

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf SmoothCuspRealizationAt finiteAdelicGL2Subgroup productionPinsOf AdelicGL2 HeckeEigensystem rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal rowIsometrySubgroup₀ archWeightCharℝ HasArchCharacterAt₀ IsGenuineCuspRealizationAt IsArchSmoothAt ArchDir archDerivAt isotypicCuspSubmodule ArchRepAt ArchRepAt.ofChar ArchTypeFamily archCutSubmodule archCutSubmodule_mono rightConv SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre"
namespace RJClose
namespace K0
p2m_open "AutomorphicForm"

variable {F : Type} [Field F]

noncomputable def extendFamily (tys : ArchTypeFamily F)
    (chiP chiM : ∀ v : InfinitePlace F, rowIsometrySubgroup₀ v.Completion →* ℂˣ) : ArchTypeFamily F where
  card := fun v => tys.card v + 2
  rep := fun v i =>
    if h : (i : ℕ) < tys.card v then tys.rep v ⟨i, h⟩
    else if (i : ℕ) = tys.card v then ArchRepAt.ofChar F (chiP v) else ArchRepAt.ofChar F (chiM v)

theorem isContainedIn_extendFamily (tys : ArchTypeFamily F)
    (chiP chiM : ∀ v : InfinitePlace F, rowIsometrySubgroup₀ v.Completion →* ℂˣ) :
    tys.IsContainedIn F (extendFamily tys chiP chiM) := fun v i =>
  ⟨⟨i, by show (i : ℕ) < tys.card v + 2; omega⟩, by
    show (if h : ((⟨i, _⟩ : Fin (tys.card v + 2)) : ℕ) < tys.card v then tys.rep v ⟨_, h⟩ else _) = tys.rep v i
    rw [dif_pos i.2]⟩

theorem extendFamily_rep_plus (tys : ArchTypeFamily F)
    (chiP chiM : ∀ v : InfinitePlace F, rowIsometrySubgroup₀ v.Completion →* ℂˣ) (v : InfinitePlace F) :
    (extendFamily tys chiP chiM).rep v ⟨tys.card v, by show tys.card v < tys.card v + 2; omega⟩
      = ArchRepAt.ofChar F (chiP v) := by
  show (if h : ((⟨tys.card v, _⟩ : Fin (tys.card v + 2)) : ℕ) < tys.card v then tys.rep v ⟨_, h⟩ else _) = _
  rw [dif_neg (lt_irrefl _), if_pos rfl]

theorem extendFamily_rep_minus (tys : ArchTypeFamily F)
    (chiP chiM : ∀ v : InfinitePlace F, rowIsometrySubgroup₀ v.Completion →* ℂˣ) (v : InfinitePlace F) :
    (extendFamily tys chiP chiM).rep v ⟨tys.card v + 1, by show tys.card v + 1 < tys.card v + 2; omega⟩
      = ArchRepAt.ofChar F (chiM v) := by
  show (if h : ((⟨tys.card v + 1, _⟩ : Fin (tys.card v + 2)) : ℕ) < tys.card v then tys.rep v ⟨_, h⟩ else _) = _
  rw [dif_neg (by show ¬ (tys.card v + 1 < tys.card v); omega), if_neg (by show ¬ (tys.card v + 1 = tys.card v); omega)]

open scoped Classical in

noncomputable def charAt (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    ∀ v : InfinitePlace F, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
  fun v => if h : v = w then h ▸ χ else 1

theorem charAt_self (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) : charAt w χ w = χ := by
  classical
  simp [charAt]

end AutomorphicForm.RJClose.K0

open AutomorphicForm.RJClose.K0 in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop)
    (hocc : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ P φ)) :
    ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
    ∃ R' : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ'.toRawCentral,
      IsGenuineCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Θ'.toRawCentral R' ∧ P R'.toFun ∧
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F)
      (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (x₀ : AdelicGL2 (𝓞 F) F → ℂ),
      R'.exceptionalSet ⊆ S ∧
      IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar V ∧
      x₀ ≠ 0 ∧ x₀ ∈ V ∧
      x₀ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar Θ'.level S Θ' ∧
      x₀ ∈ archCutSubmodule F tys ∧
      (∃ i, tys.rep w i = ArchRepAt.ofChar F ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))) ∧
      (∃ i, tys.rep w i = ArchRepAt.ofChar F ((archWeightCharℝ (-1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))) ∧
      HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) x₀ ∧
      IsArchSmoothAt hw x₀ ∧
      (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) x₀) ∧
        ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
            ‖l.foldr (archDerivAt hw) x₀ g‖ ≤ B) := by
  obtain ⟨Θ', hΘ', R', hR', h1, hP⟩ := hocc
  obtain ⟨S, tys₀, f, hS, -, -, hne, hiso, hcut, hchar, hsm, hreg⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
      F c u d₁ d₂ T hc hd₁ hd hcov Θ' R' hR' w hw 1 h1

  let tys : ArchTypeFamily F := extendFamily tys₀
    (charAt w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))))
    (charAt w ((archWeightCharℝ (-1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))))
  have hcut' : rightConv F R'.toFun f ∈ archCutSubmodule F tys :=
    archCutSubmodule_mono F (isContainedIn_extendFamily tys₀ _ _) hcut

  have hmem := AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent F c u d₁ d₂ T
    hd hcov R'.centralChar Θ'.level S tys Θ' (Submodule.mem_inf.mpr ⟨hiso, hcut'⟩)
  by_cases hex : ∃ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar V ∧
      CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar Θ'.level S Θ' V ∧
      V ⊓ archCutSubmodule F tys ≠ ⊥
  · obtain ⟨V₀, hV₀⟩ := hex
    have hxV₀ : rightConv F R'.toFun f ∈ V₀ := by
      refine (iSup₂_le (f := fun (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar V ∧
          CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar Θ'.level S Θ' V ∧
          V ⊓ archCutSubmodule F tys ≠ ⊥) => V) fun V hV => ?_) hmem
      exact (AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre F c u d₁ d₂ T hd hcov
        R'.centralChar Θ'.level S Θ' V V₀ hV.1 hV₀.1 hV.2.1 hV₀.2.1).le
    refine ⟨Θ', hΘ', R', hR', hP, S, tys, V₀, rightConv F R'.toFun f, hS, hV₀.1, hne, hxV₀, hiso, hcut', ?_, ?_,
      hchar, hsm, hreg⟩
    · refine ⟨⟨tys₀.card w, by show tys₀.card w < tys₀.card w + 2; omega⟩, ?_⟩
      show (extendFamily tys₀ _ _).rep w _ = _
      rw [extendFamily_rep_plus, charAt_self]
    · refine ⟨⟨tys₀.card w + 1, by show tys₀.card w + 1 < tys₀.card w + 2; omega⟩, ?_⟩
      show (extendFamily tys₀ _ _).rep w _ = _
      rw [extendFamily_rep_minus, charAt_self]
  · exfalso
    have hbot : (⨆ (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar V ∧
          CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) R'.centralChar Θ'.level S Θ' V ∧
          V ⊓ archCutSubmodule F tys ≠ ⊥), V) = ⊥ :=
      iSup_eq_bot.mpr fun V => iSup_eq_bot.mpr fun hV => absurd ⟨V, hV⟩ hex
    rw [hbot, Submodule.mem_bot] at hmem
    exact hne hmem

end S_AutomorphicForm_exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf
end P2MW
export P2MW.S_AutomorphicForm_exists_isCuspConstituent_mem_isotypicCuspSubmodule_archCutSubmodule_hasArchCharacterAt_one_of_archOccursInClassOf (solution)
