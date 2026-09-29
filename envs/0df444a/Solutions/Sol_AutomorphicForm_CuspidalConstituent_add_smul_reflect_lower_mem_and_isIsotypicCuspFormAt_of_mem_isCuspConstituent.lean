-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/332b7046-2a44-5572-a8b8-42018d9b4278

import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ)
    (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) φ)
    (hsm : IsArchSmoothAt hw φ) (hcas : archCasimirAt hw φ = lam • φ)
    (c : ℂ) :
    let ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := φ + c • (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))
        (g * archRealGLAt hw UpperHalfPlane.J))
    ψ ∈ V ∧
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ ψ ∧
    HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) ψ ∧
    IsArchSmoothAt hw ψ ∧ archCasimirAt hw ψ = lam • ψ ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d ψ)) := by
  intro ψ
  classical
  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat

  set T : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun θ g =>
      (archDerivAt hw ArchDir.H θ - Complex.I • (archDerivAt hw ArchDir.E θ + archDerivAt hw ArchDir.Fm θ))
        (g * archRealGLAt hw UpperHalfPlane.J) with hTdef
  have hψdef : ψ = φ + c • T φ := rfl
  obtain ⟨-, hTsm, hTwt, -, -⟩ := AutomorphicForm.isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul ℚ w hw T hTdef φ hsm
  have hTwt1 := hTwt hwt

  have hψwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) ψ := by
    intro k g
    rw [hψdef]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hwt k g, hTwt1 k g]
    ring
  by_cases h0 : φ = 0
  ·
    have hL0 : archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0 := by
      have hz : ∀ d : ArchDir, archDerivAt hw d φ = 0 := by
        intro d; rw [h0]; exact archDerivAt_const hw d 0
      rw [hz, hz, hz]; simp
    have hT0 : T φ = 0 := by
      funext g
      show (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))
        (g * archRealGLAt hw UpperHalfPlane.J) = 0
      rw [hL0]; rfl
    have hψφ : ψ = φ := by rw [hψdef, hT0, smul_zero, add_zero]
    have hd0 : ∀ d : ArchDir, Continuous (archDerivAt hw d ψ) := by
      intro d
      rw [hψφ, h0]
      have hz0 : archDerivAt hw d (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) = 0 := archDerivAt_const hw d 0
      rw [hz0]; exact continuous_const
    rw [hψφ] at hψwt ⊢
    exact ⟨hφV, hiso, hψwt, hsm, hcas, by rwa [hψφ] at hd0⟩

  let χ : ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
    fun v => archWeightCharAt (isReal_infinitePlace_rat v) 1
  let χ' : ℤ → ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
    fun m v => archWeightCharAt (isReal_infinitePlace_rat v) m
  have hmem : φ ∈ V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N ⊓
        archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
    refine ⟨⟨hφV, fun g u' hu' => hiso.level_invariant g u' hu'⟩, ?_⟩
    refine (mem_archCutSubmodule_ofChar_iff (F := ℚ) χ φ).mpr fun v => ?_
    obtain rfl : v = w := Subsingleton.elim _ _
    exact hwt
  have hX : V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) N ⊓
        archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) ≠ ⊥ := by
    intro hbot
    apply h0
    have := hmem
    rw [hbot] at this
    exact (Submodule.mem_bot ℂ).mp this
  have h51 := AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar ℚ
    (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov ξ V hV
    isReal_infinitePlace_rat N hN χ w hw 1 rfl χ'
    (fun m v hv => absurd (Subsingleton.elim v w) hv) (fun m => rfl) φ hmem
  have hlow3 := h51.1 1
  simp only [Function.iterate_one] at hlow3
  have hlowV : (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) ∈ V :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp hlow3).1).1

  have hTV : T φ ∈ V :=
    AutomorphicForm.CuspidalConstituent.comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov ξ N S Φ V hV ⟨φ, hφV, h0, hiso⟩ w hw _ hlowV
  have hψV : ψ ∈ V := by rw [hψdef]; exact V.add_mem hφV (V.smul_mem c hTV)

  obtain ⟨lamV, hallV⟩ := AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent ℚ
    (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov ξ V hV N hN
    (ArchTypeFamily.ofChar ℚ χ) hX w hw
  have hsmV : ∀ x ∈ V, IsArchSmoothAt hw x := fun x hx => (hallV x hx).1
  obtain ⟨hψsm, hψd1, -, hψcas⟩ := hallV ψ hψV
  have hlam : lamV = lam := by
    obtain ⟨-, -, -, hφcas⟩ := hallV φ hφV
    have h := hcas.symm.trans hφcas
    by_contra hne
    apply h0
    have h2 : (lam - lamV) • φ = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) (fun e => hne e.symm)
    · exact h3

  have hφmem := hiso.mem_isotypicCuspSubmodule
  obtain ⟨hLiso, -⟩ := AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem ℚ
    (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) ξ N S Φ V hV w hw hsmV φ hφV h0 hφmem
  have hLmem := hLiso hlowV
  have hTmem : T φ ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) ξ N S Φ := by
    by_cases hL0 : (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) = 0
    · have : T φ = 0 := by
        funext g
        show (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))
          (g * archRealGLAt hw UpperHalfPlane.J) = 0
        rw [hL0]; rfl
      rw [this]; exact Submodule.zero_mem _
    · obtain ⟨-, hJiso⟩ := AutomorphicForm.CuspidalConstituent.lower_mem_isotypicCuspSubmodule_and_comp_J_mem_isotypicCuspSubmodule_of_mem ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) ξ N S Φ V hV w hw hsmV _ hlowV hL0 hLmem
      exact hJiso hTV
  have hψmem : ψ ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) ξ N S Φ := by
    rw [hψdef]; exact Submodule.add_mem _ hφmem (Submodule.smul_mem _ c hTmem)
  have hψiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ ψ := by
    by_cases hψ0 : ψ = 0
    ·
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hψ0]; exact isSmoothCuspAutomorphicFnAt_zero ℚ _ ξ
      · rw [hψ0]; exact continuous_const
      · intro g u' hu'; rw [hψ0]; rfl
      · intro v hv
        obtain ⟨reps, hsys, -⟩ := hiso.hecke_eigen v hv
        refine ⟨reps, hsys, fun g => ?_⟩
        rw [hψ0]
        simp [SmoothCusp.heckeCosetSum]
      · intro v hv g; rw [hψ0]; simp
    · exact AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule ℚ _ _ _ ξ N S Φ ψ hψmem hψ0
  refine ⟨hψV, hψiso, hψwt, hψsm, ?_, hψd1⟩
  rw [← hlam]; exact hψcas

end S_AutomorphicForm_CuspidalConstituent_add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent (solution)
