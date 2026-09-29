-- Prove2me | solution 1 for AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a2ba6c94-0f94-537d-a010-72840f3ac038

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
import Theorems.Thm_NumberField_TateGlobal_exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar
import Theorems.Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal
namespace ContinuedIntertwining

private theorem identityPrinciple_eventuallyEq_nhdsNE_of_isPreconnected {f g : ℂ → ℂ} {V : Set ℂ}
    (hf : MeromorphicOn f V) (hg : MeromorphicOn g V) (hVc : IsPreconnected V) {z₀ : ℂ} (hz₀ : z₀ ∈ V)
    (h₀ : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = g z) {s : ℂ} (hs : s ∈ V) : ∀ᶠ z in nhdsWithin s {s}ᶜ, f z = g z := by
  have hd : MeromorphicOn (f - g) V := hf.sub hg
  have htop : meromorphicOrderAt (f - g) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (h₀.mono fun z hz => by simp [hz])
  have hs_top : meromorphicOrderAt (f - g) s = ⊤ := by
    by_contra hne
    exact hd.meromorphicOrderAt_ne_top_of_isPreconnected hVc hs hz₀ hne htop
  exact (meromorphicOrderAt_eq_top_iff.mp hs_top).mono fun z hz => by simpa [sub_eq_zero] using hz

private theorem identityPrinciple_eq_of_meromorphicNFAt_of_eventuallyEq_nhdsNE
    {f g : ℂ → ℂ} {s : ℂ} (hf : MeromorphicNFAt f s)
    (hg : MeromorphicNFAt g s) (h : ∀ᶠ z in nhdsWithin s {s}ᶜ, f z = g z) : f s = g s :=
  ((hf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg).mp h).eq_of_nhds

private theorem identityPrinciple_eventually_one_half_lt_re_one : ∀ᶠ z : ℂ in nhds 1, (1 / 2 : ℝ) < z.re :=
  (Complex.continuous_re.tendsto 1).eventually_const_lt (by norm_num)

private theorem eqOn_and_analyticOnNhd_of_meromorphicNFOn_of_eqOn_re_gt_one_half
    (f h : ℂ → ℂ) (V : Set ℂ) (hf : MeromorphicNFOn f Set.univ) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hVh : {s : ℂ | 0 ≤ s.re} ⊆ V) (hh : AnalyticOnNhd ℂ h V)
    (hfh : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → f s = h s) :
    Set.EqOn f h V ∧ AnalyticOnNhd ℂ f V := by
  have hfV : MeromorphicOn f V := fun s _ => (hf (Set.mem_univ s)).meromorphicAt
  have h1V : (1 : ℂ) ∈ V := hVh (by simp)
  have h₀ : ∀ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, f z = h z :=
    eventually_nhdsWithin_of_eventually_nhds
      (identityPrinciple_eventually_one_half_lt_re_one.mono fun z hz => hfh z hz)
  have heq : Set.EqOn f h V := fun s hs =>
    identityPrinciple_eq_of_meromorphicNFAt_of_eventuallyEq_nhdsNE (hf (Set.mem_univ s)) (hh s hs).meromorphicNFAt
      (identityPrinciple_eventuallyEq_nhdsNE_of_isPreconnected hfV hh.meromorphicOn hVc h1V h₀ hs)
  refine ⟨heq, fun s hs => (hh s hs).congr ?_⟩
  exact Filter.eventuallyEq_of_mem (hV.mem_nhds hs) fun z hz => (heq hz).symm

end ContinuedIntertwining

namespace ContinuedIntertwining

private theorem identityPrinciplePole_analyticAt_sub_const (s₀ s : ℂ) : AnalyticAt ℂ (fun z : ℂ => z - s₀) s :=
  analyticAt_id.sub analyticAt_const

private theorem eq_sub_mul_of_meromorphicNFOn_of_analyticOnNhd_of_eq_re_gt_one_half
    (f h : ℂ → ℂ) (s₀ : ℂ) (V : Set ℂ) (hf : MeromorphicNFOn f Set.univ) (hV : IsOpen V)
    (hVc : IsPreconnected V) (hVh : {s : ℂ | 0 ≤ s.re} ⊆ V) (hh : AnalyticOnNhd ℂ h V)
    (hfh : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → h s = (s - s₀) * f s) :
    ∀ s ∈ V, s ≠ s₀ → h s = (s - s₀) * f s := by
  have _ := hV
  have hFV : MeromorphicOn (fun z : ℂ => (z - s₀) * f z) V := fun s _ =>
    (identityPrinciplePole_analyticAt_sub_const s₀ s).meromorphicAt.mul (hf (Set.mem_univ s)).meromorphicAt
  have h1V : (1 : ℂ) ∈ V := hVh (by simp)
  have hre : ∀ᶠ z : ℂ in nhds 1, (1 / 2 : ℝ) < z.re :=
    (Complex.continuous_re.tendsto 1).eventually_const_lt (by norm_num)
  have h₀ : ∀ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, h z = (z - s₀) * f z :=
    eventually_nhdsWithin_of_eventually_nhds (hre.mono fun z hz => hfh z hz)
  intro s hs hs₀
  have hd : MeromorphicOn (h - fun z : ℂ => (z - s₀) * f z) V := hh.meromorphicOn.sub hFV
  have htop : meromorphicOrderAt (h - fun z : ℂ => (z - s₀) * f z) 1 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (h₀.mono fun z hz => by simp [hz])
  have hs_top : meromorphicOrderAt (h - fun z : ℂ => (z - s₀) * f z) s = ⊤ := by
    by_contra hne
    exact hd.meromorphicOrderAt_ne_top_of_isPreconnected hVc hs h1V hne htop
  have hne_s : ∀ᶠ z in nhdsWithin s {s}ᶜ, h z = (z - s₀) * f z :=
    (meromorphicOrderAt_eq_top_iff.mp hs_top).mono fun z hz => by simpa [sub_eq_zero] using hz
  have hFnf : MeromorphicNFAt (fun z : ℂ => (z - s₀) * f z) s :=
    (meromorphicNFAt_mul_iff_right (identityPrinciplePole_analyticAt_sub_const s₀ s) (sub_ne_zero.mpr hs₀)).mpr
      (hf (Set.mem_univ s))
  exact (((hh s hs).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hFnf).mp hne_s).eq_of_nhds

end ContinuedIntertwining

namespace ContinuedIntertwining

private theorem exists_isOpen_isPreconnected_analyticOnNhd_div_and_continuousOn_div
    {G : Type} [TopologicalSpace G] (U : Set ℂ) (hU : IsOpen U) (hUh : {s : ℂ | 0 ≤ s.re} ⊆ U)
    (D : ℂ → ℂ) (hD : Differentiable ℂ D) (hD0 : ∀ s : ℂ, 0 ≤ s.re → D s ≠ 0)
    (H : ℂ → G → ℂ) (hHa : ∀ g : G, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U)
    (hHc : ContinuousOn (fun p : ℂ × G => H p.1 p.2) (U ×ˢ Set.univ)) :
    ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ {s : ℂ | 0 ≤ s.re} ⊆ V ∧ V ⊆ U ∧ (∀ s ∈ V, D s ≠ 0) ∧
      (∀ g : G, AnalyticOnNhd ℂ (fun s : ℂ => H s g / D s) V) ∧
      ContinuousOn (fun p : ℂ × G => H p.1 p.2 / D p.1) (V ×ˢ Set.univ) := by
  have hW : IsOpen (U ∩ {s : ℂ | D s ≠ 0}) := hU.inter (isOpen_ne_fun hD.continuous continuous_const)
  have hhalf : {s : ℂ | 0 ≤ s.re} ⊆ U ∩ {s : ℂ | D s ≠ 0} := fun s hs => ⟨hUh hs, hD0 s hs⟩
  have h0 : (0 : ℂ) ∈ {s : ℂ | 0 ≤ s.re} := Complex.zero_re.symm.le
  have hconv : Convex ℝ {s : ℂ | 0 ≤ s.re} :=
    convex_halfSpace_ge (IsLinearMap.mk Complex.add_re Complex.smul_re) (0 : ℝ)
  have hVW : connectedComponentIn (U ∩ {s : ℂ | D s ≠ 0}) 0 ⊆ U ∩ {s : ℂ | D s ≠ 0} :=
    connectedComponentIn_subset _ _
  have hVU : connectedComponentIn (U ∩ {s : ℂ | D s ≠ 0}) 0 ⊆ U := hVW.trans Set.inter_subset_left
  have hVD : ∀ s ∈ connectedComponentIn (U ∩ {s : ℂ | D s ≠ 0}) 0, D s ≠ 0 := fun s hs => (hVW hs).2
  refine ⟨connectedComponentIn (U ∩ {s : ℂ | D s ≠ 0}) 0, hW.connectedComponentIn,
    isPreconnected_connectedComponentIn, hconv.isPreconnected.subset_connectedComponentIn h0 hhalf, hVU, hVD,
    fun g => ((hHa g).mono hVU).div (fun s _ => hD.analyticAt s) hVD, ?_⟩
  exact (hHc.mono (Set.prod_mono hVU subset_rfl)).div (hD.continuous.comp continuous_fst).continuousOn
    fun p hp => hVD p.1 (Set.mem_prod.1 hp).1

end ContinuedIntertwining

namespace ContinuedIntertwining

private theorem quotientChar_val_mul_inv (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((μ * ν⁻¹) x : ℂˣ) : ℂ) = ((μ x : ℂˣ) : ℂ) * (((ν x : ℂˣ) : ℂ))⁻¹ := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]

private theorem quotientChar_continuous_of_continuous_val
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχ : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) : Continuous χ :=
  Units.isEmbedding_val₀.continuous_iff.2 hχ

private theorem isUnitaryChar_mul_inv_and_exists_mem_normOneIdeles_ne_one_of_forall_ne_normPowChar
    (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (hfree : ∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) :
    IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) ∧ IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) ∧ Continuous (μ * ν⁻¹) ∧
      ∃ x ∈ NumberField.TateGlobal.normOneIdeles F, (μ * ν⁻¹) x ≠ 1 := by
  have hunit : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
    intro x
    rw [quotientChar_val_mul_inv F μ ν x, norm_mul, norm_inv, hμ x, hν x, inv_one, mul_one]
  have hcont : Continuous (μ * ν⁻¹) :=
    quotientChar_continuous_of_continuous_val F (μ * ν⁻¹)
      ((hμc.mul (hνc.inv₀ fun x => Units.ne_zero (ν x))).congr fun x => (quotientChar_val_mul_inv F μ ν x).symm)
  refine ⟨hunit, ?_, hcont, ?_⟩
  · intro u
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμic u, hνic u, inv_one, mul_one]
  · by_contra hcon
    obtain ⟨t, ht⟩ :=
      NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F (μ * ν⁻¹) hcont hunit
        (fun x hx => by
          by_contra hne
          exact hcon ⟨x, hx, hne⟩)
    exact hfree t ht

end ContinuedIntertwining

namespace ContinuedIntertwining

private theorem zetaCarrier_one_lt_absNorm (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

private theorem zetaCarrier_absNorm_ne_zero (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h := zetaCarrier_one_lt_absNorm F v
  exact_mod_cast (zero_lt_one.trans h).ne'

private theorem zetaCarrier_one_sub_cpow_ne_zero (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {w : ℂ} (hw : 0 < w.re) :
    (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w) ≠ 0 := by
  have h1 := zetaCarrier_one_lt_absNorm F v
  have hlt : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (zero_lt_one.trans h1)), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

private theorem zetaCarrier_differentiable_factor (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (c : ℂ) :
    Differentiable ℂ fun s : ℂ => (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + c)) :=
  (differentiable_const (1 : ℂ)).sub
    (((differentiable_id.add_const c).neg).const_cpow (Or.inl (zetaCarrier_absNorm_ne_zero F v)))

private theorem zetaCarrier_differentiable_prod (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (c : ℂ) :
    Differentiable ℂ fun s : ℂ => ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + c))) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiable_const _
  · intro v T hv ih
    simp only [Finset.prod_insert hv]
    exact (zetaCarrier_differentiable_factor F v c).mul ih

open scoped Classical in

private theorem exists_differentiable_eq_sub_mul_partialEulerProduct_normPowChar
    (F : Type) [Field F] [NumberField F] (τ : ℝ) (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T},
          (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (NumberField.TateGlobal.normPowChar F τ) v.1 then
                (((NumberField.TateGlobal.normPowChar F τ) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ)
              else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  obtain ⟨R, hRd, -, hRζ, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero F
  refine ⟨fun s => R (s + (τ : ℂ) * Complex.I) *
      ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + (τ : ℂ) * Complex.I))), ?_, ?_⟩
  · exact (hRd.comp (differentiable_id.add_const _)).mul (zetaCarrier_differentiable_prod F T _)
  · intro s hs
    show R (s + (τ : ℂ) * Complex.I) *
        ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + (τ : ℂ) * Complex.I))) = _
    set w : ℂ := s + (τ : ℂ) * Complex.I with hw
    have hτre : ((τ : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hwre : 1 < w.re := by
      rw [hw, Complex.add_re, hτre, add_zero]
      exact hs
    have hws : w - 1 = s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) := by
      rw [hw]
      ring
    set f : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℂ :=
      fun v => ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹ with hf
    have hE : HasProd f (NumberField.dedekindZeta F w) :=
      NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F w hwre
    have hM : Multipliable fun v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T} => f v.1 := by
      have h := (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F T
        (fun _ => (1 : ℂ)) (fun _ => by simp)).1 w hwre
      simp only [one_mul] at h
      exact h
    have hb : HasProd (f ∘ (↑) : ((↑T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))ᶜ :
        Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) → ℂ)
        (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1) :=
      hM.hasProd
    have hsplit : NumberField.dedekindZeta F w =
        (∏ v ∈ T, f v) * ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 :=
      hE.unique ((Finset.hasProd T f).mul_compl hb)
    have hT : (∏ v ∈ T, f v) * ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [hf]
      exact inv_mul_cancel₀ (zetaCarrier_one_sub_cpow_ne_zero F v (zero_lt_one.trans hwre))
    have hP : ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 =
        NumberField.dedekindZeta F w * ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) := by
      calc ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1
          = (∏ v ∈ T, f v) * (∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) *
              ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 := by rw [hT, one_mul]
        _ = NumberField.dedekindZeta F w *
              ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) := by
            rw [hsplit]
            ring
    have hcoef : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        (if NumberField.TateGlobal.IsUnramifiedCharAt (NumberField.TateGlobal.normPowChar F τ) v then
            (((NumberField.TateGlobal.normPowChar F τ) (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ)
          else 0) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) =
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w) := by
      intro v
      rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg F τ v,
        ← Complex.cpow_add _ _ (zetaCarrier_absNorm_ne_zero F v), hw]
      congr 1
      ring
    calc R w * ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))
        = (w - 1) * NumberField.dedekindZeta F w *
            ∏ v ∈ T, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) := by rw [hRζ w hwre]
      _ = (w - 1) * ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // v ∉ T}, f v.1 := by
            rw [hP]
            ring
      _ = _ := by
            rw [hws]
            congr 1
            exact tprod_congr fun v => by rw [hcoef v.1]

end ContinuedIntertwining

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F,
        (letI := adeleBorel (𝓞 F) F
         MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
          ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)),
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
        ∃ Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
          (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => Mreg s g) U) ∧
          ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2) (U ×ˢ Set.univ) ∧
          ∀ s ∈ U, s ≠ ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I) →
            ∀ g : AdelicGL2 (𝓞 F) F, Mreg s g = (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Mc s g) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
        (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => Mc s g) U) ∧
        ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mc p.1 p.2) (U ×ˢ Set.univ)) := by
  intro α hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol hμc hνc hφKu Mc hMc
  have hN1H := AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation F
    hα μ ν hμ hν hμic hνic φ hφ hφK hφf hφjc hφhol hμc hνc hφKu Mc hMc
  have hre : ∀ s : ℂ, (2 * s + 1).re = 2 * s.re + 1 := by
    intro s
    simp [Complex.add_re, Complex.mul_re]
  refine ⟨?_, ?_⟩
  · intro τ hτ
    obtain ⟨Q, hQ, hQE⟩ :=
      ContinuedIntertwining.exists_differentiable_eq_sub_mul_partialEulerProduct_normPowChar F τ ∅
    obtain ⟨A, N, hP⟩ :=
      NumberField.TateGlobal.exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar F τ ∅ Q hQ hQE
    have hD0 : ∀ s : ℂ, 0 ≤ s.re → Q (2 * s + 1) ≠ 0 := by
      intro s hs h0
      have h1 := hP (2 * s + 1) (by rw [hre]; linarith)
      rw [h0, norm_zero, mul_zero] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨U, hU, hUh, H, hHa, hHc, hid⟩ := hN1H.1 τ hτ Q hQ (by
      intro w hw
      rw [hτ]
      exact hQE w hw)
    obtain ⟨V, hV, hVc, hVh, -, -, hVa, hVcont⟩ :=
      ContinuedIntertwining.exists_isOpen_isPreconnected_analyticOnNhd_div_and_continuousOn_div U hU hUh
        (fun s : ℂ => Q (2 * s + 1)) (by fun_prop) hD0 H hHa hHc
    refine ⟨V, hV, hVh, fun s g => H s g / Q (2 * s + 1), hVa, hVcont, ?_⟩
    intro s hs hs₀ g
    refine ContinuedIntertwining.eq_sub_mul_of_meromorphicNFOn_of_analyticOnNhd_of_eq_re_gt_one_half
      (fun s : ℂ => Mc s g) (fun s : ℂ => H s g / Q (2 * s + 1)) _ V (hMc g).1 hV hVc hVh (hVa g) ?_ s hs hs₀
    intro s' hs'
    have hne : Q (2 * s' + 1) ≠ 0 := hD0 s' (by linarith)
    show H s' g / Q (2 * s' + 1) = _ * Mc s' g
    rw [hid s' hs' g]
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hne]
  · intro hfree
    obtain ⟨hu, hic, hc, hne⟩ :=
      ContinuedIntertwining.isUnitaryChar_mul_inv_and_exists_mem_normOneIdeles_ne_one_of_forall_ne_normPowChar F μ ν
        hμ hν hμic hνic hμc hνc hfree
    obtain ⟨L, hL, hLE⟩ :=
      NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one F
        (μ * ν⁻¹) hic hc hu hne ∅
    obtain ⟨A, N, hE⟩ :=
      NumberField.TateGlobal.exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct F
        (μ * ν⁻¹) hic hc hu hne ∅ L hL hLE
    have hD0 : ∀ s : ℂ, 0 ≤ s.re → L (2 * s + 1) ≠ 0 := by
      intro s hs h0
      have h1 := hE (2 * s + 1) (by rw [hre]; linarith)
      rw [h0, norm_zero, mul_zero] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨U, hU, hUh, H, hHa, hHc, hid⟩ := hN1H.2 hfree L hL hLE
    obtain ⟨V, hV, hVc, hVh, -, -, hVa, hVcont⟩ :=
      ContinuedIntertwining.exists_isOpen_isPreconnected_analyticOnNhd_div_and_continuousOn_div U hU hUh
        (fun s : ℂ => L (2 * s + 1)) (by fun_prop) hD0 H hHa hHc
    have key : ∀ g : AdelicGL2 (𝓞 F) F,
        Set.EqOn (fun s : ℂ => Mc s g) (fun s : ℂ => H s g / L (2 * s + 1)) V ∧
          AnalyticOnNhd ℂ (fun s : ℂ => Mc s g) V := by
      intro g
      refine ContinuedIntertwining.eqOn_and_analyticOnNhd_of_meromorphicNFOn_of_eqOn_re_gt_one_half
        (fun s : ℂ => Mc s g) (fun s : ℂ => H s g / L (2 * s + 1)) V (hMc g).1 hV hVc hVh (hVa g) ?_
      intro s' hs'
      have hne : L (2 * s' + 1) ≠ 0 := hD0 s' (by linarith)
      show Mc s' g = H s' g / L (2 * s' + 1)
      rw [hid s' hs' g]
      rw [mul_div_cancel_left₀ _ hne]
    refine ⟨V, hV, hVh, fun g => (key g).2, ?_⟩
    refine hVcont.congr ?_
    rintro ⟨s, g⟩ ⟨hsV, -⟩
    exact (key g).1 hsV

end S_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
end P2MW
export P2MW.S_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection (solution)
