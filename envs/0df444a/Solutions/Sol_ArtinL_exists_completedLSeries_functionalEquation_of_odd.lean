-- Prove2me | solution 1 for ArtinL.exists_completedLSeries_functionalEquation_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/712407f4-54d1-567d-b7b9-22464473c1dc

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
import Theorems.Thm_ArtinL_LSeriesSummable_coeff_of_one_lt_re
import Theorems.Thm_ArtinL_Abelian_exists_completedLSeries_functionalEquation_u0
import Theorems.Thm_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd
import Theorems.Thm_ArtinL_Abelian_induced_apply_isConj_eq_nPlus_sub_nMinus
import Theorems.Thm_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
import Theorems.Thm_ArtinL_conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_exists_completedLSeries_functionalEquation_of_odd
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FLT.InfiniteAdeleBaseChange.uniqueSelfExtension"
p2m_attr_erase "instance" "NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup AutomorphicForm.CuspidalityNotion.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply"
p2m_attr_erase "simp" "JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open NumberField NumberField.InfinitePlace Complex Finset

namespace ArtinFEAssembly

section Algebra

variable {ι : Type*} [Fintype ι]

theorem expand (E Lq : ι → ℂ) (p q r m : ι → ℕ) (A B : ℂ) :
    ∏ i, (E i * A ^ p i * B ^ q i * (A * B) ^ r i * Lq i) ^ m i =
      (∏ i, E i ^ m i) * A ^ (∑ i, m i * (p i + r i)) * B ^ (∑ i, m i * (q i + r i)) *
        ∏ i, Lq i ^ m i := by
  have h : ∀ i, (E i * A ^ p i * B ^ q i * (A * B) ^ r i * Lq i) ^ m i =
      E i ^ m i * (A ^ (m i * (p i + r i)) * (B ^ (m i * (q i + r i)) * Lq i ^ m i)) := by
    intro i; ring
  simp_rw [h, prod_mul_distrib, prod_pow_eq_pow_sum]
  ring

theorem key (a : ι → ℤ) (Λ P E Lq : ι → ℂ) (p q r : ι → ℕ) (A B S₁ S₂ EN Lρ : ℂ)
    (hΛ : ∀ i, Λ i = P i * (E i * A ^ p i * B ^ q i * (A * B) ^ r i * Lq i))
    (hP₁ : ∏ i, P i ^ (a i).toNat = S₁) (hP₂ : ∏ i, P i ^ (-a i).toNat = S₂)
    (hE : ∏ i, E i ^ (a i).toNat = EN * ∏ i, E i ^ (-a i).toNat)
    (hp : ∑ i, (a i).toNat * (p i + r i) = 1 + ∑ i, (-a i).toNat * (p i + r i))
    (hq : ∑ i, (a i).toNat * (q i + r i) = 1 + ∑ i, (-a i).toNat * (q i + r i))
    (hL : Lρ * ∏ i, Lq i ^ (-a i).toNat = ∏ i, Lq i ^ (a i).toNat) :
    S₂ * ∏ i, Λ i ^ (a i).toNat = (S₁ * ∏ i, Λ i ^ (-a i).toNat) * (EN * A * B) * Lρ := by
  have h1 : ∀ m : ι → ℕ, ∏ i, Λ i ^ m i = (∏ i, P i ^ m i) *
      ((∏ i, E i ^ m i) * A ^ (∑ i, m i * (p i + r i)) * B ^ (∑ i, m i * (q i + r i)) *
        ∏ i, Lq i ^ m i) := by
    intro m
    rw [← expand, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [hΛ, mul_pow]
  rw [h1, h1, hP₁, hP₂, hE, hp, hq, ← hL, pow_add, pow_add, pow_one, pow_one]
  ring

end Algebra

section Analysis

theorem cpow_ofReal_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (w : ℂ) :
    (((x : ℝ) : ℂ) ^ w) ^ n = (((x ^ n : ℝ)) : ℂ) ^ w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx]

theorem prod_cpow_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (w : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ w = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf i) (prod_nonneg fun j _ => hf j)]

theorem LSeries_conj (f : ℕ → ℂ) (s : ℂ) :
    LSeries (fun n => starRingEnd ℂ (f n)) s = starRingEnd ℂ (LSeries f (starRingEnd ℂ s)) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', map_div₀]
    congr 1
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj (n : ℂ) s harg
    rw [Complex.conj_natCast] at this
    rw [this, Complex.conj_conj]

theorem Gammaℝ_ne_zero {s : ℂ} (hs : 1 < s.re) : Gammaℝ s ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)

theorem Gammaℝ_add_one_ne_zero {s : ℂ} (hs : 1 < s.re) : Gammaℝ (s + 1) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

theorem sub_ne_zero_of_lt {s : ℂ} (hs : 1 < s.re) : s * (s - 1) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · rintro rfl; norm_num at hs
  · rw [sub_ne_zero]; rintro rfl; norm_num at hs

theorem sqrt_gamma (N : ℕ) (s : ℂ) :
    (((N : ℝ)) : ℂ) ^ (s / 2) * (Gammaℝ s * Gammaℝ (s + 1)) =
      2 * ((((Real.sqrt N / (2 * Real.pi) : ℝ)) : ℂ) ^ s * Complex.Gamma s) := by
  rw [Complex.Gammaℝ_mul_Gammaℝ_add_one, Complex.Gammaℂ_def]
  have hN : (((N : ℝ)) : ℂ) ^ (s / 2) = (((Real.sqrt N : ℝ)) : ℂ) ^ s := by
    have h0 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
    have h1 : (((N : ℝ)) : ℂ) ^ (s / 2) = (((Real.sqrt N ^ 2 : ℝ)) : ℂ) ^ (s / 2) := by
      rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [h1, ← cpow_ofReal_pow _ h0, ← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have h2 : ((2 : ℂ) * Real.pi) ^ (-s) = ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) ^ s := by
    rw [Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow]
    · push_cast; ring_nf
    · rw [show ((2 * Real.pi : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) from rfl]
      push_cast
      rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm
  rw [hN, h2, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg _) hpi]
  ring

end Analysis

section Pieces

theorem trace_eq_zero_of_mul_self_eq_one (A : Matrix (Fin 2) (Fin 2) ℂ) (h1 : A * A = 1)
    (h2 : A.det = -1) : A.trace = 0 := by
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  rw [Matrix.det_fin_two] at h2
  rw [Matrix.trace_fin_two]
  have ht : (A 0 0 + A 1 1) * (A 0 0 + A 1 1) = 0 := by linear_combination e00 + e11 + 2 * h2
  exact mul_self_eq_zero.1 ht

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Classical in

theorem induced_one {F : Type} [Field F] [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) :
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F, (if hx : x⁻¹ * 1 * x ∈ H then (((χ ⟨x⁻¹ * 1 * x, hx⟩ : ℂˣ) : ℂ)) else 0) =
      (Module.finrank ℚ (IntermediateField.fixedField H) : ℂ) := by
  classical
  have hmem : ∀ x : F ≃ₐ[ℚ] F, x⁻¹ * 1 * x ∈ H := fun x => by simp
  have hterm : ∀ x : F ≃ₐ[ℚ] F,
      (if hx : x⁻¹ * 1 * x ∈ H then (((χ ⟨x⁻¹ * 1 * x, hx⟩ : ℂˣ) : ℂ)) else 0) = 1 := by
    intro x
    rw [dif_pos (hmem x)]
    have : (⟨x⁻¹ * 1 * x, hmem x⟩ : H) = 1 := Subtype.ext (by simp)
    rw [this, map_one, Units.val_one]
  simp_rw [hterm]
  rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hH : Nat.card H = Module.finrank (IntermediateField.fixedField H) F := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, IsGalois.card_fixingSubgroup_eq_finrank,
      IntermediateField.fixingSubgroup_fixedField H]
  have hG : Fintype.card (F ≃ₐ[ℚ] F) = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have htower : Module.finrank ℚ F =
      Module.finrank ℚ (IntermediateField.fixedField H) *
        Module.finrank (IntermediateField.fixedField H) F :=
    (Module.finrank_mul_finrank ℚ (IntermediateField.fixedField H) F).symm
  have hpos : (Nat.card H : ℂ) ≠ 0 := by
    rw [hH]; exact_mod_cast Module.finrank_pos.ne'
  rw [hG, htower, Nat.cast_mul, ← hH]
  field_simp

theorem finrank_eq_nPlus_add {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    Module.finrank ℚ K =
      ArtinL.Abelian.nPlus ψ + ArtinL.Abelian.nMinus ψ + 2 * nrComplexPlaces K := by
  rw [ArtinL.Abelian.nPlus_add_nMinus, card_add_two_mul_card_eq_rank]

end Pieces

section Main

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

theorem differentiable_prod_pow {ι : Type*} (u : Finset ι) (f : ι → ℂ → ℂ) (m : ι → ℕ)
    (hf : ∀ i, Differentiable ℂ (f i)) : Differentiable ℂ fun s => ∏ i ∈ u, f i s ^ m i := by
  have h := Differentiable.finsetProd (u := u) (f := fun i => (f i) ^ (m i))
    (fun i _ => (hf i).pow (m i))
  convert h using 1 <;> try rfl
  ext s
  simp [Finset.prod_apply]

theorem abelian_piece (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (Hs : Subgroup (F ≃ₐ[ℚ] F)) (χ : Hs →* ℂˣ) :
    ∃ (W : ℂ) (Λa Λb : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λa ∧ Differentiable ℂ Λb ∧
      (0 < |(discr (IntermediateField.fixedField Hs) : ℝ)| *
          (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup Hs χ)) : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re →
        Λa s = (if ArtinL.Abelian.ofSubgroup Hs χ = 1 then s * (s - 1) else 1) *
          (((|(discr (IntermediateField.fixedField Hs) : ℝ)| *
              (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup Hs χ)) : ℝ) :
                ℝ) : ℂ) ^ (s / 2) *
            Gammaℝ s ^ ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup Hs χ) *
            Gammaℝ (s + 1) ^ ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup Hs χ) *
            (Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces (IntermediateField.fixedField Hs) *
            ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup Hs χ) s) ∧
        Λb s = (if ArtinL.Abelian.ofSubgroup Hs χ = 1 then s * (s - 1) else 1) *
          (((|(discr (IntermediateField.fixedField Hs) : ℝ)| *
              (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup Hs χ)) : ℝ) :
                ℝ) : ℂ) ^ (s / 2) *
            Gammaℝ s ^ ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup Hs χ) *
            Gammaℝ (s + 1) ^ ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup Hs χ) *
            (Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces (IntermediateField.fixedField Hs) *
            ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup Hs χ)⁻¹ s) ∧
        ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup Hs χ) s ≠ 0 ∧
        ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup Hs χ)⁻¹ s ≠ 0 ∧
        ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup Hs χ)⁻¹ s =
          starRingEnd ℂ (ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup Hs χ)
            (starRingEnd ℂ s))) ∧
      (∀ s : ℂ, Λa (1 - s) = W * Λb s) := by
  obtain ⟨W, Λa, Λb, hW, hΛa, hΛb, hval, hFE⟩ :=
    ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0 (IntermediateField.fixedField Hs) F
      (ArtinL.Abelian.ofSubgroup Hs χ)
  refine ⟨W, Λa, Λb, hW, hΛa, hΛb, ?_, fun s hs => ?_, hFE⟩
  · exact mul_pos
      (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero (IntermediateField.fixedField Hs)))
      (by exact_mod_cast ArtinL.Abelian.absNorm_conductor_pos (ArtinL.Abelian.ofSubgroup Hs χ))
  refine ⟨?_, ?_,
    (ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd _ F
      (ArtinL.Abelian.ofSubgroup Hs χ) hs).2.1,
    (ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd _ F
      (ArtinL.Abelian.ofSubgroup Hs χ)⁻¹ hs).2.1, ?_⟩
  · rw [(hval s hs).1, ArtinL.Abelian.completedLSeries, Complex.Gammaℝ_mul_Gammaℝ_add_one]
  · rw [(hval s hs).2, ArtinL.Abelian.completedLSeries, Complex.Gammaℝ_mul_Gammaℝ_add_one,
      ArtinL.Abelian.conductor_inv, ArtinL.Abelian.nPlus_inv, ArtinL.Abelian.nMinus_inv]
  · rw [ArtinL.Abelian.LSeries, ArtinL.Abelian.LSeries, ← LSeries_conj]
    exact congrArg (fun f => LSeries f s)
      (funext fun n => ArtinL.Abelian.coeff_inv (ArtinL.Abelian.ofSubgroup Hs χ) n)

set_option maxHeartbeats 1600000 in
open scoped Classical in

theorem signature (ρ : Γℚ →* GL (Fin 2) ℂ)
    (hodd : ((ρ complexConjugation : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin 2) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0)) :
    (∑ i, (a i).toNat * (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup (H i) (χ i)) +
        nrComplexPlaces (IntermediateField.fixedField (H i))) =
      1 + ∑ i, (-a i).toNat * (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup (H i) (χ i)) +
        nrComplexPlaces (IntermediateField.fixedField (H i)))) ∧
    (∑ i, (a i).toNat * (ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup (H i) (χ i)) +
        nrComplexPlaces (IntermediateField.fixedField (H i))) =
      1 + ∑ i, (-a i).toNat * (ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup (H i) (χ i)) +
        nrComplexPlaces (IntermediateField.fixedField (H i)))) := by

  set p : Fin k → ℕ := fun i => ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup (H i) (χ i)) with hp
  set q : Fin k → ℕ := fun i => ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup (H i) (χ i)) with hq
  set r : Fin k → ℕ := fun i => nrComplexPlaces (IntermediateField.fixedField (H i)) with hr

  set cF : F ≃ₐ[ℚ] F := AlgEquiv.restrictNormalHom F complexConjugation with hcF
  set φ : F →+* ℂ := complexEmbedding.toRingHom.comp (algebraMap F (AlgebraicClosure ℚ)) with hφ
  have hconj : ComplexEmbedding.IsConj φ cF := by
    refine RingHom.ext fun x => ?_
    rw [ComplexEmbedding.conjugate_coe_eq]
    change starRingEnd ℂ (complexEmbedding (algebraMap F (AlgebraicClosure ℚ) x)) =
      complexEmbedding (algebraMap F (AlgebraicClosure ℚ)
        ((complexConjugation.restrictNormal F) x))
    rw [AlgEquiv.restrictNormal_commutes, complexEmbedding_complexConjugation]

  have hρc : ρ complexConjugation = ρF cF := by rw [hρ]; rfl
  have htr0 : ((ρF cF : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = 0 := by
    rw [← hρc]
    refine trace_eq_zero_of_mul_self_eq_one _ ?_ hodd
    rw [← Units.val_mul, ← map_mul, complexConjugation_mul_self, map_one, Units.val_one]
  have e1 : ∑ i, (a i : ℂ) * ((p i : ℂ) - (q i : ℂ)) = 0 := by
    rw [← htr0, htr cF]
    exact sum_congr rfl fun i _ => by
      rw [ArtinL.Abelian.induced_apply_isConj_eq_nPlus_sub_nMinus φ cF hconj (H i) (χ i)]

  have e2 : ∑ i, (a i : ℂ) * ((p i : ℂ) + (q i : ℂ) + 2 * (r i : ℂ)) = 2 := by
    have h2 : ((ρF 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = 2 := by
      rw [map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]; norm_num
    have h3 : ((ρF 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace =
        ∑ i, (a i : ℂ) * ((p i : ℂ) + (q i : ℂ) + 2 * (r i : ℂ)) := by
      rw [htr 1]
      refine sum_congr rfl fun i _ => ?_
      rw [induced_one (H i) (χ i), finrank_eq_nPlus_add (ArtinL.Abelian.ofSubgroup (H i) (χ i))]
      push_cast
      rfl
    rw [← h3, h2]

  have e1z : ∑ i, a i * ((p i : ℤ) - q i) = 0 := by exact_mod_cast e1
  have e2z : ∑ i, a i * ((p i : ℤ) + q i + 2 * r i) = 2 := by exact_mod_cast e2
  have e3 : ∑ i, a i * ((p i : ℤ) + r i) = 1 := by
    have hsum : ∑ i, a i * ((p i : ℤ) - q i) + ∑ i, a i * ((p i : ℤ) + q i + 2 * r i) =
        2 * ∑ i, a i * ((p i : ℤ) + r i) := by
      rw [← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    linarith
  have e4 : ∑ i, a i * ((q i : ℤ) + r i) = 1 := by
    have hsum : ∑ i, a i * ((p i : ℤ) + r i) - ∑ i, a i * ((p i : ℤ) - q i) =
        ∑ i, a i * ((q i : ℤ) + r i) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    linarith

  have split : ∀ x : Fin k → ℤ, ∑ i, a i * x i =
      ∑ i, ((a i).toNat : ℤ) * x i - ∑ i, ((-a i).toNat : ℤ) * x i := by
    intro x
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by rw [← sub_mul, Int.toNat_sub_toNat_neg]
  constructor
  · have h := e3
    rw [split] at h
    have h' : ((∑ i, (a i).toNat * (p i + r i) : ℕ) : ℤ) =
        ((1 + ∑ i, (-a i).toNat * (p i + r i) : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast h'
  · have h := e4
    rw [split] at h
    have h' : ((∑ i, (a i).toNat * (q i + r i) : ℕ) : ℤ) =
        ((1 + ∑ i, (-a i).toNat * (q i + r i) : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast h'

open scoped Classical in

theorem conductor_piece {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {k : ℕ} (H : Fin k → Subgroup (F ≃ₐ[ℚ] F)) (χ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ((ρF g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : F ≃ₐ[ℚ] F,
          if hx : x⁻¹ * g * x ∈ H i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0))
    (w : ℂ) :
    ∏ i, (((|(discr (IntermediateField.fixedField (H i)) : ℝ)| *
        (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i))) : ℝ) :
          ℝ) : ℂ) ^ w) ^ (a i).toNat =
      ((((ArtinL.conductor ρ : ℕ) : ℝ)) : ℂ) ^ w *
        ∏ i, (((|(discr (IntermediateField.fixedField (H i)) : ℝ)| *
          (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i))) : ℝ) :
            ℝ) : ℂ) ^ w) ^ (-a i).toNat := by
  set D : Fin k → ℝ := fun i => |(discr (IntermediateField.fixedField (H i)) : ℝ)| *
    (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i))) : ℝ) with hD
  have hD0 : ∀ i, 0 ≤ D i := fun i => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hpow : ∀ m : Fin k → ℕ, ∏ i, ((((D i : ℝ)) : ℂ) ^ w) ^ m i =
      (((∏ i, D i ^ m i : ℝ)) : ℂ) ^ w := by
    intro m
    rw [← prod_cpow_ofReal _ _ (fun i => pow_nonneg (hD0 i) _)]
    exact prod_congr rfl fun i _ => cpow_ofReal_pow _ (hD0 i) _ _
  have hcond := ArtinL.conductor_mul_prod_pow_eq_prod_pow_of_trace_eq_sum ρ F ρF hρ H χ a htr
  have hcondR : (∏ i, D i ^ (a i).toNat : ℝ) = (ArtinL.conductor ρ : ℝ) * ∏ i, D i ^ (-a i).toNat := by
    have h := congrArg (Nat.cast (R := ℝ)) hcond
    push_cast at h
    simp only [Nat.cast_natAbs, Int.cast_abs] at h
    rw [← h]
  change ∏ i, ((((D i : ℝ)) : ℂ) ^ w) ^ (a i).toNat =
    ((((ArtinL.conductor ρ : ℕ) : ℝ)) : ℂ) ^ w * ∏ i, ((((D i : ℝ)) : ℂ) ^ w) ^ (-a i).toNat
  rw [hpow, hpow, hcondR, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (prod_nonneg fun i _ => pow_nonneg (hD0 i) _)]

set_option maxHeartbeats 1600000 in
open scoped Classical in
theorem main (ρ : Γℚ →* GL (Fin 2) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (hodd : ((ρ complexConjugation : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = -1) :
    ∃ (W : ℂ) (Λ₁ Λ₂ Λ₁' Λ₂' : ℂ → ℂ), W ≠ 0 ∧
      Differentiable ℂ Λ₁ ∧ Differentiable ℂ Λ₂ ∧ Differentiable ℂ Λ₁' ∧ Differentiable ℂ Λ₂' ∧
      (∀ s : ℂ, 1 < s.re →
        LSeriesSummable (ArtinL.coeff ρ) s ∧ Λ₂ s ≠ 0 ∧ Λ₂' s ≠ 0 ∧
        Λ₁ s = Λ₂ s *
          (((Real.sqrt (ArtinL.conductor ρ) / (2 * Real.pi) : ℝ) : ℂ) ^ s * Complex.Gamma s *
            _root_.LSeries (ArtinL.coeff ρ) s) ∧
        Λ₁' s = Λ₂' s *
          (((Real.sqrt (ArtinL.conductor ρ) / (2 * Real.pi) : ℝ) : ℂ) ^ s * Complex.Gamma s *
            _root_.LSeries (fun m => starRingEnd ℂ (ArtinL.coeff ρ m)) s)) ∧
      (∀ s : ℂ, Λ₁ (1 - s) = W * Λ₁' s) ∧
      (∀ s : ℂ, Λ₂ (1 - s) = Λ₂' s) := by

  obtain ⟨L₀, hfd₀, hL₀⟩ := id hρ
  haveI := hfd₀
  set F : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L₀ (AlgebraicClosure ℚ) with hFdef
  haveI hfdF : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ L₀ _
  haveI hNF : Normal ℚ F := normalClosure.normal ℚ L₀ _
  haveI : NumberField F := ⟨⟩
  haveI : IsGalois ℚ F := ⟨⟩
  set res := (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F) with hres
  have hker : res.ker ≤ ρ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    change σ.restrictNormal F = 1 at hσ
    refine hL₀ σ fun x hx => ?_
    have h := AlgEquiv.restrictNormal_commutes σ F ⟨x, IntermediateField.le_normalClosure L₀ hx⟩
    rw [hσ, AlgEquiv.one_apply] at h
    exact h.symm
  have hsurj : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective _
  set ρF : (F ≃ₐ[ℚ] F) →* GL (Fin 2) ℂ :=
    MonoidHom.liftOfRightInverse res (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨ρ, hker⟩ with hρF
  have hfac : ρ = ρF.comp res :=
    (MonoidHom.liftOfRightInverse_comp res (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨ρ, hker⟩).symm

  obtain ⟨k, H, χ, a, htr⟩ :=
    BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter ρF

  choose W Λa Λb hW hΛa hΛb hDpos hval hFE using fun i => abelian_piece F (H i) (χ i)

  set m₁ : ℕ := ∑ i, (a i).toNat *
    (if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1 then 1 else 0) with hm₁
  set m₂ : ℕ := ∑ i, (-a i).toNat *
    (if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1 then 1 else 0) with hm₂
  set Wneg : ℂ := ∏ i, W i ^ (-a i).toNat with hWneg
  set Wpos : ℂ := ∏ i, W i ^ (a i).toNat with hWpos
  have hWneg0 : Wneg ≠ 0 := prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hW i)
  have hWpos0 : Wpos ≠ 0 := prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hW i)
  refine ⟨Wpos / Wneg,
    fun s => (s * (s - 1)) ^ m₂ * ∏ i, Λa i s ^ (a i).toNat,
    fun s => 2 * (s * (s - 1)) ^ m₁ * ∏ i, Λa i s ^ (-a i).toNat,
    fun s => Wneg * ((s * (s - 1)) ^ m₂ * ∏ i, Λb i s ^ (a i).toNat),
    fun s => Wneg * (2 * (s * (s - 1)) ^ m₁ * ∏ i, Λb i s ^ (-a i).toNat),
    div_ne_zero hWpos0 hWneg0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · have hpoly : Differentiable ℂ fun s : ℂ => (s * (s - 1)) ^ m₂ :=
      (differentiable_id.mul (differentiable_id.sub_const 1)).pow _
    exact hpoly.mul (differentiable_prod_pow _ _ _ hΛa)
  · have hpoly : Differentiable ℂ fun s : ℂ => 2 * (s * (s - 1)) ^ m₁ :=
      (differentiable_const 2).mul ((differentiable_id.mul (differentiable_id.sub_const 1)).pow _)
    exact hpoly.mul (differentiable_prod_pow _ _ _ hΛa)
  · have hpoly : Differentiable ℂ fun s : ℂ => (s * (s - 1)) ^ m₂ :=
      (differentiable_id.mul (differentiable_id.sub_const 1)).pow _
    exact (differentiable_const _).mul (hpoly.mul (differentiable_prod_pow _ _ _ hΛb))
  · have hpoly : Differentiable ℂ fun s : ℂ => 2 * (s * (s - 1)) ^ m₁ :=
      (differentiable_const 2).mul ((differentiable_id.mul (differentiable_id.sub_const 1)).pow _)
    exact (differentiable_const _).mul (hpoly.mul (differentiable_prod_pow _ _ _ hΛb))

  · intro s hs
    have hS : s * (s - 1) ≠ 0 := sub_ne_zero_of_lt hs
    have hA0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero hs
    have hB0 : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_add_one_ne_zero hs
    have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs

    obtain ⟨hp, hq⟩ := signature ρ hodd F ρF hfac H χ a htr
    have hE := conductor_piece ρ F ρF hfac H χ a htr (s / 2)
    have hL := ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum ρ F ρF hfac H χ a htr hs
    have hL' : _root_.LSeries (fun m => starRingEnd ℂ (ArtinL.coeff ρ m)) s *
        ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i))⁻¹ s ^ (-a i).toNat =
        ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i))⁻¹ s ^ (a i).toNat := by
      have h := congrArg (starRingEnd ℂ)
        (ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum ρ F ρF hfac H χ a htr hs')
      rw [map_mul, map_prod, map_prod] at h
      simp_rw [map_pow, ← LSeries_conj] at h
      have hc : ∀ i, starRingEnd ℂ (ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i))
          (starRingEnd ℂ s)) = ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i))⁻¹ s :=
        fun i => ((hval i s hs).2.2.2.2).symm
      simp_rw [hc] at h
      exact h

    have hPpow : ∀ (m : Fin k → ℕ), ∏ i, (if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1
        then s * (s - 1) else (1 : ℂ)) ^ m i =
        (s * (s - 1)) ^ ∑ i, m i * (if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1 then 1 else 0) := by
      intro m
      rw [← prod_pow_eq_pow_sum]
      exact prod_congr rfl fun i _ => by split_ifs <;> simp

    have hΛa0 : ∀ i, Λa i s ≠ 0 ∧ Λb i s ≠ 0 := by
      intro i
      have hEne : ((((|(discr (IntermediateField.fixedField (H i)) : ℝ)| *
          (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i))) : ℝ) :
            ℝ) : ℂ) ^ (s / 2))) ≠ 0 := by
        intro h
        exact (hDpos i).ne' (Complex.ofReal_eq_zero.1 ((Complex.cpow_eq_zero_iff _ _).1 h).1)
      have hPne : (if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1 then s * (s - 1) else (1 : ℂ)) ≠ 0 := by
        split_ifs
        · exact hS
        · exact one_ne_zero
      have hpre := mul_ne_zero (mul_ne_zero (mul_ne_zero hEne (pow_ne_zero
        (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup (H i) (χ i))) hA0))
        (pow_ne_zero (ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup (H i) (χ i))) hB0))
        (pow_ne_zero (nrComplexPlaces (IntermediateField.fixedField (H i))) (mul_ne_zero hA0 hB0))
      constructor
      · rw [(hval i s hs).1]
        exact mul_ne_zero hPne (mul_ne_zero hpre (hval i s hs).2.2.1)
      · rw [(hval i s hs).2.1]
        exact mul_ne_zero hPne (mul_ne_zero hpre (hval i s hs).2.2.2.1)

    have hkey := key a (fun i => Λa i s)
      (fun i => if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1 then s * (s - 1) else (1 : ℂ))
      (fun i => (((|(discr (IntermediateField.fixedField (H i)) : ℝ)| *
          (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i))) : ℝ) :
            ℝ) : ℂ) ^ (s / 2)))
      (fun i => ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i)) s)
      (fun i => ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup (H i) (χ i)))
      (fun i => ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup (H i) (χ i)))
      (fun i => nrComplexPlaces (IntermediateField.fixedField (H i)))
      (Gammaℝ s) (Gammaℝ (s + 1)) ((s * (s - 1)) ^ m₁) ((s * (s - 1)) ^ m₂)
      ((((ArtinL.conductor ρ : ℕ) : ℝ) : ℂ) ^ (s / 2)) (_root_.LSeries (ArtinL.coeff ρ) s)
      (fun i => (hval i s hs).1) (hPpow _) (hPpow _) hE hp hq hL
    have hkey' := key a (fun i => Λb i s)
      (fun i => if ArtinL.Abelian.ofSubgroup (H i) (χ i) = 1 then s * (s - 1) else (1 : ℂ))
      (fun i => (((|(discr (IntermediateField.fixedField (H i)) : ℝ)| *
          (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup (H i) (χ i))) : ℝ) :
            ℝ) : ℂ) ^ (s / 2)))
      (fun i => ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup (H i) (χ i))⁻¹ s)
      (fun i => ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup (H i) (χ i)))
      (fun i => ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup (H i) (χ i)))
      (fun i => nrComplexPlaces (IntermediateField.fixedField (H i)))
      (Gammaℝ s) (Gammaℝ (s + 1)) ((s * (s - 1)) ^ m₁) ((s * (s - 1)) ^ m₂)
      ((((ArtinL.conductor ρ : ℕ) : ℝ) : ℂ) ^ (s / 2))
      (_root_.LSeries (fun m => starRingEnd ℂ (ArtinL.coeff ρ m)) s)
      (fun i => (hval i s hs).2.1) (hPpow _) (hPpow _) hE hp hq hL'
    have hγ : (((ArtinL.conductor ρ : ℕ) : ℝ) : ℂ) ^ (s / 2) * Gammaℝ s * Gammaℝ (s + 1) =
        2 * ((((Real.sqrt (ArtinL.conductor ρ) / (2 * Real.pi) : ℝ)) : ℂ) ^ s * Complex.Gamma s) := by
      rw [mul_assoc]; exact sqrt_gamma _ s
    refine ⟨ArtinL.LSeriesSummable_coeff_of_one_lt_re ρ hρ hs, ?_, ?_, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hS))
        (prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hΛa0 i).1)
    · exact mul_ne_zero hWneg0 (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hS))
        (prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hΛa0 i).2))
    · beta_reduce at hkey ⊢
      rw [hkey, hγ]; ring
    · beta_reduce at hkey' ⊢
      rw [hkey', hγ]; ring

  · intro s
    have h1 : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
    simp only [h1, hFE, mul_pow, prod_mul_distrib]
    rw [← hWpos]
    field_simp
  · intro s
    have h1 : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
    simp only [h1, hFE, mul_pow, prod_mul_distrib]
    rw [← hWneg]
    ring

end Main

end ArtinFEAssembly

end

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem solution
    (ρ : Γℚ →* GL (Fin 2) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (hodd : ((ρ complexConjugation : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = -1) :
    ∃ (W : ℂ) (Λ₁ Λ₂ Λ₁' Λ₂' : ℂ → ℂ), W ≠ 0 ∧
      Differentiable ℂ Λ₁ ∧ Differentiable ℂ Λ₂ ∧ Differentiable ℂ Λ₁' ∧ Differentiable ℂ Λ₂' ∧
      (∀ s : ℂ, 1 < s.re →
        LSeriesSummable (ArtinL.coeff ρ) s ∧ Λ₂ s ≠ 0 ∧ Λ₂' s ≠ 0 ∧
        Λ₁ s = Λ₂ s *
          (((Real.sqrt (ArtinL.conductor ρ) / (2 * Real.pi) : ℝ) : ℂ) ^ s * Complex.Gamma s *
            _root_.LSeries (ArtinL.coeff ρ) s) ∧
        Λ₁' s = Λ₂' s *
          (((Real.sqrt (ArtinL.conductor ρ) / (2 * Real.pi) : ℝ) : ℂ) ^ s * Complex.Gamma s *
            _root_.LSeries (fun m => starRingEnd ℂ (ArtinL.coeff ρ m)) s)) ∧
      (∀ s : ℂ, Λ₁ (1 - s) = W * Λ₁' s) ∧
      (∀ s : ℂ, Λ₂ (1 - s) = Λ₂' s) :=
  ArtinFEAssembly.main ρ hρ hodd

end S_ArtinL_exists_completedLSeries_functionalEquation_of_odd
end P2MW
export P2MW.S_ArtinL_exists_completedLSeries_functionalEquation_of_odd (solution)
