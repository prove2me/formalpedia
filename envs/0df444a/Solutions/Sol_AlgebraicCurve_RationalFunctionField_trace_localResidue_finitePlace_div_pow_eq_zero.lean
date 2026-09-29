-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e51816cb-e025-5114-bf07-801caf2ac1b7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Theorems.Thm_AlgebraicCurve_residueTraceCompletionCommute_v2
import Theorems.Thm_AlgebraicCurve_completionTraceSum_of_isSeparable
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import Theorems.Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_X
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_exists_ord_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum placeOfPoint deg_placeOfPoint placeInfty placeInfty_toValuationSubring hasPrincipalDivisors ord_placeOfPoint_algebraMap eq_ofHeightOneSpectrum_or_eq_placeInfty ord_placeInfty deg_placeInfty placeInfty_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum finite_setOf_ord_ne_zero ord_placeInfty_X ord_ofHeightOneSpectrum_eq_neg_log ord_ofHeightOneSpectrum_of_span ord_placeInfty_algebraMap degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve.RationalFunctionField AlgebraicCurve"

scoped instance instIsCurveOver (K : Type*) [Field K] : IsCurveOver K (RatFunc K) :=
  AlgebraicCurve.instIsCurveOverRatFunc K

scoped instance instHasPrincipalDivisors (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  hasPrincipalDivisors K

end AlgebraicCurve.RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000
namespace Algebra
p2m_export "Algebra" "algebraMap_eq_smul_one trace_eq_of_algEquiv trace adjoin.powerBasis_dim mk algebraMap adjoin.powerBasis_gen mem_top eq_top_iff adjoin.powerBasis IsIntegral.of_finite smul_def adjoin mem_bot IsSeparable.of_algHom"
p2m_open "Algebra"
end Algebra
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace IntermediateField
p2m_export "IntermediateField" "toAlgebra mk adjoin.powerBasis_gen algebra_adjoin_le_adjoin adjoin.powerBasis_dim minpoly_gen ext isSeparable_adjoin_simple_iff_isSeparable equivOfEq algebraMap_apply adjoin.finiteDimensional smul_def adjoin.finrank adjoin mk.injEq topEquiv mem_top adjoin.powerBasis mem_bot restrict map"
p2m_open "IntermediateField"
end IntermediateField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace IsLocalRing
p2m_export "IsLocalRing" "ResidueField residue"
p2m_open "IsLocalRing"
end IsLocalRing
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace KaehlerDifferential
p2m_export "KaehlerDifferential" "finite D span_range_derivation map_D map"
p2m_open "KaehlerDifferential"
end KaehlerDifferential
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace Module
p2m_export "Module" "Finite.of_basis finrank mk Basis.traceDual_powerBasis_eq Basis"
p2m_open "Module"
end Module
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace Polynomial
p2m_export "Polynomial" "C C_comp comp_eq_aeval X coeff_natDegree comp_eq_zero_iff natDegree_comp coeff_map derivative_C aeval_map_algebraMap derivative_map aeval_def natDegree_mul C_eq_algebraMap mul_comp leadingCoeff eval₂_eq_sum_range' coeff algebraMap_eq aeval_X_left_apply natDegree_sub_eq_left_of_natDegree_lt unique aeval coeff_C_zero rootMultiplicity_X_sub_C degree aeval_C degree_sub_le coeff_sub degree_derivative_lt map degree_C degree_ne_bot Monic comp algebra exists_eq_pow_rootMultiplicity_mul_and_not_dvd natDegree_pow pow_comp X_dvd_iff sum X_comp derivative_mul Separable leadingCoeff_C natDegree aeval_mem_adjoin_singleton eq_of_monic_of_dvd_of_natDegree_le transcendental_X flt X_ne_zero rootMultiplicity degree_mul_le natDegree_lt_natDegree leadingCoeff_mul derivative_sub coeff_zero_eq_eval_zero natDegree_map derivative degree_sub_lt aeval_X_left isUnit_C dvd_iff_isRoot algebraMap_apply natDegree_eq_zero_of_isUnit degree_map natDegree_C map_ne_zero isCoprime_iff_aeval_ne_zero_of_isAlgClosed ext degree_eq_natDegree sub_comp isUnit_iff ring aeval_algHom_apply transcendental degree_mul aeval_algebraMap_apply leadingCoeff_ne_zero eval aeval_eq_sum_range'"
p2m_open "Polynomial"
end Polynomial
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace RationalFunctionField
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
namespace WithZero
p2m_export "WithZero" "log_le_log map log exp one le exp_le_exp exp_log exp_injective"
p2m_open "WithZero"
end WithZero
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module Algebra P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Algebra"
namespace FLT
namespace EulerDualBasis
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in

theorem coeff_minpolyDiv_dim_sub_one (pb : PowerBasis K L) :
    (minpolyDiv K pb.gen).coeff (pb.dim - 1) = 1 := by
  have h1 : (minpolyDiv K pb.gen).natDegree = pb.dim - 1 := by
    rw [natDegree_minpolyDiv, pb.natDegree_minpoly]
  rw [← h1]
  exact (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree

theorem traceDual_eq_one_div_of_val_eq (pb : PowerBasis K L) {j : Fin pb.dim}
    (hj : (j : ℕ) = pb.dim - 1) :
    pb.basis.traceDual j = 1 / aeval pb.gen (derivative (minpoly K pb.gen)) := by
  rw [Module.Basis.traceDual_powerBasis_eq]
  rw [hj, coeff_minpolyDiv_dim_sub_one]

theorem trace_pow_div_aeval_derivative_minpoly_of_lt (pb : PowerBasis K L) {k : ℕ}
    (hk : k < pb.dim - 1) :
    Algebra.trace K L
      (pb.gen ^ k / aeval pb.gen (derivative (minpoly K pb.gen))) = 0 := by
  have hd : 0 < pb.dim := by omega
  have hk' : k < pb.dim := by omega
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨k, hk'⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, if_neg]
  simp only [Fin.mk.injEq]
  omega

theorem trace_pow_div_aeval_derivative_minpoly_self (pb : PowerBasis K L)
    (hd : 0 < pb.dim) :
    Algebra.trace K L
      (pb.gen ^ (pb.dim - 1) / aeval pb.gen (derivative (minpoly K pb.gen))) = 1 := by
  have hlt : pb.dim - 1 < pb.dim := by omega
  have key := pb.basis.trace_mul_traceDual ⟨pb.dim - 1, hlt⟩ ⟨pb.dim - 1, hlt⟩
  rw [traceDual_eq_one_div_of_val_eq pb rfl, pb.basis_eq_pow, mul_one_div] at key
  rw [key, if_pos rfl]

end FLT.EulerDualBasis
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing IntermediateField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IntermediateField"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum mk.injEq toValuationSubring mk ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_of_mem differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict mem_restrict_iff ord_restrict fiber mem_fiber adicCompletion adicCompletionIntegers finiteResidue_of_deg_pos CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap ord_algebraMap ord_eq_neg_log_of_valuationSubring_eq ord_neg ord_nonneg_of_mem mem_of_ord_nonneg mem_iff_ord_nonneg exists_ord_pos"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero AlgebraicCurve"
section Ultrametric
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.AlgebraicCurve.Place.ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by

  have hfv := v.adicValuation_ne_zero hf
  have hgv := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← exp_log hfv, ← exp_log hgv]
    have hlog : log (v.adicValuation g) < log (v.adicValuation f) := by
      simp only [ord] at h
      omega
    exact lt_of_le_of_ne (exp_le_exp.mpr hlog.le)
      fun hcon => hlog.ne (exp_injective hcon)
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ (ne_of_lt hlt).symm
  rw [max_eq_left hlt.le] at h1
  simp only [ord, h1]

p2m_export "AlgebraicCurve.Place" "ord_add_eq_left"
end Ultrametric
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum placeOfPoint deg_placeOfPoint placeInfty placeInfty_toValuationSubring hasPrincipalDivisors ord_placeOfPoint_algebraMap eq_ofHeightOneSpectrum_or_eq_placeInfty ord_placeInfty deg_placeInfty placeInfty_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum finite_setOf_ord_ne_zero ord_placeInfty_X ord_ofHeightOneSpectrum_eq_neg_log ord_ofHeightOneSpectrum_of_span ord_placeInfty_algebraMap degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
theorem ord_finitePlace_ne_zero_iff {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) q) ≠ 0 ↔ p ∣ q := by
  rw [finitePlace, Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) _ hq,
    heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]

variable {K}
section DegInfty
variable (K) [DecidableEq (RatFunc K)]
theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩

  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, _root_.map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]

  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt

end DegInfty
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum placeOfPoint deg_placeOfPoint placeInfty placeInfty_toValuationSubring hasPrincipalDivisors ord_placeOfPoint_algebraMap eq_ofHeightOneSpectrum_or_eq_placeInfty ord_placeInfty deg_placeInfty placeInfty_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum finite_setOf_ord_ne_zero ord_placeInfty_X ord_ofHeightOneSpectrum_eq_neg_log ord_ofHeightOneSpectrum_of_span ord_placeInfty_algebraMap degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
scoped instance instFiniteResidueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).FiniteResidue := by
  obtain ⟨p, hp, hw⟩ := exists_irreducible_span K w
  refine Place.finiteResidue_of_deg_pos _ ?_
  rw [deg_ofHeightOneSpectrum K hw]
  exact hp.natDegree_pos

scoped instance instFiniteResiduePlaceInfty [DecidableEq (RatFunc K)] :
    (placeInfty K).FiniteResidue :=
  Place.finiteResidue_of_deg_pos _ (by rw [deg_placeInfty K]; exact one_pos)

variable {K} in

scoped instance instFiniteResidue (v : Place K (RatFunc K)) : v.FiniteResidue := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact instFiniteResidueOfHeightOneSpectrum K w
  · exact instFiniteResiduePlaceInfty K

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [HasPrincipalDivisors K F]
section P1PrincipalPartSubrows
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
variable (K)
variable [DecidableEq (RatFunc K)]
variable [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
variable [HasPrincipalDivisors K (RatFunc K)]
variable {K}
omit [HasCanonicalLocalResidueKStar K (RatFunc K)] [HasCanonicalDivisor (K := K) (F := RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
  [HasPrincipalDivisors K (RatFunc K)] in

theorem finitePlace_ne_placeInfty {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp ≠ placeInfty K :=
  fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

end P1PrincipalPartSubrows
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum placeOfPoint deg_placeOfPoint placeInfty placeInfty_toValuationSubring hasPrincipalDivisors ord_placeOfPoint_algebraMap eq_ofHeightOneSpectrum_or_eq_placeInfty ord_placeInfty deg_placeInfty placeInfty_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum finite_setOf_ord_ne_zero ord_placeInfty_X ord_ofHeightOneSpectrum_eq_neg_log ord_ofHeightOneSpectrum_of_span ord_placeInfty_algebraMap degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
theorem exists_ord_finitePlace_eq_nsmul {p : K[X]} (hp : Irreducible p) {q : K[X]}
    (hq : q ≠ 0) :
    ∃ m : ℕ, (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) q)
      = m * (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨m, b, hb, rfl⟩ := WfDvdMonoid.max_power_factor hq hp
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hq (mul_zero _)
  have hordb : (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) b) = 0 := by
    by_contra hcon
    exact hb ((ord_finitePlace_ne_zero_iff K hp hb0).mp hcon)
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow,
    (finitePlace K hp).ord_mul (pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hp0))
      ((map_ne_zero_iff _ hinj).mpr hb0),
    hordb, add_zero, ← zpow_natCast, (finitePlace K hp).ord_zpow]

theorem ord_finitePlace_dvd {p : K[X]} (hp : Irreducible p) {f : RatFunc K} (hf : f ≠ 0) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) ∣ (finitePlace K hp).ord f := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  obtain ⟨a, ha⟩ := exists_ord_finitePlace_eq_nsmul K hp (RatFunc.num_ne_zero hf)
  obtain ⟨b, hb⟩ := exists_ord_finitePlace_eq_nsmul K hp f.denom_ne_zero
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (finitePlace K hp).ord_mul hnum' (inv_ne_zero hden'), (finitePlace K hp).ord_inv, ha, hb]
  exact ⟨(a : ℤ) - b, by ring⟩

theorem ord_finitePlace_self {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) = 1 := by

  have hnonneg : 0 ≤ (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) :=
    (finitePlace K hp).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K _ p)

  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (finitePlace K hp).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) p) ∣ 1 :=
    (finitePlace K hp).ord_coe_irreducible hπ ▸ ord_finitePlace_dvd K hp hπ0
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
theorem ord_placeInfty_X_inv : (placeInfty K).ord (RatFunc.X : RatFunc K)⁻¹ = 1 := by
  rw [(placeInfty K).ord_inv, ord_placeInfty_X, neg_neg]

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
abbrev dX : Ω[(RatFunc K)⁄K] := KaehlerDifferential.D K (RatFunc K) RatFunc.X

theorem aeval_ratFuncX_eq_algebraMap (q : K[X]) :
    aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X,
    show algebraMap K[X] (RatFunc K) X = IsScalarTower.toAlgHom K K[X] (RatFunc K) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem D_algebraMap_polynomial (q : K[X]) :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) q.derivative • dX K := by
  rw [← aeval_ratFuncX_eq_algebraMap K q, (D K (RatFunc K)).map_aeval q RatFunc.X,
    aeval_ratFuncX_eq_algebraMap K q.derivative]

theorem denom_sq_smul_D_eq (f : RatFunc K) :
    (algebraMap K[X] (RatFunc K) f.denom) ^ 2 • KaehlerDifferential.D K (RatFunc K) f
      = algebraMap K[X] (RatFunc K)
          (f.num.derivative * f.denom - f.num * f.denom.derivative) • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero
  have hDf : KaehlerDifferential.D K (RatFunc K) f
      = ((algebraMap K[X] (RatFunc K) f.denom)⁻¹ ^ 2) •
        (algebraMap K[X] (RatFunc K) f.denom • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.num)
          - algebraMap K[X] (RatFunc K) f.num
              • D K (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom)) := by
    conv_lhs => rw [← f.num_div_denom, (D K (RatFunc K)).leibniz_div]
  rw [hDf, smul_smul, ← mul_pow, mul_inv_cancel₀ hd, one_pow, one_smul,
    D_algebraMap_polynomial K f.num, D_algebraMap_polynomial K f.denom,
    smul_smul, smul_smul, ← sub_smul]
  push_cast
  ring_nf

theorem span_dX_eq_top :
    Submodule.span (RatFunc K) {dX K} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr f.denom_ne_zero

  have hsq : ((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
        * (algebraMap K[X] (RatFunc K) f.denom) ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hd)
  refine Submodule.mem_span_singleton.mpr ⟨((algebraMap K[X] (RatFunc K) f.denom) ^ 2)⁻¹
    * algebraMap K[X] (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative), ?_⟩
  rw [mul_smul, ← denom_sq_smul_D_eq K f, smul_smul, hsq, one_smul]

theorem dX_ne_zero [Nontrivial Ω[(RatFunc K)⁄K]] : dX K ≠ 0 := by
  intro h0
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  have hω_mem : ω ∈ Submodule.span (RatFunc K) {dX K} :=
    span_dX_eq_top K ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hω_mem
  exact hω hω_mem

theorem not_dvd_derivative_of_sq_not_dvd {p : K[X]} (hp : Irreducible p) (hsep : p.Separable)
    {q : K[X]} (hpq : p ∣ q) (hpq2 : ¬ p ^ 2 ∣ q) : ¬ p ∣ q.derivative := by
  obtain ⟨m, rfl⟩ := hpq
  have hpm : ¬ p ∣ m := fun ⟨r, hr⟩ => hpq2 ⟨r, by rw [hr]; ring⟩
  intro hpdvd
  rw [derivative_mul] at hpdvd
  have hpdvd' : p ∣ p.derivative * m := by
    have := dvd_sub hpdvd (dvd_mul_right p m.derivative)
    rwa [add_sub_cancel_right] at this
  rcases hp.prime.dvd_mul.mp hpdvd' with hpp' | hpm'
  ·
    exact hp.not_isUnit (hsep.isUnit_of_dvd' dvd_rfl hpp')
  · exact hpm hpm'

variable {K}
theorem not_dvd_derivative_of_ord_eq_one {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {q : K[X]} (hq : q ≠ 0)
    (hord : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 1) :
    ¬ p ∣ q.derivative := by
  have hwmem : ∀ {r : K[X]}, r ≠ 0 →
      ((Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) ≠ 0 ↔ p ∣ r) := fun {r} hr => by
    rw [Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hr,
      hwp, Ideal.mem_span_singleton]
  have hordp : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 :=
    ord_ofHeightOneSpectrum_of_span w hp.ne_zero hwp
  refine not_dvd_derivative_of_sq_not_dvd K hp hsep
    ((hwmem hq).mp (hord ▸ one_ne_zero)) ?_

  rintro ⟨r, rfl⟩
  have hr : r ≠ 0 := fun h => hq (by simp [h])
  have : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) (p ^ 2 * r)) ≥ 2 := by
    have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp.ne_zero
    have hr0 : algebraMap K[X] (RatFunc K) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hr
    rw [map_mul, map_pow,
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_mul (pow_ne_zero 2 hp0) hr0,
      ← zpow_natCast, (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_zpow,
      hordp, mul_one]
    have : 0 ≤ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
        (algebraMap K[X] (RatFunc K) r) :=
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord_nonneg_of_mem
        (algebraMap_mem_ofHeightOneSpectrum K w r)
    omega
  omega

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
section SurjectivePlaceInfty
variable (K) [DecidableEq (RatFunc K)]
theorem surjective_algebraMap_residueField_placeInfty :
    Function.Surjective (algebraMap K (placeInfty K).ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : (placeInfty K).ResidueField) one_ne_zero).mp
      (show Module.finrank K (placeInfty K).ResidueField = 1 from deg_placeInfty K) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end SurjectivePlaceInfty
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section WronskianBound
variable {K : Type*} [Field K]
theorem natDegree_numDenomWronskian_lt {n d : K[X]} (hn : n ≠ 0) (hd : d ≠ 0)
    (hW : n.derivative * d - n * d.derivative ≠ 0) :
    (n.derivative * d - n * d.derivative).natDegree < n.natDegree + d.natDegree := by
  have hdeg : (n.derivative * d - n * d.derivative).degree < (n * d).degree := by
    rw [Polynomial.degree_mul]
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_right (Polynomial.degree_ne_bot.mpr hd)]
      exact Polynomial.degree_derivative_lt hn
    · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      rw [WithBot.add_lt_add_iff_left (Polynomial.degree_ne_bot.mpr hn)]
      exact Polynomial.degree_derivative_lt hd
  have h2 := Polynomial.natDegree_lt_natDegree hW hdeg
  rwa [Polynomial.natDegree_mul hn hd] at h2

end WronskianBound
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section DXCoeff
variable (K : Type*) [Field K]
def ratFuncDXCoeff (f : RatFunc K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
    / (algebraMap K[X] (RatFunc K) f.denom) ^ 2

theorem ratFuncDXCoeff_def (f : RatFunc K) :
    ratFuncDXCoeff K f
      = algebraMap K[X] (RatFunc K) (f.num.derivative * f.denom - f.num * f.denom.derivative)
        / (algebraMap K[X] (RatFunc K) f.denom) ^ 2 := rfl

theorem D_eq_ratFuncDXCoeff_smul_dX (f : RatFunc K) :
    KaehlerDifferential.D K (RatFunc K) f = ratFuncDXCoeff K f • dX K := by
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [ratFuncDXCoeff_def, div_eq_mul_inv, mul_comm, mul_smul, ← denom_sq_smul_D_eq K f,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hd), one_smul]

theorem wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero {f : RatFunc K}
    (h : ratFuncDXCoeff K f ≠ 0) :
    f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
  intro h0
  exact h (by rw [ratFuncDXCoeff_def, h0, _root_.map_zero, zero_div])

end DXCoeff
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section FinitePlaces
variable {K : Type*} [Field K]
variable {w : HeightOneSpectrum K[X]}
local notation "v" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w
theorem ord_algebraMap_denom_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne

  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (v).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (v).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((v).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)

  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, hordn] at hord
  omega

theorem ord_algebraMap_num_eq_one_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : (v).ord f = 1) :
    (v).ord (algebraMap K[X] (RatFunc K) f.num) = 1 := by
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have h := hord
  rw [← f.num_div_denom, div_eq_mul_inv, (v).ord_mul hnum0 (inv_ne_zero hden0),
    (v).ord_inv, ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord] at h
  omega

theorem not_dvd_wronskian_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) := by
  have hpn' : ¬ p ∣ f.num.derivative :=
    not_dvd_derivative_of_ord_eq_one hp hwp hsep (RatFunc.num_ne_zero hf)
      (ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord)
  have hpd : ¬ p ∣ f.denom := fun hpd => by
    have h0 := ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord
    rw [← Ideal.mem_span_singleton, ← hwp] at hpd
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mpr hpd h0
  have hpn : p ∣ f.num := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      (RatFunc.num_ne_zero hf)).mp ?_
    rw [ord_algebraMap_num_eq_one_of_ord_eq_one hp hwp hf hord]
    exact one_ne_zero
  intro hdvd

  have hpnd' : p ∣ f.num * f.denom.derivative := hpn.mul_right _
  have hpn'd : p ∣ f.num.derivative * f.denom := by
    have h1 := dvd_add hdvd hpnd'
    rwa [sub_add_cancel] at h1
  rcases hp.prime.dvd_mul.mp hpn'd with h | h
  · exact hpn' h
  · exact hpd h

theorem ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) (hsep : p.Separable)
    {f : RatFunc K} (hf : f ≠ 0) (hord : (v).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (v).ord (ratFuncDXCoeff K f) = 0 := by
  have hW : ¬ p ∣ (f.num.derivative * f.denom - f.num * f.denom.derivative) :=
    not_dvd_wronskian_of_ord_eq_one hp hwp hsep hf hord
  have hξ0 : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := fun h =>
    hW (h ▸ dvd_zero p)
  have hd0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hξ0' : algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hξ0

  have hordξ : (v).ord (algebraMap K[X] (RatFunc K)
      (f.num.derivative * f.denom - f.num * f.denom.derivative)) = 0 := by
    by_contra h
    refine hW ?_
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hξ0).mp h
  refine ⟨div_ne_zero hξ0' (pow_ne_zero 2 hd0), ?_⟩
  rw [ratFuncDXCoeff_def, div_eq_mul_inv,
    (v).ord_mul hξ0' (inv_ne_zero (pow_ne_zero 2 hd0)), (v).ord_inv, hordξ,
    ← zpow_natCast, (v).ord_zpow,
    ord_algebraMap_denom_eq_zero_of_ord_eq_one hp hwp hf hord]
  ring

end FinitePlaces
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section PlaceInftySide
variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
theorem ord_placeInfty_ratFuncDXCoeff_ge {g : RatFunc K} (hg : g ≠ 0)
    (hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0) :
    (placeInfty K).ord g + 1 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  have hn0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hd0 : g.denom ≠ 0 := g.denom_ne_zero
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0

  have hdeg : (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree
      < g.num.natDegree + g.denom.natDegree :=
    natDegree_numDenomWronskian_lt hn0 hd0 hW

  have hcoeff : (placeInfty K).ord (ratFuncDXCoeff K g)
      = 2 * (g.denom.natDegree : ℤ)
        - (g.num.derivative * g.denom - g.num * g.denom.derivative).natDegree := by
    rw [ratFuncDXCoeff_def, ord_placeInfty (div_ne_zero hW' (pow_ne_zero 2 hd')),
      RatFunc.intDegree_div hW' (pow_ne_zero 2 hd'), RatFunc.intDegree_polynomial,
      ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_pow]
    push_cast
    ring

  have hgord : (placeInfty K).ord g = (g.denom.natDegree : ℤ) - g.num.natDegree := by
    rw [ord_placeInfty hg, RatFunc.intDegree]
    ring
  rw [hcoeff, hgord]
  omega

theorem exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero {g : RatFunc K}
    (hg : g ≠ 0) (hord : (placeInfty K).ord g = 0) :
    ∃ e : RatFunc K, (e = 0 ∨ 2 ≤ (placeInfty K).ord e) ∧
      KaehlerDifferential.D K (RatFunc K) g = e • dX K := by

  have hmem : RatFunc.inftyValuation K g ≤ 1 := by
    have h1 : g ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hg hord.symm.le
    rwa [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at h1

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K hmem

  have hDg : KaehlerDifferential.D K (RatFunc K) g
      = KaehlerDifferential.D K (RatFunc K) (g - algebraMap K (RatFunc K) c) := by
    rw [map_sub, Derivation.map_algebraMap (KaehlerDifferential.D K (RatFunc K)) c, sub_zero]
  rcases hc with hc0 | hcneg
  ·
    exact ⟨0, Or.inl rfl, by rw [hDg, hc0, _root_.map_zero, zero_smul]⟩
  ·
    have hg₁0 : g - algebraMap K (RatFunc K) c ≠ 0 := by
      intro h0
      rw [h0] at hcneg
      simp at hcneg
    refine ⟨ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c), ?_,
      by rw [hDg, D_eq_ratFuncDXCoeff_smul_dX]⟩
    rcases eq_or_ne (ratFuncDXCoeff K (g - algebraMap K (RatFunc K) c)) 0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hW := wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K h0
      have hge := ord_placeInfty_ratFuncDXCoeff_ge hg₁0 hW
      have hord₁ : 1 ≤ (placeInfty K).ord (g - algebraMap K (RatFunc K) c) := by
        rw [ord_placeInfty hg₁0]
        omega
      omega

theorem exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one {h : RatFunc K}
    (hh : h ≠ 0) (hord : (placeInfty K).ord h = -1) :
    ∃ b : RatFunc K, b ≠ 0 ∧ (placeInfty K).ord b = 0 ∧
      KaehlerDifferential.D K (RatFunc K) h = b • dX K := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hXinv : (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := inv_ne_zero hX

  have hg0 : h * (RatFunc.X : RatFunc K)⁻¹ ≠ 0 := mul_ne_zero hh hXinv
  have hordg : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹) = 0 := by
    rw [(placeInfty K).ord_mul hh hXinv, (placeInfty K).ord_inv, ord_placeInfty_X, hord]
    ring
  obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg0 hordg

  have hh_eq : h = h * (RatFunc.X : RatFunc K)⁻¹ * RatFunc.X := by
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  have hDh : KaehlerDifferential.D K (RatFunc K) h
      = (h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e) • dX K := by
    conv_lhs => rw [hh_eq]
    rw [Derivation.leibniz, hDe, smul_smul,
      show KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) = dX K from rfl,
      ← add_smul]
  rcases he with rfl | he2
  ·
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * 0, ?_, ?_, hDh⟩
    · rw [mul_zero, add_zero]
      exact hg0
    · rw [mul_zero, add_zero]
      exact hordg
  ·
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, (placeInfty K).ord_zero] at he2
      omega
    have hXe0 : (RatFunc.X : RatFunc K) * e ≠ 0 := mul_ne_zero hX he0
    have hlt : (placeInfty K).ord (h * (RatFunc.X : RatFunc K)⁻¹)
        < (placeInfty K).ord ((RatFunc.X : RatFunc K) * e) := by
      rw [hordg, (placeInfty K).ord_mul hX he0, ord_placeInfty_X]
      omega
    refine ⟨h * (RatFunc.X : RatFunc K)⁻¹ + RatFunc.X * e, ?_, ?_, hDh⟩
    ·
      intro hsum
      have hXe_eq : (RatFunc.X : RatFunc K) * e = -(h * (RatFunc.X : RatFunc K)⁻¹) := by
        linear_combination hsum
      rw [hXe_eq, (placeInfty K).ord_neg] at hlt
      exact lt_irrefl _ hlt
    · rw [(placeInfty K).ord_add_eq_left hg0 hXe0 hlt]
      exact hordg

theorem exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one {f : RatFunc K}
    (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ∃ e : RatFunc K, e ≠ 0 ∧ (placeInfty K).ord e = 2 ∧
      KaehlerDifferential.D K (RatFunc K) f = e • dX K := by

  have hf' : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hord' : (placeInfty K).ord f⁻¹ = -1 := by
    rw [(placeInfty K).ord_inv, hord]
  obtain ⟨b, hb0, hbord, hDb⟩ := exists_unit_dXCoeff_of_ord_placeInfty_eq_neg_one hf' hord'
  refine ⟨-(f ^ 2 * b), neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hf) hb0), ?_, ?_⟩
  · rw [(placeInfty K).ord_neg, (placeInfty K).ord_mul (pow_ne_zero 2 hf) hb0, hbord,
      add_zero, ← zpow_natCast, (placeInfty K).ord_zpow, hord]
    norm_num
  ·
    conv_lhs => rw [← inv_inv f]
    rw [(KaehlerDifferential.D K (RatFunc K)).leibniz_inv f⁻¹, hDb, inv_inv, smul_smul,
      neg_mul]

end PlaceInftySide
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
set_option linter.unusedSectionVars false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
section AlgEquiv
variable {p : K[X]} (hpirr : Irreducible p)
def finitePlaceResidueFieldAlgEquivAdjoinRoot :
    AdjoinRoot p ≃ₐ[K] (finitePlace K hpirr).ResidueField :=
  residueFieldEquivOfHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hpirr)

theorem finitePlaceResidueFieldAlgEquivAdjoinRoot_mk (q : K[X]) :
    finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr (AdjoinRoot.mk p q)
      = IsLocalRing.residue _ ⟨algebraMap K[X] (RatFunc K) q,
          algebraMap_mem_ofHeightOneSpectrum K _ q⟩ :=
  rfl

end AlgEquiv
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section TraceTransport
variable {p : K[X]} (hpirr : Irreducible p)
theorem trace_finitePlace_residueField_eq_trace_adjoinRoot
    (y : (finitePlace K hpirr).ResidueField) :
    Algebra.trace K (finitePlace K hpirr).ResidueField y
      = Algebra.trace K (AdjoinRoot p)
          ((finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).symm y) := by
  conv_lhs => rw [← (finitePlaceResidueFieldAlgEquivAdjoinRoot K hpirr).apply_symm_apply y]
  exact Algebra.trace_eq_of_algEquiv _ _

end TraceTransport
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
set_option linter.unusedSectionVars false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section DXCoeffIntegrality
variable {K : Type*} [Field K]
theorem ratFuncDXCoeff_eq_of_D_eq_smul_dX {f e : RatFunc K}
    (h : KaehlerDifferential.D K (RatFunc K) f = e • dX K) : ratFuncDXCoeff K f = e := by
  have key : (ratFuncDXCoeff K f - e) • dX K = 0 := by
    rw [sub_smul, ← D_eq_ratFuncDXCoeff_smul_dX K f, h, sub_self]
  rcases smul_eq_zero.mp key with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (dX_ne_zero K)

theorem ratFuncDXCoeff_zero : ratFuncDXCoeff K (0 : RatFunc K) = 0 :=
  ratFuncDXCoeff_eq_of_D_eq_smul_dX (by rw [_root_.map_zero, zero_smul])

section FinitePlaces
variable {w : HeightOneSpectrum K[X]}
local notation "vw" => Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w
theorem ord_algebraMap_denom_eq_zero_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) (hord : 0 ≤ (vw).ord f) :
    (vw).ord (algebraMap K[X] (RatFunc K) f.denom) = 0 := by
  by_contra hne
  have hpd : p ∣ f.denom := by
    rw [← Ideal.mem_span_singleton, ← hwp]
    exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
      f.denom_ne_zero).mp hne
  have hpn : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit (f.isCoprime_num_denom.isUnit_of_dvd' hpn hpd)
  have hordn : (vw).ord (algebraMap K[X] (RatFunc K) f.num) = 0 := by
    by_contra h
    exact hpn (by
      rw [← Ideal.mem_span_singleton, ← hwp]
      exact (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w
        (RatFunc.num_ne_zero hf)).mp h)
  have hordd : 0 < (vw).ord (algebraMap K[X] (RatFunc K) f.denom) :=
    lt_of_le_of_ne ((vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _))
      (Ne.symm hne)
  have hnum0 : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hden0 : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero f.denom_ne_zero
  rw [← f.num_div_denom, div_eq_mul_inv, (vw).ord_mul hnum0 (inv_ne_zero hden0),
    (vw).ord_inv, hordn] at hord
  omega

theorem ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg {p : K[X]}
    (hp : Irreducible p) (hwp : w.asIdeal = Ideal.span {p}) {g : RatFunc K}
    (hg : g ≠ 0) (hord : 0 ≤ (vw).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 0 ≤ (vw).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
    wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
  have hW' : algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hW
  have hd' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero g.denom_ne_zero
  have hWord : 0 ≤ (vw).ord (algebraMap K[X] (RatFunc K)
      (g.num.derivative * g.denom - g.num * g.denom.derivative)) :=
    (vw).ord_nonneg_of_mem (algebraMap_mem_ofHeightOneSpectrum K w _)
  have hden : (vw).ord (algebraMap K[X] (RatFunc K) g.denom) = 0 :=
    ord_algebraMap_denom_eq_zero_of_ord_nonneg hp hwp hg hord
  have key : (vw).ord (ratFuncDXCoeff K g)
      = (vw).ord (algebraMap K[X] (RatFunc K)
          (g.num.derivative * g.denom - g.num * g.denom.derivative))
        - 2 * (vw).ord (algebraMap K[X] (RatFunc K) g.denom) := by
    rw [ratFuncDXCoeff_def, div_eq_mul_inv,
      (vw).ord_mul hW' (inv_ne_zero (pow_ne_zero 2 hd')), (vw).ord_inv, ← zpow_natCast,
      (vw).ord_zpow]
    push_cast
    ring
  rw [key, hden]
  omega

end FinitePlaces
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section PlaceInftySide
variable [DecidableEq (RatFunc K)]
theorem ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
    {f : RatFunc K} (hf : f ≠ 0) (hord : (placeInfty K).ord f = 1) :
    ratFuncDXCoeff K f ≠ 0 ∧ (placeInfty K).ord (ratFuncDXCoeff K f) = 2 := by
  obtain ⟨e, he0, heord, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hf hord
  rw [ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe]
  exact ⟨he0, heord⟩

theorem ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg
    {g : RatFunc K} (hg : g ≠ 0) (hord : 0 ≤ (placeInfty K).ord g) :
    ratFuncDXCoeff K g = 0 ∨ 2 ≤ (placeInfty K).ord (ratFuncDXCoeff K g) := by
  rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hne
  · exact Or.inl h0
  refine Or.inr ?_
  rcases eq_or_lt_of_le hord with heq | hlt
  ·
    obtain ⟨e, he, hDe⟩ := exists_dXCoeff_ord_ge_two_of_ord_placeInfty_eq_zero hg heq.symm
    have hee := ratFuncDXCoeff_eq_of_D_eq_smul_dX hDe
    rcases he with rfl | h2
    · exact absurd hee hne
    · rw [hee]; exact h2
  ·
    have hW : g.num.derivative * g.denom - g.num * g.denom.derivative ≠ 0 :=
      wronskian_ne_zero_of_ratFuncDXCoeff_ne_zero K hne
    have h := ord_placeInfty_ratFuncDXCoeff_ge hg hW
    omega

end PlaceInftySide
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end DXCoeffIntegrality
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section PerfectDCoord
variable (K : Type*) [Field K] [PerfectField K]
theorem exists_ne_zero_smul_dX_of_uniformizer (v : Place K (RatFunc K)) :
    ∃ c : RatFunc K, c ≠ 0 ∧
      KaehlerDifferential.D K (RatFunc K) v.uniformizer = c • dX K := by
  classical
  have hord : v.ord v.uniformizer = 1 := v.ord_uniformizer
  have hpi0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  ·
    obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
    obtain ⟨hne, -⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
      (PerfectField.separable_of_irreducible hp) hpi0 hord
    exact ⟨ratFuncDXCoeff K _, hne, D_eq_ratFuncDXCoeff_smul_dX K _⟩
  ·
    obtain ⟨e, he0, -, hDe⟩ := exists_dXCoeff_ord_two_of_ord_placeInfty_eq_one hpi0 hord
    exact ⟨e, he0, hDe⟩

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal exists_irreducible_span finitePlace finitePlace_def algebraMap_mem_ofHeightOneSpectrum residueFieldEquivOfHeightOneSpectrum deg_ofHeightOneSpectrum placeOfPoint deg_placeOfPoint placeInfty placeInfty_toValuationSubring hasPrincipalDivisors ord_placeOfPoint_algebraMap eq_ofHeightOneSpectrum_or_eq_placeInfty ord_placeInfty deg_placeInfty placeInfty_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum finite_setOf_ord_ne_zero ord_placeInfty_X ord_ofHeightOneSpectrum_eq_neg_log ord_ofHeightOneSpectrum_of_span ord_placeInfty_algebraMap degree_eq_zero_of_forall_eq_ord"
p2m_open "AlgebraicCurve.RationalFunctionField"
scoped instance (priority := low) instDCoordGeneratesPerfectField (v : Place K (RatFunc K)) :
    v.DCoordGenerates := by
  obtain ⟨c, hc0, hDc⟩ := exists_ne_zero_smul_dX_of_uniformizer K v
  refine ⟨?_⟩
  have hdc : v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer := rfl
  rw [hdc, hDc, eq_top_iff, ← span_dX_eq_top K, Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_span_singleton.mpr
    ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end PerfectDCoord
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
section EulerPerfectField
variable {p : K[X]} [Fact (Irreducible p)]
theorem ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField (hpmon : p.Monic)
    {k : ℕ} (hk : k < p.natDegree - 1) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p)) = 0 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt
    (AdjoinRoot.powerBasis hpmon.ne_zero) (k := k)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen] at h

theorem ag9b12c_trace_root_pow_div_derivative_self_of_perfectField (hpmon : p.Monic)
    (hd : 0 < p.natDegree) :
    Algebra.trace K (AdjoinRoot p)
      (AdjoinRoot.root p ^ (p.natDegree - 1) /
        aeval (AdjoinRoot.root p) (derivative p)) = 1 := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hmin : minpoly K (AdjoinRoot.powerBasis hpmon.ne_zero).gen = p :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hpmon
  have h := FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self
    (AdjoinRoot.powerBasis hpmon.ne_zero)
    (by rwa [AdjoinRoot.powerBasis_dim])
  rwa [hmin, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at h

private theorem ag9b12c_aeval_root_eq_sum_range {c : K[X]} {d : ℕ} (hd : c.natDegree < d) :
    (aeval (AdjoinRoot.root p) c : AdjoinRoot p)
      = ∑ k ∈ Finset.range d, c.coeff k • AdjoinRoot.root p ^ k := by
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap K (AdjoinRoot p)) hd]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem ag9b12c_trace_adjoinRoot_mk_div_mk_derivative_of_perfectField (hpmon : p.Monic)
    {c : K[X]} (hdeg : c.degree < p.degree) :
    Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.mk p c / AdjoinRoot.mk p (derivative p))
      = c.coeff (p.natDegree - 1) := by
  haveI : FiniteDimensional K (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hpmon.ne_zero).basis
  have hpd : 0 < p.natDegree := (Fact.out : Irreducible p).natDegree_pos
  have hcd : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hpd
    · exact natDegree_lt_natDegree hc hdeg
  rw [← AdjoinRoot.aeval_eq, ← AdjoinRoot.aeval_eq,
    ag9b12c_aeval_root_eq_sum_range K hcd, Finset.sum_div, map_sum]
  trans ∑ k ∈ Finset.range p.natDegree,
      c.coeff k * Algebra.trace K (AdjoinRoot p)
        (AdjoinRoot.root p ^ k / aeval (AdjoinRoot.root p) (derivative p))
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, mul_div_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (p.natDegree - 1)]
  · rw [ag9b12c_trace_root_pow_div_derivative_self_of_perfectField K hpmon hpd, mul_one]
  · intro k hk hkne
    have hk' : k < p.natDegree - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)) hkne
    rw [ag9b12c_trace_root_pow_div_derivative_of_lt_of_perfectField K hpmon hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hpd one_pos)) h

end EulerPerfectField
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
section
section
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.WithZero Module P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Module IsLocalRing P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.IsLocalRing Module.IsLocalRing KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
section LemmaAPerfect
variable {K : Type*} [Field K] [PerfectField K]
theorem ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField
    (v : Place K (RatFunc K)) {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    ratFuncDXCoeff K v.uniformizer ≠ 0 ∧
      (ratFuncDXCoeff K g = 0 ∨
        v.ord (ratFuncDXCoeff K v.uniformizer) ≤ v.ord (ratFuncDXCoeff K g)) := by
  classical
  have hg0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne g 0 with rfl | hgne
  · refine ⟨?_, Or.inl (ratFuncDXCoeff_zero (K := K))⟩
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    · obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      exact (ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)).1
    · exact (ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
        ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)).1
  · rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
    ·
      obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
      obtain ⟨hπne, hπord⟩ := ratFuncDXCoeff_ne_zero_and_ord_eq_zero_of_ord_eq_one hp hwp
        (PerfectField.separable_of_irreducible hp)
        (Place.uniformizer_ne_zero _) (Place.ord_uniformizer _)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_ord_nonneg_of_ord_nonneg hp hwp hgne hg0 with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)
    ·
      obtain ⟨hπne, hπord⟩ :=
        ratFuncDXCoeff_ne_zero_and_ord_placeInfty_eq_two_of_ord_eq_one
          (f := (placeInfty K).uniformizer)
          ((placeInfty K).uniformizer_ne_zero) ((placeInfty K).ord_uniformizer)
      refine ⟨hπne, ?_⟩
      rcases ratFuncDXCoeff_eq_zero_or_two_le_ord_placeInfty_of_ord_nonneg hgne hg0
        with h0 | hge
      · exact Or.inl h0
      · exact Or.inr (by rw [hπord]; exact hge)

theorem ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField
    (v : Place K (RatFunc K)) (f : RatFunc K)
    (hπ : ratFuncDXCoeff K v.uniformizer ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) f)
      = ratFuncDXCoeff K f / ratFuncDXCoeff K v.uniformizer :=
  v.differentialCoeff_unique (by
    rw [show v.dCoord = KaehlerDifferential.D K (RatFunc K) v.uniformizer from rfl,
      D_eq_ratFuncDXCoeff_smul_dX K v.uniformizer, D_eq_ratFuncDXCoeff_smul_dX K f,
      smul_smul, div_mul_cancel₀ _ hπ])

theorem ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField (v : Place K (RatFunc K))
    {g : RatFunc K} (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  obtain ⟨hπne, hcase⟩ :=
    ag9b13e_ratFuncDXCoeff_uniformizer_ne_zero_and_ord_le_of_perfectField v hg
  rw [ag9b13e_differentialCoeff_D_eq_ratFuncDXCoeff_div_of_perfectField v g hπne]
  rcases hcase with h0 | hle
  · rw [h0, zero_div]; exact zero_mem _
  · rcases eq_or_ne (ratFuncDXCoeff K g) 0 with h0 | hgne'
    · rw [h0, zero_div]; exact zero_mem _
    · refine v.mem_of_ord_nonneg (div_ne_zero hgne' hπne) ?_
      rw [div_eq_mul_inv, v.ord_mul hgne' (inv_ne_zero hπne), v.ord_inv]
      omega

end LemmaAPerfect
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"

theorem surjective_algebraMap_residueField_of_deg_eq_one (K : Type*) [Field K]
    {F : Type*} [Field F] [Algebra K F]
    (v : Place K F) (hdeg : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp
    (show Module.finrank K v.ResidueField = 1 from hdeg) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue adicValuation adicValuation_ne_zero ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ofHeightOneSpectrum mk.injEq toValuationSubring mk ord_ofHeightOneSpectrum_ne_zero_iff dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK localResidue localResidue_of_mem differentialCoeff_ne_zero ramificationIndex ramificationIndex_pos restrict mem_restrict_iff ord_restrict fiber mem_fiber adicCompletion adicCompletionIntegers finiteResidue_of_deg_pos CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap ord_algebraMap ord_eq_neg_log_of_valuationSubring_eq ord_neg ord_nonneg_of_mem mem_of_ord_nonneg mem_iff_ord_nonneg exists_ord_pos"
p2m_open "AlgebraicCurve.Place~algebraMap_ne_zero"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

p2m_export "AlgebraicCurve.Place" "ord_neg'"
private theorem _root_.AlgebraicCurve.Place.ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  ·
    have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega

p2m_export "AlgebraicCurve.Place" "ord_add_eq_min"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

noncomputable section

p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"

namespace P1Tower

variable (K : Type*) [Field K] (p : K[X])

def substPoly : K[X] →ₐ[K] RatFunc K :=
  Polynomial.aeval (algebraMap K[X] (RatFunc K) p)

theorem substPoly_apply (q : K[X]) :
    substPoly K p q = algebraMap K[X] (RatFunc K) (q.comp p) := by
  simp only [substPoly, Polynomial.comp_eq_aeval, ← Polynomial.aeval_algebraMap_apply]

variable {p} in
theorem substPoly_ne_zero (hp : 0 < p.natDegree) {q : K[X]} (hq : q ≠ 0) : substPoly K p q ≠ 0 := by
  rw [substPoly_apply, Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
  exact fun h => hq ((Polynomial.comp_eq_zero_iff.mp h).resolve_right (fun hh => by
    have := hh.2; rw [this] at hp; simp at hp) )

def subst (hp : 0 < p.natDegree) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (substPoly K p) (fun q hq => by
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero (substPoly_ne_zero K hp (nonZeroDivisors.ne_zero hq)))

theorem subst_algebraMap (hp : 0 < p.natDegree) (q : K[X]) :
    subst K p hp (algebraMap K[X] (RatFunc K) q) = algebraMap K[X] (RatFunc K) (q.comp p) := by
  rw [subst, RatFunc.liftAlgHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, map_one, div_one,
    substPoly_apply]

def Kx (_hp : 0 < p.natDegree) : Type _ := RatFunc K

variable (hp : 0 < p.natDegree)

scoped instance : Field (Kx K p hp) := inferInstanceAs (Field (RatFunc K))
scoped instance : Algebra K (Kx K p hp) := inferInstanceAs (Algebra K (RatFunc K))
scoped instance : DecidableEq (Kx K p hp) := Classical.decEq _

def toKx : RatFunc K ≃ₐ[K] Kx K p hp := AlgEquiv.refl

scoped instance algebraKx : Algebra (RatFunc K) (Kx K p hp) :=
  ((toKx K p hp).toAlgHom.comp (subst K p hp)).toRingHom.toAlgebra

theorem algebraMap_Kx_apply (f : RatFunc K) :
    algebraMap (RatFunc K) (Kx K p hp) f = toKx K p hp (subst K p hp f) := rfl

scoped instance : IsScalarTower K (RatFunc K) (Kx K p hp) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    rw [algebraMap_Kx_apply, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), ← Polynomial.C_eq_algebraMap]
    show algebraMap K (RatFunc K) a = subst K p hp (algebraMap K[X] (RatFunc K) (C a))
    rw [subst_algebraMap, Polynomial.C_comp, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply])

theorem subst_X : subst K p hp (RatFunc.X : RatFunc K) = algebraMap K[X] (RatFunc K) p := by
  rw [← RatFunc.algebraMap_X, subst_algebraMap, Polynomial.X_comp]

theorem aeval_ratFuncX (q : K[X]) : aeval (RatFunc.X : RatFunc K) q = algebraMap K[X] (RatFunc K) q := by
  rw [← RatFunc.algebraMap_X]
  rw [show (algebraMap K[X] (RatFunc K)) X = (IsScalarTower.toAlgHom K K[X] (RatFunc K)) X from rfl,
    Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left]
  rfl

private def _root_.AlgebraicCurve.P1Tower.gen : Kx K p hp := toKx K p hp (RatFunc.X : RatFunc K)

p2m_export "AlgebraicCurve.P1Tower" "gen"

def minP : (RatFunc K)[X] := p.map (algebraMap K (RatFunc K)) - C (RatFunc.X : RatFunc K)

theorem toKx_apply (f : RatFunc K) : toKx K p hp f = (f : RatFunc K) := rfl

theorem aeval_gen_map (q : K[X]) :
    aeval (gen K p hp) (q.map (algebraMap K (RatFunc K))) = toKx K p hp (algebraMap K[X] (RatFunc K) q) := by
  rw [aeval_map_algebraMap]
  exact aeval_ratFuncX K q

theorem aeval_gen_minP : aeval (gen K p hp) (minP K p) = 0 := by
  rw [minP, map_sub, aeval_gen_map, aeval_C, algebraMap_Kx_apply, subst_X, sub_self]

include hp in
theorem monic_minP (hmon : p.Monic) : (minP K p).Monic := by
  rw [minP]
  refine (hmon.map _).sub_of_left ?_
  rw [degree_C (RatFunc.X_ne_zero), Polynomial.degree_map]
  exact_mod_cast (show (0 : WithBot ℕ) < p.degree from by
    rw [Polynomial.degree_eq_natDegree (by rintro rfl; simp at hp)]; exact_mod_cast hp)

private theorem _root_.AlgebraicCurve.P1Tower.isIntegral_gen (hmon : p.Monic) : IsIntegral (RatFunc K) (gen K p hp) :=
  ⟨minP K p, monic_minP K p hp hmon, by
    have h := aeval_gen_minP K p hp
    rwa [aeval_def] at h⟩

p2m_export "AlgebraicCurve.P1Tower" "isIntegral_gen"
include hp in
theorem minP_ne_zero (hmon : p.Monic) : minP K p ≠ 0 := (monic_minP K p hp hmon).ne_zero

theorem toKx_algebraMap_mem_adjoin (q : K[X]) :
    toKx K p hp (algebraMap K[X] (RatFunc K) q) ∈ IntermediateField.adjoin (RatFunc K) {gen K p hp} := by
  rw [← aeval_gen_map]
  exact IntermediateField.algebra_adjoin_le_adjoin (RatFunc K) _ (Polynomial.aeval_mem_adjoin_singleton (RatFunc K) _)

theorem adjoin_gen_eq_top : IntermediateField.adjoin (RatFunc K) {gen K p hp} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  induction f using RatFunc.induction_on with
  | f a b hb =>
    have ha := toKx_algebraMap_mem_adjoin K p hp a
    have hb' := toKx_algebraMap_mem_adjoin K p hp b
    exact div_mem ha hb'

theorem finiteDimensional_Kx (hmon : p.Monic) : FiniteDimensional (RatFunc K) (Kx K p hp) := by
  have h := IntermediateField.adjoin.finiteDimensional (isIntegral_gen K p hp hmon)
  rw [adjoin_gen_eq_top] at h
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem isIntegral_Kx (hmon : p.Monic) : Algebra.IsIntegral (RatFunc K) (Kx K p hp) :=
  haveI := finiteDimensional_Kx K p hp hmon
  Algebra.IsIntegral.of_finite (RatFunc K) (Kx K p hp)

theorem derivative_minP : derivative (minP K p) = (derivative p).map (algebraMap K (RatFunc K)) := by
  rw [minP, derivative_sub, derivative_C, sub_zero, Polynomial.derivative_map]

theorem transcendental_ratFuncX : Transcendental K (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact (transcendental_algebraMap_iff (IsFractionRing.injective K[X] (RatFunc K))).mpr
    (Polynomial.transcendental_X K)

include hp in
theorem separable_minP (hsep : p.Separable) : (minP K p).Separable := by
  classical
  let L := AlgebraicClosure (RatFunc K)
  rw [Polynomial.Separable, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (RatFunc K) L]
  intro β
  by_contra h
  push_neg at h
  obtain ⟨hP, hP'⟩ := h
  have hd0 : derivative p ≠ 0 := by
    intro h0
    have hu : IsUnit p := by
      have hc : IsCoprime p (derivative p) := hsep
      rw [h0] at hc
      exact isCoprime_zero_right.mp hc
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have h1 : aeval β (derivative p) = 0 := by
    rw [derivative_minP, aeval_map_algebraMap] at hP'
    exact hP'
  have hβ : IsIntegral K β := isAlgebraic_iff_isIntegral.mp ⟨derivative p, hd0, h1⟩
  have h2 : aeval β p = algebraMap (RatFunc K) L RatFunc.X := by
    rw [minP, map_sub, aeval_map_algebraMap, aeval_C, sub_eq_zero] at hP
    exact hP
  have h3 : IsIntegral K (aeval β p) :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin K {β}) hβ.fg_adjoin_singleton _
      (Polynomial.aeval_mem_adjoin_singleton K _)
  rw [h2] at h3
  have h4 : IsIntegral K (RatFunc.X : RatFunc K) :=
    (isIntegral_algebraMap_iff (algebraMap (RatFunc K) L).injective).mp h3
  exact transcendental_ratFuncX K h4.isAlgebraic

theorem isSeparable_gen (hmon : p.Monic) (hsep : p.Separable) : IsSeparable (RatFunc K) (gen K p hp) :=
  (separable_minP K p hp hsep).of_dvd (minpoly.dvd _ _ (aeval_gen_minP K p hp))

theorem isSeparable_Kx (hmon : p.Monic) (hsep : p.Separable) :
    Algebra.IsSeparable (RatFunc K) (Kx K p hp) := by
  haveI := finiteDimensional_Kx K p hp hmon
  have h : Algebra.IsSeparable (RatFunc K) (IntermediateField.adjoin (RatFunc K) {gen K p hp}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc K) (Kx K p hp)).mpr
      (isSeparable_gen K p hp hmon hsep)
  rw [adjoin_gen_eq_top] at h
  exact Algebra.IsSeparable.of_algHom (RatFunc K) _
    (IntermediateField.topEquiv (F := RatFunc K) (E := Kx K p hp)).symm.toAlgHom

end P1Tower
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"

namespace P1Tower

p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] (p : K[X]) (hp : 0 < p.natDegree)

scoped instance hasPrincipalDivisors_Kx : HasPrincipalDivisors K (Kx K p hp) :=
  RationalFunctionField.hasPrincipalDivisors K

variable {p} in

theorem ord_finitePlace_pos_iff_dvd {q : K[X]} (hirr : Irreducible q) {a : K[X]} (ha : a ≠ 0) :
    0 < (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) a) ↔ q ∣ a := by
  have hmem := algebraMap_mem_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hirr) a
  have hnn : 0 ≤ (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) a) :=
    (finitePlace K hirr).ord_nonneg_of_mem hmem
  have hiff := Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
    (heightOneSpectrumOfIrreducible K hirr) ha
  rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, ← finitePlace_def] at hiff
  rw [← hiff]
  omega

variable {p} in
theorem ord_finitePlace_eq_zero_iff_not_dvd {q : K[X]} (hirr : Irreducible q) {a : K[X]} (ha : a ≠ 0) :
    (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) a) = 0 ↔ ¬ q ∣ a := by
  have hiff := Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
    (heightOneSpectrumOfIrreducible K hirr) ha
  rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, ← finitePlace_def] at hiff
  rw [← hiff, not_not]

theorem not_dvd_comp_of_eval_zero_ne_zero {u : K[X]} (hu : u.eval 0 ≠ 0) (hpu : ¬ IsUnit p) :
    ¬ p ∣ u.comp p := by
  intro hdvd

  have hX : X ∣ u - C (u.eval 0) := by
    rw [Polynomial.X_dvd_iff, coeff_sub, coeff_C_zero, ← Polynomial.coeff_zero_eq_eval_zero, sub_self]
  obtain ⟨r, hr⟩ := hX
  have hcomp : u.comp p = p * r.comp p + C (u.eval 0) := by
    have := congrArg (fun q => q.comp p) hr
    simp only [Polynomial.sub_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp] at this
    rw [← this]; ring
  have : p ∣ C (u.eval 0) := by
    have h2 : C (u.eval 0) = u.comp p - p * r.comp p := by rw [hcomp]; ring
    rw [h2]
    exact dvd_sub hdvd (dvd_mul_right _ _)
  exact hpu (isUnit_of_dvd_unit this (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hu)))

include hp in
theorem not_isUnit_p : ¬ IsUnit p := fun h => by
  have := Polynomial.natDegree_eq_zero_of_isUnit h; omega

theorem ord_finitePlace_subst_algebraMap (hirr : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (finitePlace K hirr).ord (subst K p hp (algebraMap K[X] (RatFunc K) q))
      = (Polynomial.rootMultiplicity 0 q : ℤ)
        * (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) := by
  obtain ⟨u, hqu, hXu⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0
  set k := Polynomial.rootMultiplicity 0 q
  have hu0 : u ≠ 0 := by rintro rfl; simp at hqu; exact hq hqu
  have hueval : u.eval 0 ≠ 0 := by
    intro h
    exact hXu (by simpa using (Polynomial.dvd_iff_isRoot).mpr h)
  have hcomp : q.comp p = p ^ k * u.comp p := by
    conv_lhs => rw [hqu]
    simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_zero, sub_zero]
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hup0 : u.comp p ≠ 0 := fun h => by
    have := not_dvd_comp_of_eval_zero_ne_zero K p hueval (not_isUnit_p K p hp)
    rw [h] at this; exact this (dvd_zero _)
  rw [subst_algebraMap, hcomp, map_mul, map_pow,
    (finitePlace K hirr).ord_mul (pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hp0))
      ((map_ne_zero_iff _ hinj).mpr hup0),
    ← zpow_natCast, (finitePlace K hirr).ord_zpow,
    (ord_finitePlace_eq_zero_iff_not_dvd K hirr hup0).mpr
      (not_dvd_comp_of_eval_zero_ne_zero K p hueval (not_isUnit_p K p hp)), add_zero]

theorem ord_finitePlace_subst (hirr : Irreducible p) (f : RatFunc K) :
    (finitePlace K hirr).ord (subst K p hp f)
      = (placeOfPoint K 0).ord f * (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hsn : subst K p hp (algebraMap K[X] (RatFunc K) f.num) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.num ▸ substPoly_ne_zero K hp hnum
  have hsd : subst K p hp (algebraMap K[X] (RatFunc K) f.denom) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.denom ▸ substPoly_ne_zero K hp hden
  conv_lhs => rw [← RatFunc.num_div_denom f, map_div₀]
  conv_rhs => rw [← RatFunc.num_div_denom f]
  rw [div_eq_mul_inv, div_eq_mul_inv, (finitePlace K hirr).ord_mul hsn (inv_ne_zero hsd), Place.ord_inv,
    ord_finitePlace_subst_algebraMap K p hp hirr hnum, ord_finitePlace_subst_algebraMap K p hp hirr hden,
    (placeOfPoint K 0).ord_mul ((map_ne_zero_iff _ hinj).mpr hnum)
      (inv_ne_zero ((map_ne_zero_iff _ hinj).mpr hden)), Place.ord_inv,
    ord_placeOfPoint_algebraMap 0 hnum, ord_placeOfPoint_algebraMap 0 hden]
  ring

theorem restrict_finitePlace (hirr : Irreducible p) [Algebra.IsIntegral (RatFunc K) (Kx K p hp)] :
    Place.restrict (RatFunc K) (show Place K (Kx K p hp) from finitePlace K hirr) = placeOfPoint K 0 := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [Place.mem_restrict_iff]
  show subst K p hp f ∈ (finitePlace K hirr).toValuationSubring ↔ _
  rcases eq_or_ne f 0 with rfl | hf
  · simp [map_zero, zero_mem]
  have hsf : subst K p hp f ≠ 0 := (map_ne_zero_iff _ (subst K p hp).toRingHom.injective).mpr hf
  have hpos : 0 < (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) := by
    rw [ord_finitePlace_pos_iff_dvd K hirr hirr.ne_zero]
  rw [Place.mem_iff_ord_nonneg _ hsf, Place.mem_iff_ord_nonneg _ hf, ord_finitePlace_subst K p hp hirr]
  constructor
  · intro h; by_contra hneg; push_neg at hneg
    have : (placeOfPoint K 0).ord f * (finitePlace K hirr).ord (algebraMap K[X] (RatFunc K) p) < 0 :=
      mul_neg_of_neg_of_pos hneg hpos
    omega
  · intro h; exact mul_nonneg h hpos.le

scoped instance instFiniteResiduePlaceKx [DecidableEq (RatFunc K)] (w : Place K (Kx K p hp)) : w.FiniteResidue :=
  RationalFunctionField.instFiniteResidue (K := K) w

variable {p} in

theorem eq_finitePlace_of_ord_pos [DecidableEq (RatFunc K)] (hirr : Irreducible p)
    {w' : Place K (RatFunc K)} (h : 0 < w'.ord (algebraMap K[X] (RatFunc K) p)) :
    w' = finitePlace K hirr := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty w' with ⟨q, rfl⟩ | rfl
  · have hmem : p ∈ q.asIdeal :=
      (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) q hirr.ne_zero).mp h.ne'
    obtain ⟨r, hrirr, hr⟩ := exists_irreducible_span K q
    have hassoc : Associated r p := by
      rw [hr, Ideal.mem_span_singleton] at hmem
      exact hrirr.associated_of_dvd hirr hmem
    have hq : q = heightOneSpectrumOfIrreducible K hirr := by
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      rw [heightOneSpectrumOfIrreducible_asIdeal, hr, Ideal.span_singleton_eq_span_singleton]
      exact hassoc
    rw [hq, finitePlace_def]
  · exfalso
    rw [ord_placeInfty ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hirr.ne_zero),
      RatFunc.intDegree_polynomial] at h
    have : (0 : ℤ) ≤ (p.natDegree : ℤ) := Int.natCast_nonneg _
    omega

theorem finitePlace_mem_fiber (hirr : Irreducible p) [Algebra.IsIntegral (RatFunc K) (Kx K p hp)] :
    (show Place K (Kx K p hp) from finitePlace K hirr) ∈ (placeOfPoint K 0).fiber (Kx K p hp) :=
  Place.mem_fiber.mpr (restrict_finitePlace K p hp hirr)

theorem fiber_placeOfPoint_zero (hirr : Irreducible p) [DecidableEq (RatFunc K)]
    [Algebra.IsIntegral (RatFunc K) (Kx K p hp)] :
    (placeOfPoint K 0).fiber (Kx K p hp) = {(show Place K (Kx K p hp) from finitePlace K hirr)} := by
  ext w'
  rw [Finset.mem_singleton, Place.mem_fiber]
  constructor
  · intro hw'

    have hX : (placeOfPoint K 0).ord (RatFunc.X : RatFunc K) = 1 := by
      classical
      rw [← RatFunc.algebraMap_X, ord_placeOfPoint_algebraMap 0 Polynomial.X_ne_zero]
      have h := (Polynomial.rootMultiplicity_X_sub_C : Polynomial.rootMultiplicity (0 : K) (X - C 0) = _)
      rw [map_zero, sub_zero, if_pos rfl] at h
      exact_mod_cast h
    have hord : w'.ord (algebraMap (RatFunc K) (Kx K p hp) RatFunc.X)
        = (Place.ramificationIndex (F := RatFunc K) w' : ℤ) * 1 := by
      rw [Place.ord_restrict, hw', hX]
    have hpos : 0 < w'.ord (algebraMap (RatFunc K) (Kx K p hp) RatFunc.X) := by
      rw [hord, mul_one]; exact_mod_cast Place.ramificationIndex_pos (F := RatFunc K) w'
    rw [algebraMap_Kx_apply, subst_X] at hpos
    exact eq_finitePlace_of_ord_pos K hirr hpos
  · rintro rfl
    exact restrict_finitePlace K p hp hirr

theorem ord_placeInfty_subst_algebraMap [DecidableEq (RatFunc K)] {q : K[X]} (hq : q ≠ 0) :
    (placeInfty K).ord (subst K p hp (algebraMap K[X] (RatFunc K) q))
      = (p.natDegree : ℤ) * (placeInfty K).ord (algebraMap K[X] (RatFunc K) q) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hqp : q.comp p ≠ 0 := fun h => by
    have := substPoly_ne_zero K hp hq; rw [substPoly_apply, h, map_zero] at this; exact this rfl
  rw [subst_algebraMap, ord_placeInfty ((map_ne_zero_iff _ hinj).mpr hqp),
    ord_placeInfty ((map_ne_zero_iff _ hinj).mpr hq), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, Polynomial.natDegree_comp]
  push_cast
  ring

theorem ord_placeInfty_subst [DecidableEq (RatFunc K)] (f : RatFunc K) :
    (placeInfty K).ord (subst K p hp f) = (p.natDegree : ℤ) * (placeInfty K).ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hsn : subst K p hp (algebraMap K[X] (RatFunc K) f.num) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.num ▸ substPoly_ne_zero K hp hnum
  have hsd : subst K p hp (algebraMap K[X] (RatFunc K) f.denom) ≠ 0 := by
    rw [subst_algebraMap]; exact substPoly_apply K p f.denom ▸ substPoly_ne_zero K hp hden
  conv_lhs => rw [← RatFunc.num_div_denom f, map_div₀]
  conv_rhs => rw [← RatFunc.num_div_denom f]
  rw [div_eq_mul_inv, div_eq_mul_inv, (placeInfty K).ord_mul hsn (inv_ne_zero hsd), Place.ord_inv,
    ord_placeInfty_subst_algebraMap K p hp hnum, ord_placeInfty_subst_algebraMap K p hp hden,
    (placeInfty K).ord_mul ((map_ne_zero_iff _ hinj).mpr hnum)
      (inv_ne_zero ((map_ne_zero_iff _ hinj).mpr hden)), Place.ord_inv]
  ring

theorem ord_sum_of_injOn {F : Type*} [Field F] [Algebra K F] (v : Place K F) {ι : Type*} (s : Finset ι)
    (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) (hinj : Set.InjOn (fun i => v.ord (f i)) s) (hs : s.Nonempty) :
    (∑ i ∈ s, f i) ≠ 0 ∧ v.ord (∑ i ∈ s, f i) = s.inf' hs (fun i => v.ord (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (Finset.not_nonempty_empty)
  | @insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · refine ⟨?_, ?_⟩
      · simpa using hf a (Finset.mem_insert_self a ∅)
      · simp
    have hf' : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hinj' : Set.InjOn (fun i => v.ord (f i)) s := hinj.mono (Finset.subset_insert a s)
    obtain ⟨hne, hord⟩ := ih hf' hinj' hsne
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)

    obtain ⟨j, hj, hjmin⟩ := Finset.exists_mem_eq_inf' hsne (fun i => v.ord (f i))
    have hdiff : v.ord (f a) ≠ v.ord (∑ i ∈ s, f i) := by
      rw [hord, hjmin]
      intro heq
      have := hinj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hj) heq
      exact ha (this ▸ hj)
    rw [Finset.sum_insert ha, Finset.inf'_insert]
    refine ⟨?_, ?_⟩
    · intro h0
      have : ∑ i ∈ s, f i = -f a := eq_neg_of_add_eq_zero_right h0
      rw [this, v.ord_neg'] at hdiff
      exact hdiff rfl
    · rw [v.ord_add_eq_min hfa hne hdiff, hord]

theorem linearIndependent_pow_gen [DecidableEq (RatFunc K)] :
    LinearIndependent (RatFunc K) (fun i : Fin p.natDegree => gen K p hp ^ (i : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg

  have hsum : ∑ i : Fin p.natDegree, subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ) = 0 := by
    have : ∀ i : Fin p.natDegree, g i • gen K p hp ^ (i : ℕ)
        = toKx K p hp (subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ)) := fun i => by
      rw [Algebra.smul_def, algebraMap_Kx_apply]; rfl
    simp_rw [this] at hg
    rw [← map_sum] at hg
    exact (map_eq_zero_iff _ (toKx K p hp).injective).mp hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  let S : Finset (Fin p.natDegree) := Finset.univ.filter (fun i => g i ≠ 0)
  have hS : S.Nonempty := ⟨i0, by simp [S, hi0]⟩
  have hterm : ∀ i ∈ S, subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ) ≠ 0 := by
    intro i hi
    have hgi : g i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact mul_ne_zero ((_root_.map_ne_zero (subst K p hp)).mpr hgi)
      (pow_ne_zero _ RatFunc.X_ne_zero)
  have hordt : ∀ i ∈ S, (placeInfty K).ord (subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ))
      = (p.natDegree : ℤ) * (placeInfty K).ord (g i) - (i : ℕ) := by
    intro i hi
    have hgi : g i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [(placeInfty K).ord_mul ((_root_.map_ne_zero (subst K p hp)).mpr hgi)
      (pow_ne_zero _ RatFunc.X_ne_zero), ← zpow_natCast, (placeInfty K).ord_zpow,
      ord_placeInfty_subst, ord_placeInfty RatFunc.X_ne_zero, RatFunc.intDegree_X]
    ring
  have hinj : Set.InjOn (fun i => (placeInfty K).ord (subst K p hp (g i) * (RatFunc.X : RatFunc K) ^ (i : ℕ))) S := by
    intro i hi j hj heq
    simp only at heq
    rw [hordt i hi, hordt j hj] at heq

    have hd : ((p.natDegree : ℤ)) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by
      refine ⟨(placeInfty K).ord (g i) - (placeInfty K).ord (g j), ?_⟩
      linear_combination (-1 : ℤ) * heq
    have hlt : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs < ((p.natDegree : ℤ)).natAbs := by
      have hi' := i.isLt; have hj' := j.isLt
      omega
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hlt
    exact Fin.ext (by omega)
  have key := (ord_sum_of_injOn K (placeInfty K) S _ hterm hinj hS).1
  apply key
  rw [← hsum]
  refine Finset.sum_filter_of_ne (fun i _ hne => ?_)
  intro hgi
  apply hne
  rw [hgi, map_zero, zero_mul]

theorem natDegree_le_finrank [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    p.natDegree ≤ Module.finrank (RatFunc K) (Kx K p hp) := by
  haveI := finiteDimensional_Kx K p hp hmon
  simpa using (linearIndependent_pow_gen K p hp).fintype_card_le_finrank

theorem minpoly_gen [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    minpoly (RatFunc K) (gen K p hp) = minP K p := by
  haveI := finiteDimensional_Kx K p hp hmon
  have hint := isIntegral_gen K p hp hmon
  have hdvd : minpoly (RatFunc K) (gen K p hp) ∣ minP K p := minpoly.dvd _ _ (aeval_gen_minP K p hp)
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_minP K p hp hmon) hdvd ?_

  have h1 : (minP K p).natDegree = p.natDegree := by
    rw [minP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [natDegree_C, hp]
  have h2 : Module.finrank (RatFunc K) (Kx K p hp) = (minpoly (RatFunc K) (gen K p hp)).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, adjoin_gen_eq_top]
    exact (IntermediateField.topEquiv (F := RatFunc K) (E := Kx K p hp)).toLinearEquiv.finrank_eq.symm
  rw [h1, ← h2]
  exact natDegree_le_finrank K p hp hmon

end P1Tower
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"

namespace P1Tower

p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] (p : K[X]) (hp : 0 < p.natDegree)

noncomputable def pbGen [DecidableEq (RatFunc K)] (hmon : p.Monic) : PowerBasis (RatFunc K) (Kx K p hp) :=
  (IntermediateField.adjoin.powerBasis (isIntegral_gen K p hp hmon)).map
    ((IntermediateField.equivOfEq (adjoin_gen_eq_top K p hp)).trans IntermediateField.topEquiv)

theorem pbGen_gen [DecidableEq (RatFunc K)] (hmon : p.Monic) : (pbGen K p hp hmon).gen = gen K p hp := by
  simp [pbGen, IntermediateField.adjoin.powerBasis_gen]

theorem pbGen_dim [DecidableEq (RatFunc K)] (hmon : p.Monic) : (pbGen K p hp hmon).dim = p.natDegree := by
  rw [pbGen, PowerBasis.map_dim, IntermediateField.adjoin.powerBasis_dim, minpoly_gen K p hp hmon, minP,
    natDegree_sub_eq_left_of_natDegree_lt] <;> simp [natDegree_C, hp]

theorem aeval_gen_derivative_minpoly [DecidableEq (RatFunc K)] (hmon : p.Monic) :
    aeval (gen K p hp) (derivative (minpoly (RatFunc K) (gen K p hp)))
      = toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p)) := by
  rw [minpoly_gen K p hp hmon, derivative_minP, aeval_gen_map]

theorem toKx_algebraMap_eq_sum {c : K[X]} (hc : c.natDegree < p.natDegree) :
    toKx K p hp (algebraMap K[X] (RatFunc K) c)
      = ∑ k ∈ Finset.range p.natDegree, algebraMap K (RatFunc K) (c.coeff k) • gen K p hp ^ k := by
  rw [← aeval_gen_map, Polynomial.aeval_eq_sum_range' (by rwa [Polynomial.natDegree_map])]
  simp only [Polynomial.coeff_map]

theorem trace_mul_inv_derivative [DecidableEq (RatFunc K)] (hmon : p.Monic) (hsep : p.Separable)
    {c : K[X]} (hc : c.natDegree < p.natDegree) :
    haveI := finiteDimensional_Kx K p hp hmon
    Algebra.trace (RatFunc K) (Kx K p hp)
      (toKx K p hp (algebraMap K[X] (RatFunc K) c)
        * (toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p)))⁻¹)
      = algebraMap K (RatFunc K) (c.coeff (p.natDegree - 1)) := by
  haveI := finiteDimensional_Kx K p hp hmon
  haveI := isSeparable_Kx K p hp hmon hsep
  have hgen := pbGen_gen K p hp hmon
  have hdim := pbGen_dim K p hp hmon
  have hder : toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p))
      = aeval (pbGen K p hp hmon).gen (derivative (minpoly (RatFunc K) (pbGen K p hp hmon).gen)) := by
    rw [hgen, aeval_gen_derivative_minpoly K p hp hmon]
  rw [toKx_algebraMap_eq_sum K p hp hc, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, LinearMap.map_smul, ← div_eq_mul_inv, hder, ← hgen]

  have hd : 0 < (pbGen K p hp hmon).dim := by rw [hdim]; exact hp
  rw [← hdim, Finset.sum_eq_single ((pbGen K p hp hmon).dim - 1)]
  · rw [FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_self _ hd, smul_eq_mul, mul_one]
  · intro k hk hne
    rw [Finset.mem_range] at hk
    have hk' : k < (pbGen K p hp hmon).dim - 1 := by omega
    rw [FLT.EulerDualBasis.trace_pow_div_aeval_derivative_minpoly_of_lt _ hk', smul_zero]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

end P1Tower
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"

section LocalResidueCompletionC4

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]

theorem kwHgfV352_localResidueCompletion_spec (v : Place K E) (xh : v.adicCompletion)
    {x : E} (hx : algebraMap E v.adicCompletion x - xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = v.localResidue x := by
  unfold kwHgfV352_localResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x)
      = (algebraMap E v.adicCompletion x₀ - xh) - (algebraMap E v.adicCompletion x - xh) := by
    rw [map_sub]; ring
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hx
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 := v.localResidue_of_mem hov
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem kwHgfV352_localResidueCompletion_algebraMap (v : Place K E) (x : E) :
    kwHgfV352_localResidueCompletion v (algebraMap E v.adicCompletion x)
      = v.localResidue x :=
  kwHgfV352_localResidueCompletion_spec v _
    (by rw [sub_self]; exact zero_mem _)

end LocalResidueCompletionC4
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.FiniteResidue Place.ord Place.ord_inv HasPrincipalDivisors Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.finitePlace IsCurveOver Place.ord_uniformizer Place.uniformizer_ne_zero diagonalHom diagonalHom_apply HasCanonicalDivisor Place.CanonicalLocalResidueDataK HasCanonicalLocalResidueKStar kaehlerResidueTerm HasCanonicalLocalResidueKStar.dataKStar Place.ramificationIndex Place.ramificationIndex_pos Place.restrict Place.mem_restrict_iff Place.ord_restrict Place.mem_fiber kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt Place.finiteResidue_of_deg_pos residueTraceCompletionCommute_v2 completionTraceSum_of_isSeparable RationalFunctionField.hasPrincipalDivisors Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap Place.ord_algebraMap Place.ord_eq_neg_log_of_valuationSubring_eq Place.ord_neg instIsCurveOverRatFunc Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg Place.mem_iff_ord_nonneg Place.exists_ord_pos"
p2m_open "AlgebraicCurve"

namespace P1Tower

p2m_open "Polynomial P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField KaehlerDifferential P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.KaehlerDifferential"

variable (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
  [IsCurveOver K (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
  (p : K[X]) (hp : 0 < p.natDegree)

scoped instance isCurveOver_Kx : IsCurveOver K (Kx K p hp) := ‹IsCurveOver K (RatFunc K)›
scoped instance nontrivialKaehler_Kx : Nontrivial Ω[(Kx K p hp)⁄K] := ‹Nontrivial Ω[(RatFunc K)⁄K]›
scoped instance dCoordGenerates_Kx (w : Place K (Kx K p hp)) : w.DCoordGenerates :=
  ‹∀ v : Place K (RatFunc K), v.DCoordGenerates› w

theorem D_ratFuncX_ne_zero : KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K) ≠ 0 := by
  intro h0
  have hpoly : ∀ q : K[X], KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) q) = 0 := by
    intro q
    rw [← aeval_ratFuncX K q, Derivation.map_aeval, h0, smul_zero]
  have hall : ∀ f : RatFunc K, KaehlerDifferential.D K (RatFunc K) f = 0 := by
    intro f
    rw [← RatFunc.num_div_denom f, Derivation.leibniz_div, hpoly, hpoly, smul_zero, smul_zero, sub_zero,
      smul_zero]
  have htop := KaehlerDifferential.span_range_derivation (R := K) (S := RatFunc K)
  have hbot : Submodule.span (RatFunc K) (Set.range (KaehlerDifferential.D K (RatFunc K))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨f, rfl⟩
    exact hall f
  rw [hbot] at htop
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[(RatFunc K)⁄K])
  exact hx (Submodule.mem_bot (R := RatFunc K) |>.mp (htop.symm ▸ Submodule.mem_top (x := x)))

include hp in

theorem trace_localResidue_finitePlace_div_pow_eq_zero
    (hmon : p.Monic) (hirr : Irreducible p) {c : K[X]} (hc : c.degree < p.degree) {m : ℕ} (hm : 2 ≤ m) :
    Algebra.trace K (finitePlace K hirr).ResidueField
        ((finitePlace K hirr).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
            * (finitePlace K hirr).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  classical
  have hsep : p.Separable := PerfectField.separable_of_irreducible hirr
  haveI := finiteDimensional_Kx K p hp hmon
  haveI := isIntegral_Kx K p hp hmon
  haveI := isSeparable_Kx K p hp hmon hsep
  haveI hPD : HasPrincipalDivisors K (RatFunc K) := RationalFunctionField.hasPrincipalDivisors K

  set v0 : Place K (RatFunc K) := placeOfPoint K 0 with hv0
  let w : Place K (Kx K p hp) := (finitePlace K hirr : Place K (RatFunc K))
  have hw : w ∈ v0.fiber (Kx K p hp) := finitePlace_mem_fiber K p hp hirr
  have hfib : v0.fiber (Kx K p hp) = {w} := fiber_placeOfPoint_zero K p hp hirr

  set E := RatFunc K
  set t : RatFunc K := RatFunc.X with ht
  set ε : RatFunc K := v0.differentialCoeff (KaehlerDifferential.D K (RatFunc K) t) with hε
  have hε0 : ε ≠ 0 := v0.differentialCoeff_ne_zero (D_ratFuncX_ne_zero K)
  set P' : Kx K p hp := toKx K p hp (algebraMap K[X] (RatFunc K) (derivative p)) with hP'
  have hP'0 : P' ≠ 0 := by
    rw [hP']
    refine (_root_.map_ne_zero (toKx K p hp)).mpr ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr ?_)
    intro hd
    have : IsCoprime p (derivative p) := hsep
    rw [hd] at this
    exact not_isUnit_p K p hp (isCoprime_zero_right.mp this)
  set cX : Kx K p hp := toKx K p hp (algebraMap K[X] (RatFunc K) c) with hcX
  set f : Kx K p hp := toKx K p hp (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m) with hf
  set g : Kx K p hp := f * algebraMap E (Kx K p hp) ε * P'⁻¹ with hg

  set ω : Ω[(Kx K p hp)⁄K] := kaehlerPullback K (Kx K p hp) E v0.dCoord with hω
  have hcotr : algebraMap E (Kx K p hp) ε • ω
      = P' • KaehlerDifferential.D K (Kx K p hp) (gen K p hp) := by
    have h1 : KaehlerDifferential.D K E t = ε • v0.dCoord := (v0.differentialCoeff_smul_dCoord _).symm
    have h2 : kaehlerPullback K (Kx K p hp) E (KaehlerDifferential.D K E t)
        = algebraMap E (Kx K p hp) ε • ω := by
      rw [h1, hω, kaehlerPullback, kaehlerPullback, LinearMap.map_smul, algebraMap_smul]
    have h3 : kaehlerPullback K (Kx K p hp) E (KaehlerDifferential.D K E t)
        = KaehlerDifferential.D K (Kx K p hp) (algebraMap E (Kx K p hp) t) := by
      rw [kaehlerPullback, KaehlerDifferential.map_D]
    have h4 : algebraMap E (Kx K p hp) t = aeval (gen K p hp) p := by
      rw [algebraMap_Kx_apply, ht, subst_X]
      exact (aeval_ratFuncX K p).symm
    rw [← h2, h3, h4, Derivation.map_aeval, hP', ← aeval_ratFuncX K (derivative p)]
    rfl

  have hcoeffω : w.differentialCoeff ω
      = (algebraMap E (Kx K p hp) ε)⁻¹ * P' * w.differentialCoeff (KaehlerDifferential.D K (Kx K p hp) (gen K p hp)) := by
    have hεK : algebraMap E (Kx K p hp) ε ≠ 0 := (_root_.map_ne_zero _).mpr hε0
    have : ω = ((algebraMap E (Kx K p hp) ε)⁻¹ * P') • KaehlerDifferential.D K (Kx K p hp) (gen K p hp) := by
      rw [mul_smul, ← hcotr, smul_smul, inv_mul_cancel₀ hεK, one_smul]
    rw [this, w.differentialCoeff_smul]
  have hgω : g * w.differentialCoeff ω = f * w.differentialCoeff (KaehlerDifferential.D K (Kx K p hp) (gen K p hp)) := by
    have hεK : algebraMap E (Kx K p hp) ε ≠ 0 := (_root_.map_ne_zero _).mpr hε0
    rw [hcoeffω, hg]; field_simp

  have hRTCC := residueTraceCompletionCommute_v2 (K := K) (F := Kx K p hp) (E := E) v0 w hw g
  have hCTS := completionTraceSum_of_isSeparable (K := K) (F := Kx K p hp) (E := E) v0 g
  have hsum : (∑ w' ∈ (v0.fiber (Kx K p hp)).attach,
        kwHgfV352_completionTraceAt v0 w'.1 w'.2 g)
      = kwHgfV352_completionTraceAt v0 w hw g := by
    have hone : ∀ w' : { x // x ∈ v0.fiber (Kx K p hp) }, (w' : Place K (Kx K p hp)) = w := fun w' => by
      have h : (w'.1 : Place K (Kx K p hp)) ∈ ({w} : Finset (Place K (Kx K p hp))) := hfib ▸ w'.2
      exact Finset.mem_singleton.mp h
    rw [Finset.sum_eq_single_of_mem (⟨w, hw⟩ : { x // x ∈ v0.fiber (Kx K p hp) }) (Finset.mem_attach _ _)
      (fun w' _ hne => (hne (Subtype.ext (hone w'))).elim)]
  rw [hsum] at hCTS
  rw [← hCTS, kwHgfV352_localResidueCompletion_algebraMap] at hRTCC

  have hLHS : kaehlerResidueTerm ω (diagonalHom K (Kx K p hp) g) w
      = Algebra.trace K (finitePlace K hirr).ResidueField
          ((finitePlace K hirr).localResidue
            (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
              * (finitePlace K hirr).differentialCoeff
                  (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) := by
    rw [kaehlerResidueTerm, diagonalHom_apply, hgω]
    rfl
  rw [← hLHS, hRTCC]

  have hc' : c.natDegree < p.natDegree := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simpa using hp
    exact Polynomial.natDegree_lt_natDegree hc0 hc
  have htr : Algebra.trace E (Kx K p hp) g
      = ε * (t ^ m)⁻¹ * algebraMap K E (c.coeff (p.natDegree - 1)) := by
    have hf' : f = algebraMap E (Kx K p hp) ((t ^ m)⁻¹) * cX := by
      rw [algebraMap_Kx_apply, map_inv₀, map_pow, ht, subst_X, hf, hcX, ← map_mul (toKx K p hp)]
      congr 1
      rw [div_eq_mul_inv, mul_comm]
    have hg' : g = ((t ^ m)⁻¹ * ε) • (cX * P'⁻¹) := by
      rw [hg, hf', Algebra.smul_def, map_mul]; ring
    rw [hg', LinearMap.map_smul, smul_eq_mul, hcX, hP', trace_mul_inv_derivative K p hp hmon hsep hc']
    ring
  rw [htr]

  have hsurj : Function.Surjective (algebraMap K v0.ResidueField) :=
    AlgebraicCurve.surjective_algebraMap_residueField_of_deg_eq_one K v0 (by rw [hv0, deg_placeOfPoint])
  have htord : v0.ord t = 1 := by
    rw [hv0, ht, ← RatFunc.algebraMap_X, ord_placeOfPoint_algebraMap 0 Polynomial.X_ne_zero]
    have h := (Polynomial.rootMultiplicity_X_sub_C : Polynomial.rootMultiplicity (0 : K) (X - C 0) = _)
    rw [map_zero, sub_zero, if_pos rfl] at h
    exact_mod_cast h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hC1 := AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
    v0 hsurj (fun h hh => ag9b13e_differentialCoeff_D_mem_of_mem_of_perfectField v0 hh)
    (HasCanonicalLocalResidueKStar.dataKStar v0) htord (n := n) (by omega)
  have hres : v0.localResidue (ε * (t ^ (n + 1))⁻¹ * algebraMap K E (c.coeff (p.natDegree - 1))) = 0 := by
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul]
    show _ • (HasCanonicalLocalResidueKStar.dataKStar v0).res _ = 0
    rw [hε, hC1, smul_zero]
  rw [hres, _root_.map_zero]

end P1Tower
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.AlgebraicCurve.P1Tower"

open _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero.Polynomial in
theorem solution
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) {m : ℕ} (hm : 2 ≤ m) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p ^ m
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 :=
  AlgebraicCurve.P1Tower.trace_localResidue_finitePlace_div_pow_eq_zero K p hp.natDegree_pos hmon hp hc hm

end S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_div_pow_eq_zero (solution)
