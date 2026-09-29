-- Prove2me | solution 1 for AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/9f4f5d07-b3d2-5b73-addf-0040dc8f2e92

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
end AlgebraicCurve
namespace Classical
p2m_export "Classical" "choose_spec by_cases choose not_not not_forall"
p2m_open "Classical"
end Classical
namespace CongruenceSubgroup
p2m_open "CongruenceSubgroup"
end CongruenceSubgroup
namespace IntermediateField
p2m_export "IntermediateField" "toAlgebra inclusion_injective map_le_iff_le_comap mk val isIntegral_iff topEquiv_apply lift inclusion ext bot_eq_top_iff_finrank_eq_one equivOfEq algebraMap_apply smul_def adjoin mem_inf mk.injEq comap topEquiv mem_top adjoinRootEquivAdjoin restrictScalars rec adjoinRootEquivAdjoin_apply_root coe_smul AdjoinSimple.coe_gen map_sup mem_bot mem_map smul_mem restrict map"
p2m_open "IntermediateField"
end IntermediateField
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "mem_primesOverFinset_iff HeightOneSpectrum.valuationSubringAtPrime HeightOneSpectrum.valuation_of_algebraMap HeightOneSpectrum.intValuation_le_pow_iff_mem HeightOneSpectrum.asIdeal rec HeightOneSpectrum.intValuation_ne_zero HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring HeightOneSpectrum.ext mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
namespace IsLocalRing
p2m_export "IsLocalRing" "rec ResidueField maximalIdeal residue_eq_zero_iff mem_maximalIdeal ResidueField.mapEquiv residue_surjective residue_ne_zero_iff_isUnit of_injective ResidueField.algebraMap_eq residue"
p2m_open "IsLocalRing"
end IsLocalRing
namespace KaehlerDifferential
p2m_export "KaehlerDifferential" "D map"
p2m_open "KaehlerDifferential"
end KaehlerDifferential
namespace ModularCurve
namespace KwNo6Pin
end ModularCurve.KwNo6Pin
namespace ModularCurve
namespace KwNo6Section
end ModularCurve.KwNo6Section
namespace ModularCurve
namespace Ldgr35Cs
end ModularCurve.Ldgr35Cs
namespace ModularCurve
namespace Ldgr36Rc
end ModularCurve.Ldgr36Rc
namespace ModularCurve
namespace Ldgr36Si
end ModularCurve.Ldgr36Si
namespace ModularCurve
namespace Lg37
end ModularCurve.Lg37
namespace ModularCurve
namespace Ldgr37Ch
end ModularCurve.Ldgr37Ch
namespace ModularCurve
namespace Ldgr39Hf
end ModularCurve.Ldgr39Hf
namespace ModularCurve
namespace Mp72a102T3
end ModularCurve.Mp72a102T3
namespace Module
p2m_export "Module" "Finite.of_finite finrank_zero_of_subsingleton Injective support Basis.span equiv Finite.equiv rec finrank_eq_card_basis finrank mk Dual finrank_self Finite.of_injective restrictScalars finrank_zero_iff Basis.span_apply Finite.of_submodule_quotient finrank_pos finrank_prod mem_support_iff Basis"
p2m_open "Module"
end Module
namespace Mp72a101T2
end Mp72a101T2
namespace Mp72a102T1
end Mp72a102T1
namespace Mp72a102T2
end Mp72a102T2
namespace Mp72a103T2
end Mp72a103T2
namespace Pointwise
p2m_open "Pointwise"
end Pointwise
namespace Polynomial
p2m_export "Polynomial" "C X support derivative_map aeval_def leadingCoeff algebraMap_eq aeval basisMonomials ext_iff degree mapEquiv factor toSubring map degree_C Monic comp natDegree_X_pow coe_mul algHom_ext sum coe_smul Separable leadingCoeff_C natDegree transcendental_X X_ne_zero rec coe_zero natDegree_lt_natDegree leadingCoeff_mul mem_support_iff coe_add derivative degree_sub_lt algebraMap_apply coe_basisMonomials eval_map ext degree_eq_natDegree funext isUnit_iff ring degree_mul aeval_algebraMap_apply leadingCoeff_ne_zero eval monomial_one_right_eq_X_pow"
p2m_open "Polynomial"
end Polynomial
namespace RationalFunctionField
end RationalFunctionField
namespace WithZero
p2m_export "WithZero" "coe_add map coe_mul exp_lt_exp log_exp map' exp_ne_zero log exp exp_zero log_mul lift exp_le_exp exp_log"
p2m_open "WithZero"
end WithZero

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback"
p2m_open "AlgebraicCurve.Divisor"

variable {K F}

end Divisor

namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "mk mk_surjective"
p2m_open "AlgebraicCurve.Pic0"

variable {K F}

end Pic0

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

p2m_open_scoped "Pointwise P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Pointwise"

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback"
p2m_open "AlgebraicCurve.Divisor"

p2m_open_scoped "Pointwise P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Pointwise"

variable {K F}

end Divisor

namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "mk mk_surjective"
p2m_open "AlgebraicCurve.Pic0"

p2m_open_scoped "Pointwise P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Pointwise"

variable {K F}

end Pic0

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section

p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
p2m_export "AlgebraicCurve.IsCurveOver" "finite_residueField deg_eq_one_of_isAlgClosed mk rec"
p2m_open "AlgebraicCurve.IsCurveOver"

variable {K F}

end IsCurveOver

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable {K F}
variable (v : Place K F)

end Place

variable {K F}

variable (K F)

end AlgebraicCurve

namespace ModularCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"

end ModularCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

namespace ModularCurve

end ModularCurve

end
end

end

section
section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"
namespace ModularCurve
namespace Lg37
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

abbrev lg37_completion (v : Place K F) : Type _ :=
  AdicCompletion (IsLocalRing.maximalIdeal v.toValuationSubring) v.toValuationSubring
end CompletionCarrier
end ModularCurve.Lg37
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"
namespace ModularCurve
namespace Lg37
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lg37_residueHat (v : Place K F) :
    lg37_completion v →+* v.ResidueField :=
  (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal v.toValuationSubring)).toRingHom
end CompletionCarrier
end ModularCurve.Lg37
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"
namespace ModularCurve
namespace Lg37
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem lg37_residueHat_algebraMap (v : Place K F) (x : v.toValuationSubring) :
    lg37_residueHat v
        (algebraMap v.toValuationSubring (lg37_completion v) x)
      = IsLocalRing.residue v.toValuationSubring x := rfl
end CompletionCarrier
end ModularCurve.Lg37
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"
namespace ModularCurve
namespace Lg37
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Ldgr36Si
open ModularCurve.Ldgr36Rc
open ModularCurve.Ldgr35Cs
section CompletionCarrier
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

structure Lg37CompletionSection (v : Place K F) where

  lift : v.ResidueField →ₐ[K] lg37_completion v

  residueHat_lift : ∀ a, lg37_residueHat v (lift a) = a
end CompletionCarrier
end ModularCurve.Lg37
end

end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
private theorem _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩

p2m_export "AlgebraicCurve.Place" "mem_iff_ord_nonneg"
theorem exists_ord_pos : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨(π : F), ?_, ?_⟩
  · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  · rw [v.ord_coe_irreducible hπ]
    exact one_pos

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

private theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

private theorem _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'

  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)

  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  letI : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  letI : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : _root_.IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

p2m_export "AlgebraicCurve.Place" "comap_algebraMap_ne_top"
variable {w} in

theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg (algebraMap_ne_zero hf)

variable {w} in

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
    (hmem : f ∈ w.toValuationSubring.comap (algebraMap F F')) :
    IsUnit (⟨f, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) ↔
      w.ord (algebraMap F F' f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : w.ord (algebraMap F F' f) + w.ord (algebraMap F F' (b : F)) = 0 := by
      rw [← w.ord_mul (algebraMap_ne_zero hf) (algebraMap_ne_zero hbne), ← map_mul, hb',
        map_one, w.ord_one]
    have h1 : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ w.ord (algebraMap F F' (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ w.toValuationSubring.comap (algebraMap F F') :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, w.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

private theorem _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
    ∃ f : F, f ≠ 0 ∧ 0 < w.ord (algebraMap F F' f) := by
  have h := w.comap_algebraMap_ne_top (F := F)
  rw [ne_eq, SetLike.ext_iff, not_forall] at h
  obtain ⟨g, hg⟩ := h
  simp only [ValuationSubring.mem_top, iff_true] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (zero_mem _)
  refine ⟨g⁻¹, inv_ne_zero hg0, ?_⟩
  rw [map_inv₀, w.ord_inv]
  have := (mem_comap_iff_ord_nonneg hg0).not.mp hg
  omega

p2m_export "AlgebraicCurve.Place" "exists_ord_algebraMap_pos"
variable [Algebra.IsIntegral F F']

private theorem ramificationIndex_set_nonempty :
    {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}.Nonempty := by
  obtain ⟨f, hf0, hf⟩ := w.exists_ord_algebraMap_pos (F := F)
  exact ⟨(w.ord (algebraMap F F' f)).toNat, by omega, f, hf0, by omega⟩

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap w hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx

  obtain ⟨c, hc⟩ := w.ramificationIndex_dvd_ord (F := F) hf
  have hnonneg : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (ramificationIndex (F := F) w : ℤ) * c ≤ (ramificationIndex (F := F) w : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩

  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : w.ord (algebraMap F F' (f / g ^ n)) = 0 := by
    have hkey : algebraMap F F' (f / g ^ n)
        = algebraMap F F' f * (algebraMap F F' g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F F' g) n,
        ← _root_.zpow_neg]
    rw [hkey, w.ord_mul (algebraMap_ne_zero hf) (zpow_ne_zero _ (algebraMap_ne_zero hg0)),
      w.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : w.toValuationSubring.comap (algebraMap F F')) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : w.toValuationSubring.comap (algebraMap F F')) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

end RestrictDef

end Restrict

end Place

end AlgebraicCurve

end
end

end

section
section
set_option autoImplicit false
noncomputable section
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback"
p2m_open "AlgebraicCurve.Divisor"
section Pullback
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

theorem degree_eq_sum_support (D : Divisor K F) :
    degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  rw [degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl
end Pullback
end Divisor
end AlgebraicCurve
end

end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

scoped instance : Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

def placeInfty : Place K (RatFunc K) where
  toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
  algebraMap_mem' a := by
    rw [Valuation.mem_valuationSubring_iff]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' :=
    (Valuation.valuationSubring_isDiscreteValuationRing
      (RatFunc.inftyValuation K)).toIsPrincipalIdealRing

@[scoped simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl

theorem inftyValuation_isEquiv_adicValuation :
    (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  (placeInfty K).isEquiv_adicValuation_of_valuationSubring_eq rfl

end PlaceInfty

variable {K}

theorem eq_ofHeightOneSpectrum_or_eq_placeInfty [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

section ResidueDegree

variable (K)

end ResidueDegree

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

theorem deg_placeInfty : (placeInfty K).deg = 1 := by
  have hbij : Function.Bijective (Algebra.ofId K (placeInfty K).ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K ((placeInfty K).ResidueField)).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K
        ((Valuation.mem_valuationSubring_iff _ _).mp hx)
      refine ⟨c, ?_⟩
      show IsLocalRing.residue _ (algebraMap K (placeInfty K).toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      show (placeInfty K).adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← (inftyValuation_isEquiv_adicValuation K).lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, _root_.map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end DegInfty

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private def _root_.AlgebraicCurve.Place.uniformizerSubring : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

p2m_export "AlgebraicCurve.Place" "uniformizerSubring"
@[scoped simp]
private theorem _root_.AlgebraicCurve.Place.coe_uniformizerSubring : (v.uniformizerSubring : F) = v.uniformizer := rfl

p2m_export "AlgebraicCurve.Place" "coe_uniformizerSubring"
private theorem _root_.AlgebraicCurve.Place.irreducible_uniformizerSubring : Irreducible v.uniformizerSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

p2m_export "AlgebraicCurve.Place" "irreducible_uniformizerSubring"
private theorem _root_.AlgebraicCurve.Place.uniformizerSubring_mem_maximalIdeal :
    v.uniformizerSubring ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
  (IsLocalRing.mem_maximalIdeal _).mpr v.irreducible_uniformizerSubring.not_isUnit

p2m_export "AlgebraicCurve.Place" "uniformizerSubring_mem_maximalIdeal"
private theorem _root_.AlgebraicCurve.Place.uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  v.uniformizerSubring.2

p2m_export "AlgebraicCurve.Place" "uniformizer_mem"
private def _root_.AlgebraicCurve.Place.simplePoleSubmodule : Submodule K F where
  carrier := {f | v.uniformizer * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf

p2m_export "AlgebraicCurve.Place" "simplePoleSubmodule"
@[scoped simp]
theorem mem_simplePoleSubmodule {f : F} :
    f ∈ v.simplePoleSubmodule ↔ v.uniformizer * f ∈ v.toValuationSubring := Iff.rfl

private theorem _root_.AlgebraicCurve.Place.mem_simplePoleSubmodule_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    f ∈ v.simplePoleSubmodule :=
  mul_mem v.uniformizer_mem hf

p2m_export "AlgebraicCurve.Place" "mem_simplePoleSubmodule_of_mem"
private def _root_.AlgebraicCurve.Place.simplePoleMulUniformizer : v.simplePoleSubmodule →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer * ((c • f : v.simplePoleSubmodule) : F)
        = ((c • ⟨v.uniformizer * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]

p2m_export "AlgebraicCurve.Place" "simplePoleMulUniformizer"
private def _root_.AlgebraicCurve.Place.simplePoleResidueAux : v.simplePoleSubmodule →ₗ[K] v.ResidueField :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap
    ∘ₗ v.simplePoleMulUniformizer

p2m_export "AlgebraicCurve.Place" "simplePoleResidueAux"
theorem simplePoleResidueAux_apply (f : v.simplePoleSubmodule) :
    v.simplePoleResidueAux f = IsLocalRing.residue _ ⟨v.uniformizer * f.1, f.2⟩ := rfl

private theorem _root_.AlgebraicCurve.Place.simplePoleResidueAux_eq_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.simplePoleResidueAux ⟨f, v.mem_simplePoleSubmodule_of_mem hf⟩ = 0 := by
  rw [simplePoleResidueAux_apply, IsLocalRing.residue_eq_zero_iff]

  have hmul : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [hmul]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal

p2m_export "AlgebraicCurve.Place" "simplePoleResidueAux_eq_zero_of_mem"
private def _root_.AlgebraicCurve.Place.localResidueExtend : F →ₗ[K] v.ResidueField :=
  v.simplePoleResidueAux.exists_extend.choose

p2m_export "AlgebraicCurve.Place" "localResidueExtend"
private theorem _root_.AlgebraicCurve.Place.localResidueExtend_apply_of_mem {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    v.localResidueExtend f = v.simplePoleResidueAux ⟨f, hf⟩ :=
  congrArg (fun φ => φ (⟨f, hf⟩ : v.simplePoleSubmodule))
    v.simplePoleResidueAux.exists_extend.choose_spec

p2m_export "AlgebraicCurve.Place" "localResidueExtend_apply_of_mem"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"

namespace Mp72a102T1

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
open ModularCurve.Lg37 ModularCurve.Ldgr37Ch
open Mp72a101T2

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable abbrev mp72a102_t1_maximalIdealHat (v : Place K F) :
    Ideal (lg37_completion v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (lg37_completion v))

theorem mp72a102_t1_isScalarTower (v : Place K F) :
    IsScalarTower K v.toValuationSubring (lg37_completion v) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem mp72a102_t1_isAdicComplete_maximalIdealHat (v : Place K F) :
    IsAdicComplete (mp72a102_t1_maximalIdealHat v) (lg37_completion v) :=
  (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal v.toValuationSubring)
      (lg37_completion v)).mpr
    (AdicCompletion.isAdicComplete
      (IsPrincipalIdealRing.principal
        (IsLocalRing.maximalIdeal v.toValuationSubring)).fg)

theorem mp72a102_t1_henselianRing_completion (v : Place K F) :
    HenselianRing (lg37_completion v) (mp72a102_t1_maximalIdealHat v) :=
  letI := mp72a102_t1_isAdicComplete_maximalIdealHat v
  IsAdicComplete.henselianRing (lg37_completion v) (mp72a102_t1_maximalIdealHat v)

theorem mp72a102_t1_maximalIdealHat_le_ker_residueHat (v : Place K F) :
    mp72a102_t1_maximalIdealHat v ≤ RingHom.ker (lg37_residueHat v) :=
  Ideal.map_le_iff_le_comap.mpr fun s hs => by
    rw [Ideal.mem_comap, RingHom.mem_ker, lg37_residueHat_algebraMap]
    exact (IsLocalRing.residue_eq_zero_iff s).mpr hs

theorem mp72a102_t1_exists_completion_root_of_residue_root
    (v : Place K F) {p : K[X]} (hpmon : p.Monic) (hpsep : p.Separable)
    {rbar : v.ResidueField} (hrbar : Polynomial.aeval rbar p = 0) :
    ∃ α : lg37_completion v,
      Polynomial.aeval α p = 0 ∧ lg37_residueHat v α = rbar := by
  classical
  haveI _htower : IsScalarTower K v.toValuationSubring (lg37_completion v) :=
    mp72a102_t1_isScalarTower v

  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) rbar

  have hapI : Polynomial.aeval a p ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h1 : IsLocalRing.residue v.toValuationSubring (Polynomial.aeval a p)
        = Polynomial.aeval rbar p := by
      rw [← ha, ← IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.aeval_algebraMap_apply]
    rw [h1, hrbar]

  have hapIhat : Polynomial.aeval
      (algebraMap v.toValuationSubring (lg37_completion v) a) p
        ∈ mp72a102_t1_maximalIdealHat v := by
    rw [Polynomial.aeval_algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hapI

  have hfeval : ∀ x : lg37_completion v,
      (p.map (algebraMap K (lg37_completion v))).eval x = Polynomial.aeval x p :=
    fun x => by rw [Polynomial.eval_map, ← Polynomial.aeval_def]
  have hfderiv :
      (p.map (algebraMap K (lg37_completion v))).derivative.eval
          (algebraMap v.toValuationSubring (lg37_completion v) a)
        = Polynomial.aeval
            (algebraMap v.toValuationSubring (lg37_completion v) a)
            (Polynomial.derivative p) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]

  obtain ⟨u, w, huw⟩ := hpsep
  have hunit : IsUnit (Ideal.Quotient.mk (mp72a102_t1_maximalIdealHat v)
      ((p.map (algebraMap K (lg37_completion v))).derivative.eval
        (algebraMap v.toValuationSubring (lg37_completion v) a))) := by
    rw [hfderiv]
    set a₀ := algebraMap v.toValuationSubring (lg37_completion v) a
    have h1 : Polynomial.aeval a₀ u * Polynomial.aeval a₀ p
        + Polynomial.aeval a₀ w * Polynomial.aeval a₀ (Polynomial.derivative p)
        = 1 := by
      have h0 := congrArg (Polynomial.aeval (R := K) a₀) huw
      simpa only [map_add, map_mul, map_one] using h0
    have h2 := congrArg (Ideal.Quotient.mk (mp72a102_t1_maximalIdealHat v)) h1
    rw [map_add, map_mul, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hapIhat, mul_zero, zero_add] at h2
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans h2)

  obtain ⟨α, hαroot, hαnear⟩ :=
    (mp72a102_t1_henselianRing_completion v).is_henselian
      (p.map (algebraMap K (lg37_completion v))) (hpmon.map _)
      (algebraMap v.toValuationSubring (lg37_completion v) a)
      (by rw [hfeval]; exact hapIhat) hunit
  refine ⟨α, ?_, ?_⟩
  · rw [← hfeval]
    exact hαroot
  ·
    have h0 : lg37_residueHat v
        (α - algebraMap v.toValuationSubring (lg37_completion v) a) = 0 :=
      RingHom.mem_ker.mp (mp72a102_t1_maximalIdealHat_le_ker_residueHat v hαnear)
    have heq : lg37_residueHat v α
        = lg37_residueHat v
            (algebraMap v.toValuationSubring (lg37_completion v) a) := by
      rwa [map_sub, sub_eq_zero] at h0
    rw [heq, lg37_residueHat_algebraMap, ha]

end Engine
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section FinitePlace

variable (K : Type*) [Field K]

end FinitePlace
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section RatWs

end RatWs
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end Mp72a102T1
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace Mp72a102T2
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
open ModularCurve.Lg37 ModularCurve.Ldgr39Hf ModularCurve.Ldgr35Cs
open Mp72a101T2
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
section ResidueCalculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a102_t2_residueHat_algebraMap_base (v : Place K F) (c : K) :
    lg37_residueHat v (algebraMap K (lg37_completion v) c)
      = algebraMap K v.ResidueField c := by
  have h : algebraMap K (lg37_completion v) c
      = algebraMap v.toValuationSubring (lg37_completion v)
          (algebraMap K v.toValuationSubring c) := rfl
  rw [h, lg37_residueHat_algebraMap v]
  rfl
end ResidueCalculus
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Mp72a102T2
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace Mp72a102T2
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
open ModularCurve.Lg37 ModularCurve.Ldgr39Hf ModularCurve.Ldgr35Cs
open Mp72a101T2
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
section ResidueCalculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def mp72a102_t2_residueHatAlgHom (v : Place K F) :
    lg37_completion v →ₐ[K] v.ResidueField where
  toRingHom := lg37_residueHat v
  commutes' := mp72a102_t2_residueHat_algebraMap_base v
end ResidueCalculus
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Mp72a102T2
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback"
p2m_open "AlgebraicCurve.Divisor"

end Divisor
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback"
p2m_open "AlgebraicCurve.Divisor"

end Divisor
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
variable (w : Place K F')

scoped instance : IsLocalHom (restrictInclusion F w) where
  map_nonunit a ha := by

    have hord : w.ord (algebraMap F F' (a : F)) = 0 := by
      have h := w.ord_coe_unit ha.unit
      rwa [IsUnit.unit_spec, coe_restrictInclusion] at h

    have ha0 : (a : F) ≠ 0 := by
      rintro h0
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
      have hb' : algebraMap F F' (a : F) * (b : F') = 1 := congrArg Subtype.val hb
      rw [h0, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    exact (isUnit_mk_comap_iff ha0 a.2).mpr hord
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit

p2m_export "AlgebraicCurve.Place" "isUnit_mk_of_ord_eq_zero"
private theorem _root_.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)

p2m_export "AlgebraicCurve.Place" "residue_ne_zero_of_ord_eq_zero"
private def _root_.AlgebraicCurve.Place.IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

p2m_export "AlgebraicCurve.Place" "IsRational"
private def _root_.AlgebraicCurve.Place.residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)

p2m_export "AlgebraicCurve.Place" "residueInv"
private theorem _root_.AlgebraicCurve.Place.algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

p2m_export "AlgebraicCurve.Place" "algebraMap_residueInv"
open _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in

private def _root_.AlgebraicCurve.Place.evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (residue v.toValuationSubring ⟨f, hf⟩)
  else 0

p2m_export "AlgebraicCurve.Place" "evalAt"
private theorem _root_.AlgebraicCurve.Place.evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) :=
  dif_pos hf

p2m_export "AlgebraicCurve.Place" "evalAt_of_mem"
private theorem _root_.AlgebraicCurve.Place.algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

p2m_export "AlgebraicCurve.Place" "algebraMap_evalAt"
private theorem _root_.AlgebraicCurve.Place.evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_of_ord_nonneg hf h.ge)
  rw [h0, _root_.map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm

p2m_export "AlgebraicCurve.Place" "evalAt_ne_zero"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback"
p2m_open "AlgebraicCurve.Divisor"

end Divisor
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace WeilDatum

end WeilDatum
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero CongruenceSubgroup P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.CongruenceSubgroup"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}

namespace Divisor p2m_export "AlgebraicCurve.Divisor" "degree degree_single principal smul_def smul_apply pullback pullback_apply degree_pullback" end Divisor
p2m_open_scoped "AlgebraicCurve.Divisor" in
theorem Divisor.degree_nonneg_of_nonneg [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [Divisor.degree_eq_sum_support]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero CongruenceSubgroup P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.CongruenceSubgroup"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}

theorem lSpace_eq_bot_of_degree_neg [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0

  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero CongruenceSubgroup P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.CongruenceSubgroup"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {D E : Divisor K F}
theorem ell_eq_zero_of_degree_neg [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (placeInfty K).ord f = 0 := by
  rw [(placeInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl
end PlaceInfty
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_intDegree_mul {f : RatFunc K} (hf : f ≠ 0) :
    (placeInfty K).ord f = f.intDegree * (placeInfty K).ord (RatFunc.X) := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)

  have hpoly : ∀ q : K[X], q ≠ 0 →
      (placeInfty K).ord (algebraMap K[X] (RatFunc K) q)
        = (q.natDegree : ℤ) * (placeInfty K).ord (RatFunc.X) := by
    intro q hq
    have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
    have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
    have hXpow : (RatFunc.X : RatFunc K) ^ q.natDegree ≠ 0 := pow_ne_zero _ hX

    have hXpoly : (RatFunc.X : RatFunc K) ^ q.natDegree
        = algebraMap K[X] (RatFunc K) (Polynomial.X ^ q.natDegree) := by
      rw [map_pow, RatFunc.algebraMap_X]
    have hdeg : (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree).intDegree = 0 := by
      rw [RatFunc.intDegree_div hq' hXpow, RatFunc.intDegree_polynomial, hXpoly,
        RatFunc.intDegree_polynomial, natDegree_X_pow, sub_self]
    have hne : algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree ≠ 0 :=
      div_ne_zero hq' hXpow
    have h0 := ord_placeInfty_eq_zero_of_intDegree_eq_zero K hne hdeg
    have hsplit : algebraMap K[X] (RatFunc K) q
        = (algebraMap K[X] (RatFunc K) q / RatFunc.X ^ q.natDegree)
          * RatFunc.X ^ q.natDegree :=
      (div_mul_cancel₀ _ hXpow).symm
    rw [hsplit, (placeInfty K).ord_mul hne hXpow, h0, zero_add, ← zpow_natCast,
      (placeInfty K).ord_zpow]
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.num_ne_zero hf)
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr f.denom_ne_zero
  rw [show f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ by
      rw [← div_eq_mul_inv, f.num_div_denom],
    (placeInfty K).ord_mul hnum' (inv_ne_zero hden'), (placeInfty K).ord_inv,
    hpoly _ (RatFunc.num_ne_zero hf), hpoly _ f.denom_ne_zero, ← div_eq_mul_inv,
    RatFunc.intDegree_div hnum' hden', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring
end PlaceInfty
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]
section PlaceInfty
variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_X : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero

  have hneg : (placeInfty K).ord (RatFunc.X : RatFunc K) < 0 := by
    by_contra h
    have hmem : (RatFunc.X : RatFunc K) ∈ (placeInfty K).toValuationSubring :=
      (placeInfty K).mem_of_ord_nonneg hX (not_lt.mp h)
    rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
      RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hX,
      RatFunc.intDegree_X, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hmem
    omega

  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (placeInfty K).toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hdvd : (placeInfty K).ord (RatFunc.X : RatFunc K) ∣ 1 := by
    rw [← (placeInfty K).ord_coe_irreducible hπ, ord_placeInfty_eq_intDegree_mul K hπ0]
    exact Dvd.intro_left _ rfl
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega
end PlaceInfty
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
section Chart
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

private def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw
end Chart
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
section Chart
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)
omit [IsDedekindDomain R] [IsFractionRing R F] in

private theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _
end Chart
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private def _root_.AlgebraicCurve.Place.poleSubmodule (n : ℕ) : Submodule K F where
  carrier := {f | v.uniformizer ^ n * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer ^ n * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf

p2m_export "AlgebraicCurve.Place" "poleSubmodule"
@[scoped simp]
theorem mem_poleSubmodule {n : ℕ} {f : F} :
    f ∈ v.poleSubmodule n ↔ v.uniformizer ^ n * f ∈ v.toValuationSubring := Iff.rfl

private theorem _root_.AlgebraicCurve.Place.uniformizer_pow_ne_zero (n : ℕ) : (v.uniformizer ^ n : F) ≠ 0 :=
  pow_ne_zero n v.uniformizer_ne_zero

p2m_export "AlgebraicCurve.Place" "uniformizer_pow_ne_zero"
private theorem _root_.AlgebraicCurve.Place.ord_uniformizer_pow (n : ℕ) : v.ord (v.uniformizer ^ n) = (n : ℤ) := by
  rw [show (v.uniformizer ^ n : F) = v.uniformizer ^ (n : ℤ) from (zpow_natCast _ n).symm,
    v.ord_zpow, v.ord_uniformizer, mul_one]

p2m_export "AlgebraicCurve.Place" "ord_uniformizer_pow"
@[scoped simp]
private theorem _root_.AlgebraicCurve.Place.poleSubmodule_one : v.poleSubmodule 1 = v.simplePoleSubmodule := by
  ext f; simp [mem_poleSubmodule, mem_simplePoleSubmodule]

p2m_export "AlgebraicCurve.Place" "poleSubmodule_one"
private theorem _root_.AlgebraicCurve.Place.mem_poleSubmodule_iff_ord {n : ℕ} {f : F} (hf : f ≠ 0) :
    f ∈ v.poleSubmodule n ↔ -(n : ℤ) ≤ v.ord f := by
  rw [mem_poleSubmodule, v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero n) hf),
    v.ord_mul (v.uniformizer_pow_ne_zero n) hf, v.ord_uniformizer_pow]
  omega

p2m_export "AlgebraicCurve.Place" "mem_poleSubmodule_iff_ord"
private theorem _root_.AlgebraicCurve.Place.poleSubmodule_mono : Monotone v.poleSubmodule := by
  intro m n hmn f hf
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · rw [v.mem_poleSubmodule_iff_ord hf0] at hf ⊢
    have : -(n : ℤ) ≤ -(m : ℤ) := by exact_mod_cast neg_le_neg (Nat.cast_le.mpr hmn)
    omega

p2m_export "AlgebraicCurve.Place" "poleSubmodule_mono"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

theorem gate_poleSubmodule_strictMono (v : Place K F) (n : ℕ) :
    (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule (n + 1) ∧
      (v.uniformizer ^ (n + 1))⁻¹ ∉ v.poleSubmodule n := by
  refine ⟨?_, ?_⟩
  · rw [Place.mem_poleSubmodule, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1))]
    exact one_mem _
  · rw [v.mem_poleSubmodule_iff_ord (inv_ne_zero (v.uniformizer_pow_ne_zero (n + 1))),
      v.ord_inv, v.ord_uniformizer_pow]
    omega

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

noncomputable section

p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"

p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"

namespace ModularCurve
namespace Mp72a102T3

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.ModularCurve.Lg37"

section General

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem mp72a102_t3_evalₐ_zero_depth (z : AdicCompletion I R) :
    AdicCompletion.evalₐ I 0 z = 0 := by
  haveI : Subsingleton (R ⧸ (I ^ 0)) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  exact Subsingleton.elim _ _

theorem mp72a102_t3_evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r)
      = Ideal.Quotient.mk (I ^ n) r := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of]

theorem mp72a102_t3_evalₐ_factor {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n z)
      = AdicCompletion.evalₐ I m z := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R z
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn c

theorem mp72a102_t3_exists_rep_of_evalₐ_eq_zero {n : ℕ} {z : AdicCompletion I R}
    (h : AdicCompletion.evalₐ I n z = 0) :
    ∃ w ∈ I ^ n, AdicCompletion.evalₐ I (n + 1) z = Ideal.Quotient.mk (I ^ (n + 1)) w := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) z)
  refine ⟨w, ?_, hw.symm⟩
  have hfac := mp72a102_t3_evalₐ_factor I (Nat.le_succ n) z
  rw [← hw, Ideal.Quotient.factor_mk, h] at hfac
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfac

theorem mp72a102_t3_evalₐ_succ_mul_eq_zero {n : ℕ} {r : R} (hr : r ∈ I)
    {z : AdicCompletion I R} (h : AdicCompletion.evalₐ I n z = 0) :
    AdicCompletion.evalₐ I (n + 1) (algebraMap R (AdicCompletion I R) r * z) = 0 := by
  obtain ⟨w, hw, hwz⟩ := mp72a102_t3_exists_rep_of_evalₐ_eq_zero I h
  rw [map_mul, mp72a102_t3_evalₐ_algebraMap, hwz, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, pow_succ']
  exact Ideal.mul_mem_mul hr hw

theorem mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ {z : AdicCompletion I R}
    (h : AdicCompletion.evalOneₐ I z = 0) : AdicCompletion.evalₐ I 1 z = 0 := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 z)
  have hfac := AdicCompletion.factorₐ_evalₐ_one I z
  rw [← hw, Ideal.Quotient.factor_mk, h] at hfac
  rw [← hw, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfac

end General
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Carrier

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a102_t3_evalDepth_add (v : Place K F) (n : ℕ)
    (x y : lg37_completion v) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n (x + y)
      = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n x
        + AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n y :=
  map_add _ x y

theorem mp72a102_t3_evalDepth_mul (v : Place K F) (n : ℕ)
    (x y : lg37_completion v) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n (x * y)
      = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n x
        * AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n y :=
  map_mul _ x y

theorem mp72a102_t3_residueHat_congr_of_depth_one (v : Place K F)
    {x y : lg37_completion v}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x
        = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 y) :
    lg37_residueHat v x = lg37_residueHat v y := by
  show AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring) x
      = AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring) y
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← AdicCompletion.factorₐ_evalₐ_one, h]

theorem mp72a102_t3_evalDepth_one_eq_zero_of_residueHat (v : Place K F)
    {x : lg37_completion v} (hx : lg37_residueHat v x = 0) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 :=
  mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ _ hx

theorem mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal (v : Place K F)
    {w : v.toValuationSubring} (hw : w ∈ maximalIdeal v.toValuationSubring) :
    ∃ u : v.toValuationSubring, w = v.uniformizerSubring * u := by
  rw [v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
  exact hw

theorem mp72a102_t3_exists_uniformizer_factor (v : Place K F)
    {x : lg37_completion v} (hx : lg37_residueHat v x = 0) (n : ℕ) :
    ∃ u : v.toValuationSubring,
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (x - algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * algebraMap v.toValuationSubring (lg37_completion v) u) = 0 := by
  rcases n with _ | n
  · exact ⟨0, mp72a102_t3_evalₐ_zero_depth _ _⟩
  · obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1) x)
    have h1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 :=
      mp72a102_t3_evalDepth_one_eq_zero_of_residueHat v hx
    have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
      (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)) x
    rw [← hw, Ideal.Quotient.factor_mk, h1] at hfac
    have hwm : w ∈ maximalIdeal v.toValuationSubring := by
      have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hfac
      rwa [pow_one] at hmem
    obtain ⟨u, hu⟩ := mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal v hwm
    refine ⟨u, ?_⟩
    rw [map_sub, map_mul, mp72a102_t3_evalₐ_algebraMap, mp72a102_t3_evalₐ_algebraMap,
      ← map_mul, ← hu, ← hw, sub_self]

theorem mp72a102_t3_sigma_taylor_expansion (v : Place K F)
    (S : Lg37CompletionSection v) (n : ℕ) (x : lg37_completion v) :
    ∃ a : ℕ → v.ResidueField,
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (x - ∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
  induction n generalizing x with
  | zero => exact ⟨fun _ => 0, mp72a102_t3_evalₐ_zero_depth _ _⟩
  | succ n ih =>
    have hres : lg37_residueHat v (x - S.lift (lg37_residueHat v x)) = 0 := by
      rw [map_sub, S.residueHat_lift, sub_self]
    obtain ⟨u, hu⟩ := mp72a102_t3_exists_uniformizer_factor v hres (n + 1)
    obtain ⟨a, ha⟩ := ih (algebraMap v.toValuationSubring (lg37_completion v) u)
    have hshift := mp72a102_t3_evalₐ_succ_mul_eq_zero
      (maximalIdeal v.toValuationSubring) v.uniformizerSubring_mem_maximalIdeal ha
    refine ⟨fun i => Nat.rec (motive := fun _ => v.ResidueField)
      (lg37_residueHat v x) (fun j _ => a j) i, ?_⟩
    rw [Finset.sum_range_succ']
    show AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
        (x - ((∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ (i + 1))
          + S.lift (lg37_residueHat v x)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ 0)) = 0
    have hsum : ∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ (i + 1)
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, pow_zero, mul_one]
    have hdecomp : x - (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring
          * ∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
          + S.lift (lg37_residueHat v x))
        = (x - S.lift (lg37_residueHat v x)
            - algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring
              * algebraMap v.toValuationSubring (lg37_completion v) u)
          + algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
            * (algebraMap v.toValuationSubring (lg37_completion v) u
              - ∑ i ∈ Finset.range n, S.lift (a i)
                * algebraMap v.toValuationSubring (lg37_completion v)
                    v.uniformizerSubring ^ i) := by
      ring
    rw [hdecomp, map_add, hu, hshift, add_zero]

end Carrier
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section RatProduction

p2m_open "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a101T2"

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end RatProduction
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end ModularCurve.Mp72a102T3
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
set_option maxHeartbeats 3200000
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.ModularCurve.Lg37 Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IntermediateField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IntermediateField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a102T1 P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a102T2"
namespace ModularCurve
namespace KwNo6Section
section GenericIso
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

noncomputable def residueFieldAdjoinRootEquiv {ᾱ : v.ResidueField} (hint : IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) :
    AdjoinRoot (minpoly K ᾱ) ≃ₐ[K] v.ResidueField :=
  (adjoinRootEquivAdjoin K hint).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
end GenericIso
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end ModularCurve.KwNo6Section
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
set_option maxHeartbeats 3200000
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.ModularCurve.Lg37 Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IntermediateField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IntermediateField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a102T1 P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a102T2"
namespace ModularCurve
namespace KwNo6Section
section GenericIso
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem residueFieldAdjoinRootEquiv_root {ᾱ : v.ResidueField} (hint : IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) :
    residueFieldAdjoinRootEquiv v hint htop (AdjoinRoot.root (minpoly K ᾱ)) = ᾱ := by
  have hgen := adjoinRootEquivAdjoin_apply_root K hint

  simp only [residueFieldAdjoinRootEquiv, AlgEquiv.trans_apply, hgen,
    IntermediateField.topEquiv_apply]
  exact AdjoinSimple.coe_gen K ᾱ
end GenericIso
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end ModularCurve.KwNo6Section
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
set_option maxHeartbeats 3200000
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.ModularCurve.Lg37 Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IntermediateField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IntermediateField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a102T1 P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Mp72a102T2"
namespace ModularCurve
namespace KwNo6Section
section GenericSection
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

noncomputable def sectionOfPrimitiveRoot {ᾱ : v.ResidueField} (hint : IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) (αhat : lg37_completion v)
    (hroot : (aeval αhat) (minpoly K ᾱ) = 0)
    (hres : lg37_residueHat v αhat = ᾱ) :
    Lg37CompletionSection v where
  lift :=
    (AdjoinRoot.liftAlgHom (minpoly K ᾱ) (Algebra.ofId K (lg37_completion v)) αhat
      (by rw [aeval_def] at hroot; exact hroot)).comp
      (residueFieldAdjoinRootEquiv v hint htop).symm.toAlgHom
  residueHat_lift a := by

    have hres' : lg37_residueHat v αhat
        = residueFieldAdjoinRootEquiv v hint htop (AdjoinRoot.root (minpoly K ᾱ)) :=
      hres.trans (residueFieldAdjoinRootEquiv_root v hint htop).symm
    have hkey : (mp72a102_t2_residueHatAlgHom v).comp
          (AdjoinRoot.liftAlgHom (minpoly K ᾱ) (Algebra.ofId K (lg37_completion v)) αhat
            (by rw [aeval_def] at hroot; exact hroot))
        = (residueFieldAdjoinRootEquiv v hint htop).toAlgHom := by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root]
      exact hres'
    have h1 := DFunLike.congr_fun hkey ((residueFieldAdjoinRootEquiv v hint htop).symm a)
    rw [AlgHom.comp_apply] at h1
    have h2 : (residueFieldAdjoinRootEquiv v hint htop).toAlgHom
        ((residueFieldAdjoinRootEquiv v hint htop).symm a) = a :=
      (residueFieldAdjoinRootEquiv v hint htop).apply_symm_apply a
    exact h1.trans h2
end GenericSection
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end ModularCurve.KwNo6Section
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
noncomputable section
p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_sub_evalAt_pos (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  ·

    exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega
p2m_export "AlgebraicCurve.Place" "ord_sub_evalAt_pos"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one (h : v.deg = 1) : v.IsRational := by
  intro x
  have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
  have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
    rw [hbot]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx
p2m_export "AlgebraicCurve.Place" "isRational_of_deg_eq_one"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mk_mem_maximalIdeal_iff {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring
      ↔ f = 0 ∨ 0 < v.ord f := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hu
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases lt_or_eq_of_le (v.ord_nonneg_of_mem hf) with h | h
      · exact h
      ·
        exfalso
        apply hu
        rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
        show v.adicValuation f = 1
        rw [v.adicValuation_eq_exp_neg_ord hf0, ← h, neg_zero, WithZero.exp_zero]
  · intro h hu
    have hne : f ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
    have h0 : v.ord f = 0 := by
      obtain ⟨u, hu'⟩ := hu
      have hcoe : f = ((u : v.toValuationSubring) : F) := by rw [hu']
      rw [hcoe]; exact v.ord_coe_unit u
    rcases h with rfl | hpos
    · exact hne rfl
    · omega
p2m_export "AlgebraicCurve.Place" "mk_mem_maximalIdeal_iff"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem one_le_deg [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  haveI : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lSpaceShiftEquiv (D : Divisor K F) {g : F} (hg : g ≠ 0)
    {Dg : Divisor K F} (hDg : ∀ v, Dg v = v.ord g) :
    LSpace D ≃ₗ[K] LSpace (D + Dg) where
  toFun h := ⟨(h : F) * g⁻¹, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (h : F) 0 with hh0 | hh0
    · left; rw [hh0, zero_mul]
    · right; intro v
      rw [Finsupp.add_apply, hDg, v.ord_mul hh0 (inv_ne_zero hg), v.ord_inv]
      have := (mem_lSpace_iff_ord.mp h.2).resolve_left hh0 v
      linarith⟩
  invFun k := ⟨(k : F) * g, by
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (k : F) 0 with hk0 | hk0
    · left; rw [hk0, zero_mul]
    · right; intro v
      have := (mem_lSpace_iff_ord.mp k.2).resolve_left hk0 v
      rw [Finsupp.add_apply, hDg] at this
      rw [v.ord_mul hk0 hg]
      linarith⟩
  map_add' h₁ h₂ := by apply Subtype.ext; push_cast; ring
  map_smul' c h := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    ring
  left_inv h := by
    apply Subtype.ext
    show (h : F) * g⁻¹ * g = (h : F)
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  right_inv k := by
    apply Subtype.ext
    show (k : F) * g * g⁻¹ = (k : F)
    rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable {D E : Divisor K F}

variable (K F)

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone

  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega

  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega

  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring

  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega

  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega

  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel

  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 0] valuationSubringAlgebra

section Setup

variable (v : Place K F)

scoped instance (priority := 100) : IsScalarTower v.toValuationSubring F F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Setup
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Center

variable {v : Place K F} {w : Place K F'}

end Center
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  ·
    intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  ·
    obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, _root_.map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  ·
    intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    show 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal := by

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπC : algebraMap v.toValuationSubring (integralClosureAt F' v) π ≠ 0 :=
    algebraMap_integralClosureAt_ne_zero hπ0

  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (integralClosureAt F' v))
        = Ideal.span {algebraMap v.toValuationSubring (integralClosureAt F' v) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

  have hord : w.ord (algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) π))
        = w.ramificationIndex F := by
    rw [ord_algebraMap_integralClosureAt hw, ValuationSubring.algebraMap_apply,
      v.ord_coe_irreducible hπ, mul_one]

  refine (Ideal.ramificationIdx_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

end ValuationDictionary
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

omit [FiniteDimensional F F'] in
theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y

  have hx : (x : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
    rw [← toValuationSubring_eq_of_restrict_eq hw]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := hx

  have hsP : s ∉ (fiberCenter F' v hw).asIdeal := hs
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ (fiberCenter F' v hw).asIdeal.zero_mem)
  have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hs0
  have hsord : w.ord (algebraMap (integralClosureAt F' v) F' s) = 0 := by
    have h1 : ¬ 0 < w.ord (algebraMap (integralClosureAt F' v) F' s) := by
      rw [← mem_fiberCenter_iff_ord_pos hw hs0]
      exact hsP
    have h2 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' s) :=
      w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw s)
    omega

  haveI hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
  have hst : s * t - 1 ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : s * t - 1 = -i := by linear_combination hti
    rw [h1]
    exact neg_mem hi
  refine ⟨a * t, ?_⟩

  rw [residueOfCenter_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

  have hcoe : ((toValuationSubringOfRestrictEq hw (a * t) - x : w.toValuationSubring) : F')
      = algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') := rfl
  rcases eq_or_ne (toValuationSubringOfRestrictEq hw (a * t) - x) 0 with hzero | hne
  · rw [hzero]
    exact (IsLocalRing.maximalIdeal w.toValuationSubring).zero_mem
  have hcoene : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') ≠ 0 := by
    intro h
    exact hne (by rwa [← hcoe, ZeroMemClass.coe_eq_zero] at h)

  have hfactor : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      = algebraMap (integralClosureAt F' v) F' (a * t * s - a)
          * (algebraMap (integralClosureAt F' v) F' s)⁻¹ := by
    rw [hxas, map_sub, map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, _root_.map_zero, zero_mul]
  have hdiffP : a * t * s - a ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : a * t * s - a = a * (s * t - 1) := by ring
    rw [h1]
    exact Ideal.mul_mem_left _ _ hst

  have hmem' : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      ∈ w.toValuationSubring := by
    rw [← hcoe]
    exact Subtype.coe_prop _
  rw [show (toValuationSubringOfRestrictEq hw (a * t) - x)
      = (⟨_, hmem'⟩ : w.toValuationSubring) from Subtype.ext hcoe,
    w.mem_maximalIdeal_iff_ord_pos hcoene hmem']
  rw [hfactor, w.ord_mul (by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hdiffC)
    (inv_ne_zero hsF), w.ord_inv, hsord, _root_.neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
        (fiberCenter F' v hw).asIdeal := by
  haveI := fiberCenter_liesOver hw
  rw [Ideal.inertiaDeg_algebraMap]
  show Module.finrank (w.restrict F).ResidueField w.ResidueField = _
  refine Algebra.finrank_eq_of_equiv_equiv (restrictResidueFieldEquiv hw)
    (residueFieldEquivQuotientCenter hw).symm ?_

  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]

  apply (residueFieldEquivQuotientCenter hw).injective
  rw [RingEquiv.apply_symm_apply]

  show IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw
        (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a)))
    = IsLocalRing.residue w.toValuationSubring (restrictInclusion F w a)

  refine congrArg _ (Subtype.ext ?_)
  show algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a))
    = algebraMap F F' (a : F)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  rfl

end ResidueDictionary
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Bijection

variable {v : Place K F}

end Bijection
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Assembly

variable (v : Place K F)

theorem sum_ramificationIndex_mul_inertiaDeg [HasPrincipalDivisors K F'] :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := Ideal.sum_ramification_inertia (integralClosureAt F' v) F F'
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (maximalIdeal_ne_bot v)
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v (Place.mem_fiber.mp hw)).asIdeal) ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v (Place.mem_fiber.mp hw)).isPrime,
      fiberCenter_liesOver (Place.mem_fiber.mp hw)⟩
  ·
    intro w hw w' hw' h
    exact eq_of_fiberCenter_eq (Place.mem_fiber.mp hw) (Place.mem_fiber.mp hw')
      (HeightOneSpectrum.ext h)
  ·
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      Place.mem_fiber.mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  ·
    intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter (Place.mem_fiber.mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter (Place.mem_fiber.mp hw)]

end Assembly
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

scoped instance instSumRamificationInertia {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] :
    SumRamificationInertia K F F' :=
  ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg v⟩

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
set_option maxHeartbeats 6400000
p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section
namespace ModularCurve
namespace KwNo6Pin
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def aCoeff (v : Place K F) (S : Lg37CompletionSection v)
    (n : ℕ) (x : lg37_completion v) : v.ResidueField :=
  (Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)) n
end ModularCurve.KwNo6Pin
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace Mp72a103T2
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
open ModularCurve.Lg37 ModularCurve.Mp72a102T3
open Mp72a102T2
section Calculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a103_t2_evalDepth_of_uniformizer_mul (v : Place K F) {n : ℕ}
    {z : lg37_completion v}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
        (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring * z) = 0) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n z = 0 := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1) z)
  rw [map_mul, mp72a102_t3_evalₐ_algebraMap, ← hw, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, v.irreducible_uniformizerSubring.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hw' : v.uniformizerSubring * w
      = v.uniformizerSubring * (v.uniformizerSubring ^ n * u) := by
    rw [hu, pow_succ', mul_assoc]
  have hcancel : w = v.uniformizerSubring ^ n * u :=
    mul_left_cancel₀ v.irreducible_uniformizerSubring.ne_zero hw'
  have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
    (Nat.le_succ n) z
  rw [← hw, Ideal.Quotient.factor_mk] at hfac
  rw [← hfac, Ideal.Quotient.eq_zero_iff_mem, hcancel,
    v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨u, rfl⟩
end Calculus
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Mp72a103T2
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace Mp72a103T2
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
open ModularCurve.Lg37 ModularCurve.Mp72a102T3
open Mp72a102T2
section Calculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a103_t2_lift_eq_zero_of_depth_one (v : Place K F)
    (S : Lg37CompletionSection v) {c : v.ResidueField}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 (S.lift c) = 0) :
    c = 0 := by
  have hres : lg37_residueHat v (S.lift c) = lg37_residueHat v 0 :=
    mp72a102_t3_residueHat_congr_of_depth_one v (by rw [h, map_zero])
  rwa [S.residueHat_lift, map_zero] at hres
end Calculus
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Mp72a103T2
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
p2m_open_scoped "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"
namespace Mp72a103T2
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.RationalFunctionField AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
open ModularCurve.Lg37 ModularCurve.Mp72a102T3
open Mp72a102T2
section Calculus
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mp72a103_t2_taylor_coeff_eq_zero_of_depth (v : Place K F)
    (S : Lg37CompletionSection v) :
    ∀ (n : ℕ) (a : ℕ → v.ResidueField),
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 →
      ∀ i < n, a i = 0 := by
  intro n
  induction n with
  | zero => intro a _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro a h
    have hsplit : (∑ i ∈ Finset.range (n + 1), S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
            * (∑ i ∈ Finset.range n, S.lift (a (i + 1))
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          + S.lift (a 0) := by
      rw [Finset.sum_range_succ', pow_zero, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hfac1 := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
      (show 1 ≤ n + 1 by omega)
      (∑ i ∈ Finset.range (n + 1), S.lift (a i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i)
    rw [h, map_zero] at hfac1
    have hT1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1
        (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (∑ i ∈ Finset.range n, S.lift (a (i + 1))
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)) = 0 :=
      mp72a102_t3_evalₐ_succ_mul_eq_zero (maximalIdeal v.toValuationSubring)
        v.uniformizerSubring_mem_maximalIdeal
        (mp72a102_t3_evalₐ_zero_depth (maximalIdeal v.toValuationSubring) _)
    have h1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1
        (S.lift (a 0)) = 0 := by
      have h1' := hfac1.symm
      rw [hsplit, map_add, hT1, zero_add] at h1'
      exact h1'
    have ha0 : a 0 = 0 := mp72a103_t2_lift_eq_zero_of_depth_one v S h1
    have hT : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (∑ i ∈ Finset.range n, S.lift (a (i + 1))
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
      apply mp72a103_t2_evalDepth_of_uniformizer_mul v
      have h' := h
      rw [hsplit, ha0, map_zero, add_zero] at h'
      exact h'
    have hrec := ih (fun j => a (j + 1)) hT
    intro i hi
    cases i with
    | zero => exact ha0
    | succ j => exact hrec j (Nat.lt_of_succ_lt_succ hi)
end Calculus
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end Mp72a103T2
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
noncomputable section
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"
variable [HasPrincipalDivisors K F]

theorem eq_algebraMap_of_forall_ord_nonneg (v₀ : Place K F) (hrat : v₀.IsRational)
    (hdeg : v₀.deg ≠ 0) {g : F} (hg : g ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  have hg₀ : g ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hg (hord v₀)
  refine ⟨v₀.evalAt g, ?_⟩
  by_contra hne

  set t : F := g - algebraMap K F (v₀.evalAt g) with ht
  have htne : t ≠ 0 := sub_ne_zero.mpr hne
  have hzero : 0 < v₀.ord t := v₀.ord_sub_evalAt_pos hrat hg₀ htne
  have hpole : ∀ v : Place K F, 0 ≤ v.ord t := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hg (hord v)) (v.algebraMap_mem' _))

  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) t htne
  have hDpos : 0 < D v₀ := by rw [hD v₀]; exact hzero
  have hDnonneg : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hpole v
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hDpos.ne'
  have hpos : 0 < Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) :=
          mul_pos hDpos (by exact_mod_cast Nat.pos_of_ne_zero hdeg)
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hDnonneg v) (Int.natCast_nonneg _)) hmem
  omega
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

noncomputable section
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem constantsAreBase_of_exists_isRational [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    ConstantsAreBase K F := by
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ algebraMap_mem_lSpace_zero c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      have h := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
      simpa using h
    obtain ⟨c, hc⟩ := Place.eq_algebraMap_of_forall_ord_nonneg v₀ hrat hdeg hf0 hord
    exact ⟨c, hc.symm⟩
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

noncomputable section
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem constantsAreBase_of_deg_eq_one [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hdeg : v₀.deg = 1) :
    ConstantsAreBase K F :=
  constantsAreBase_of_exists_isRational v₀ (v₀.isRational_of_deg_eq_one hdeg)
    (hdeg ▸ one_ne_zero)
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace Submodule
p2m_export "Submodule" "quotEquivOfEq Quotient.eq inclusion factor span_singleton_le_iff_mem coe_smul smul_mem' mk smul_mem mem_bot subtype_injective mk.injEq coe_mem Quotient.subsingleton_iff Quotient.mk span restrictScalars mem_map_of_mem inclusion_injective topEquiv_apply comapSubtypeEquivOfLe neg_le mem_comap finrank_quotient_add_finrank mem_top Quotient.equiv mem_span_singleton mul_mem_mul mem_dualAnnihilator mkQ mem_map coe_subtype map_smul' zero map_span quotientQuotientEquivQuotient coe_eq_zero range_subtype Quotient.mk_surjective map rec mem_inf mem_sup neg_le_neg Quotient.mk_eq_zero subset_span topEquiv map_injective_of_injective comap_subtype_self mapQ subsingleton_iff smul_def mk_eq_zero coe_add mkQ_apply ext factor_mk ker_mkQ map_comap_subtype comap comap_mono map_sup coe_zero map_le_iff_le_comap"
p2m_open "Submodule"

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

def nestedComapMapMkQEquiv {A B C : Submodule K X} (_hAB : A ≤ B) (hBC : B ≤ C) :
    ((B.comap C.subtype).map (A.comap C.subtype).mkQ : Submodule K _)
      ≃ₗ[K] B ⧸ A.comap B.subtype := by
  set S := A.comap C.subtype with hS
  set T := B.comap C.subtype with hT

  let ψ : (T : Type _) →ₗ[K] (C ⧸ S) := S.mkQ ∘ₗ T.subtype
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = T.map S.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let e1 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (T.map S.mkQ : Submodule K _) :=
    (Submodule.Quotient.equiv _ (LinearMap.ker ψ) (LinearEquiv.refl K T)
        (by rw [hker]; simp)).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))

  have hmap : (S.comap T.subtype).map
      (Submodule.comapSubtypeEquivOfLe hBC : (T : Type _) →ₗ[K] B) = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [mem_map, mem_comap, Submodule.coe_subtype, hS]
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxB⟩, hxA, hxeq⟩
      have hx : x = b := congrArg Subtype.val hxeq
      subst hx; exact hxA
    · intro hbA
      exact ⟨⟨⟨b, hBC hb⟩, hb⟩, hbA, rfl⟩
  let e2 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (B ⧸ A.comap B.subtype) :=
    Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) hmap
  exact e1.symm.trans e2

theorem finrank_quotient_chain {A B C : Submodule K X} (hAB : A ≤ B) (hBC : B ≤ C)
    [hCB : Module.Finite K (C ⧸ B.comap C.subtype)]
    [hBA : Module.Finite K (B ⧸ A.comap B.subtype)] :
    Module.Finite K (C ⧸ A.comap C.subtype) ∧
      finrank K (C ⧸ A.comap C.subtype)
        = finrank K (C ⧸ B.comap C.subtype) + finrank K (B ⧸ A.comap B.subtype) := by
  set S := A.comap C.subtype
  set T := B.comap C.subtype
  have hST : S ≤ T := comap_mono hAB

  have e3 := Submodule.quotientQuotientEquivQuotient S T hST

  have eK := nestedComapMapMkQEquiv (K := K) hAB hBC
  haveI : Module.Finite K (T.map S.mkQ : Submodule K _) := Module.Finite.equiv eK.symm
  haveI : Module.Finite K ((C ⧸ S) ⧸ T.map S.mkQ) := Module.Finite.equiv e3.symm
  haveI hfin : Module.Finite K (C ⧸ S) := Module.Finite.of_submodule_quotient (T.map S.mkQ)
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank (R := K) (T.map S.mkQ)
  rw [LinearEquiv.finrank_eq e3, LinearEquiv.finrank_eq eK] at h
  omega

end Submodule
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def adeleBddQuotSingleEquivResidueField (D : Divisor K F) (P : Place K F) :
    (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
      ≃ₗ[K] P.ResidueField := by
  classical
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]

  let π : P.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose_spec
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by simpa [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0

  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := fun {g} hg => by
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]

  have hmem : ∀ α : Place K F → F, α ∈ adeleBdd D → t ^ (D P) * α P ∈ P.toValuationSubring := by
    intro α hα
    rcases eq_or_ne (α P) 0 with hg0 | hg0
    · simp [hg0]
    · refine P.mem_of_ord_nonneg (mul_ne_zero htn0 hg0) ?_
      rw [hordmul hg0]
      have h := hα P
      rw [P.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h
      linarith

  let ψ : adeleBdd D →ₗ[K] P.toValuationSubring :=
    { toFun := fun α => ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩
      map_add' := by
        intro α β; apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply]
        push_cast; ring
      map_smul' := by
        intro c α; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap, Pi.smul_apply]
        ring }
  have hψ_apply : ∀ α : adeleBdd D,
      (ψ α : F) = t ^ (D P) * (α : Place K F → F) P := fun α => rfl

  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    show (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : adeleBdd D →ₗ[K] P.ResidueField := res ∘ₗ ψ

  have hphi : ∀ α : adeleBdd D, φ α = 0 ↔
      (⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := fun α => by
    rw [show φ α = IsLocalRing.residue P.toValuationSubring
            ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ from hres (ψ α),
      IsLocalRing.residue_eq_zero_iff]

  have hker : LinearMap.ker φ = (adeleBdd E).comap (adeleBdd D).subtype := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi α, P.mk_mem_maximalIdeal_iff, mem_adeleBdd]
    have hαD := α.2
    constructor
    · rintro (h | h) v
      ·
        have hα0 : (α : Place K F → F) P = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' htn0
          · exact h'
        by_cases hv : v = P
        · subst v; rw [hα0, Valuation.map_zero]; exact zero_le'
        · rw [hEv v hv]; exact hαD v
      · by_cases hv : v = P
        · subst v
          rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
          · rw [hα0, Valuation.map_zero]; exact zero_le'
          · rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP]
            rw [hordmul hα0] at h; omega
        · rw [hEv v hv]; exact hαD v
    · intro h
      rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
      · left; rw [hα0, mul_zero]
      · right
        have hP := h P
        rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP] at hP
        rw [hordmul hα0]; omega

  have hsurj : Function.Surjective φ := by
    intro c

    obtain ⟨cl, hcl⟩ := IsLocalRing.residue_surjective (R := P.toValuationSubring) c

    set f : F := (cl : F) * t ^ (-(D P)) with hf
    have hαD : Pi.single P f ∈ adeleBdd D := by
      intro v
      by_cases hv : v = P
      · subst v
        simp only [Pi.single_eq_same]
        rcases eq_or_ne (cl : F) 0 with hc0 | hc0
        · rw [hf, hc0, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hf0 : f ≠ 0 := by rw [hf]; exact mul_ne_zero hc0 (zpow_ne_zero _ ht0)
          rw [P.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_le_exp]
          rw [hf, P.ord_mul hc0 (zpow_ne_zero _ ht0), P.ord_zpow, ht1, mul_one]
          have hclnn := P.ord_nonneg_of_mem cl.2
          linarith
      · rw [Pi.single_eq_of_ne hv, Valuation.map_zero]; exact zero_le'
    refine ⟨⟨Pi.single P f, hαD⟩, ?_⟩

    show res (ψ ⟨Pi.single P f, hαD⟩) = c
    rw [hres]
    rw [show (ψ ⟨Pi.single P f, hαD⟩ : P.toValuationSubring) = cl from ?_, hcl]
    apply Subtype.ext
    rw [hψ_apply]
    show t ^ (D P) * (Pi.single P f : Place K F → F) P = (cl : F)
    rw [show (Pi.single P f : Place K F → F) P = f from Pi.single_eq_same _ _, hf,
      mul_comm (cl : F), ← mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, one_mul]

  exact (Submodule.Quotient.equiv _ _ (LinearEquiv.refl K _) (by rw [← hker]; simp)).trans
    (φ.quotKerEquivOfSurjective hsurj)

theorem finrank_adeleBdd_quotient_single [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    Module.Finite K
        (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype) ∧
      finrank K
          (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
        = P.deg := by
  haveI := IsCurveOver.finite_residueField (K := K) P
  exact ⟨Module.Finite.equiv (adeleBddQuotSingleEquivResidueField D P).symm,
    (adeleBddQuotSingleEquivResidueField D P).finrank_eq⟩

theorem finrank_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
      (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
        = Divisor.degree D₂ - Divisor.degree D₁ := by
  classical

  suffices H : ∀ m : ℕ, ∀ D₁ D₂ : Divisor K F, D₁ ≤ D₂ →
      (Divisor.degree (D₂ - D₁)).toNat = m →
      Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
        (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
          = Divisor.degree D₂ - Divisor.degree D₁ from
    H _ D₁ D₂ hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D₁ D₂ hD hm
    have hEeff : ∀ v, 0 ≤ (D₂ - D₁) v := fun v => by
      rw [Finsupp.sub_apply]; have := hD v; omega
    by_cases hD0 : D₂ - D₁ = 0
    ·
      have hD12 : D₁ = D₂ := (sub_eq_zero.mp hD0).symm
      subst hD12
      rw [Submodule.comap_subtype_self]
      haveI : Subsingleton (adeleBdd D₁ ⧸ (⊤ : Submodule K (adeleBdd D₁))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact ⟨Module.Finite.of_finite, by simp [Module.finrank_zero_of_subsingleton]⟩
    ·
      obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ (D₂ - D₁) P := by
        have hne : (D₂ - D₁) P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hEeff P; omega
      set D₂' : Divisor K F := D₂ - Finsupp.single P 1 with hD₂'
      have h12' : D₁ ≤ D₂' := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]
          have := hPpos; rw [Finsupp.sub_apply] at this; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have h2'2 : D₂' ≤ D₂ := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]

      have hdegD₂' : Divisor.degree D₂' = Divisor.degree D₂ - P.deg := by
        rw [hD₂', map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
      have hEnn : 0 ≤ Divisor.degree (D₂ - D₁) := Divisor.degree_nonneg_of_nonneg hEeff
      have hE'nn : 0 ≤ Divisor.degree (D₂' - D₁) := Divisor.degree_nonneg_of_nonneg
        (fun v => by rw [Finsupp.sub_apply]; have := h12' v; omega)
      have hdegdiff : Divisor.degree (D₂' - D₁) = Divisor.degree (D₂ - D₁) - P.deg := by
        simp only [hD₂', map_sub, Divisor.degree_single, one_mul]; ring

      have hmlt : (Divisor.degree (D₂' - D₁)).toNat < m := by rw [← hm]; omega
      obtain ⟨hfin', hrank'⟩ := IH _ hmlt D₁ D₂' h12' rfl

      obtain ⟨hfinS, hrankS⟩ := finrank_adeleBdd_quotient_single (K := K) D₂ P
      rw [← hD₂'] at hfinS hrankS

      haveI := hfin'; haveI := hfinS
      obtain ⟨hfin, hrank⟩ := Submodule.finrank_quotient_chain
        (A := adeleBdd D₁) (B := adeleBdd D₂') (C := adeleBdd D₂)
        (adeleBdd_mono h12') (adeleBdd_mono h2'2)
      refine ⟨hfin, ?_⟩
      rw [hrank, hrankS]
      push_cast
      linarith [hrank', hdegD₂']

theorem module_finite_adeleBdd_quotient [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  (finrank_adeleBdd_quotient hD).1

theorem finrank_adeleBdd_quotient_eq [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
      = Divisor.degree D₂ - Divisor.degree D₁ :=
  (finrank_adeleBdd_quotient hD).2

def lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (_hD : D₁ ≤ D₂) :
    (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      →ₗ[K] (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  Submodule.mapQ _ _
    ((diagonalHom K F).restrict
      (p := (LSpace D₂ : Submodule K F)) (q := (adeleBdd D₂ : Submodule K _))
      (fun f hf => diagonal_mem_adeleBdd_iff.mpr hf))
    (fun f hf => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hf ⊢
      exact diagonal_mem_adeleBdd_iff.mpr hf)

theorem lSpaceQuotientToAdeleBddQuotient_injective {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Function.Injective (lSpaceQuotientToAdeleBddQuotient hD) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]

  rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk ((diagonalHom K F).restrict
            (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f) from rfl,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hx
  exact diagonal_mem_adeleBdd_iff.mp hx

set_option maxHeartbeats 1600000 in

theorem ell_sub_ell_le_degree_sub_degree [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ := by
  haveI := module_finite_adeleBdd_quotient hD

  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    rw [hℓ₁]; exact (Submodule.finrank_quotient_add_finrank _).symm

  have hemb : finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      ≤ finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
    LinearMap.finrank_le_finrank_of_injective (lSpaceQuotientToAdeleBddQuotient_injective hD)
  have hloc := finrank_adeleBdd_quotient_eq hD
  have : (ell D₂ : ℤ) - (ell D₁ : ℤ)
      = (finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) : ℤ) := by
    rw [hL]; push_cast; ring
  rw [this, ← hloc]
  exact_mod_cast hemb

theorem adeleBdd_inf_sup_globalSub {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F)
      = adeleBdd D₁ ⊔ adeleBdd D₂ ⊓ globalSub K F := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleBdd_mono hD), inf_comm]

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (K F)

theorem weilDualityAdelic_of_residueRows (hΩℓ : WeilOmegaEllAgrees K F) :
    WeilDualityAdelic K F := by
  intro _ _ _ ω hω D
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact hΩℓ hω D
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace Submodule
p2m_export "Submodule" "quotEquivOfEq Quotient.eq inclusion factor span_singleton_le_iff_mem coe_smul smul_mem' mk smul_mem mem_bot subtype_injective mk.injEq coe_mem Quotient.subsingleton_iff Quotient.mk span restrictScalars mem_map_of_mem inclusion_injective topEquiv_apply comapSubtypeEquivOfLe neg_le mem_comap finrank_quotient_add_finrank mem_top Quotient.equiv mem_span_singleton mul_mem_mul mem_dualAnnihilator mkQ mem_map coe_subtype map_smul' zero map_span quotientQuotientEquivQuotient coe_eq_zero range_subtype Quotient.mk_surjective map rec mem_inf mem_sup neg_le_neg Quotient.mk_eq_zero subset_span topEquiv map_injective_of_injective comap_subtype_self mapQ subsingleton_iff smul_def mk_eq_zero coe_add mkQ_apply ext factor_mk ker_mkQ map_comap_subtype comap comap_mono map_sup coe_zero map_le_iff_le_comap"
p2m_open "Submodule"

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem comap_subtype_sup_of_le_of_le {S T C : Submodule K X} (hS : S ≤ C) (hT : T ≤ C) :
    S.comap C.subtype ⊔ T.comap C.subtype = (S ⊔ T).comap C.subtype := by
  apply Submodule.map_injective_of_injective (f := C.subtype) C.subtype_injective
  rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    Submodule.map_comap_subtype, inf_eq_right.mpr hS, inf_eq_right.mpr hT,
    inf_eq_right.mpr (sup_le hS hT)]

end Submodule
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem globalSub_le_adeleSpace [HasPrincipalDivisors K F] :
    globalSub K F ≤ adeleSpace K F := by
  rintro _ ⟨f, rfl⟩
  exact diagonal_mem_adeleSpace f

theorem adeleBdd_sup_globalSub_le_adeleSpace [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
  sup_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

theorem adeleBddPrincipal_eq_comap [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBddPrincipal K F D = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype :=
  Submodule.comap_subtype_sup_of_le_of_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

section FiniteLSpace

variable [IsCurveOver K F] [Nonempty (Place K F)]

omit [Nonempty (Place K F)] in

theorem finiteDimensional_lSpace [hL0 : FiniteDimensional K (LSpace (0 : Divisor K F))]
    (D : Divisor K F) : FiniteDimensional K (LSpace D) := by

  have h0D : (0 : Divisor K F) ≤ D ⊔ 0 := le_sup_right
  have hDD : D ≤ D ⊔ 0 := le_sup_left
  suffices h : FiniteDimensional K (LSpace (D ⊔ 0)) by
    exact Module.Finite.of_injective (Submodule.inclusion (lSpace_mono hDD))
      (Submodule.inclusion_injective _)

  haveI := module_finite_adeleBdd_quotient (K := K) h0D
  haveI hfinQ : FiniteDimensional K
      (LSpace (D ⊔ 0) ⧸ (LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype) :=
    Module.Finite.of_injective _ (lSpaceQuotientToAdeleBddQuotient_injective h0D)
  haveI : FiniteDimensional K
      ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype : Submodule K _) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (lSpace_mono h0D)).symm
  exact Module.Finite.of_submodule_quotient
    ((LSpace (0 : Divisor K F)).comap (LSpace (D ⊔ 0)).subtype)

end FiniteLSpace
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option maxHeartbeats 3200000 in

theorem range_lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD)
      = ((adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype).map
          ((adeleBdd D₁).comap (adeleBdd D₂).subtype).mkQ := by
  classical
  ext z
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [LinearMap.mem_range, Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.mkQ_apply]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x

    have hxeq : Submodule.Quotient.mk
        ((diagonalHom K F).restrict (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f)
        = (Submodule.Quotient.mk α :
            adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) := hx
    refine ⟨α, ?_, rfl⟩

    have hdiag2 : (diagonalHom K F (f : F)) ∈ adeleBdd D₂ := diagonal_mem_adeleBdd_iff.mpr f.2
    have hsub : (α : Place K F → F) - diagonalHom K F (f : F) ∈ adeleBdd D₁ := by
      have hq := (Submodule.Quotient.eq _).mp hxeq.symm
      simpa using hq
    refine Submodule.mem_sup.mpr ⟨(α : Place K F → F) - diagonalHom K F (f : F), hsub,
      diagonalHom K F (f : F), diagonal_mem_globalSub _, ?_⟩
    abel
  · rintro ⟨β, hβ, hβeq⟩

    have hβ' : (β : Place K F → F) ∈ adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F) :=
      Submodule.mem_inf.mpr ⟨β.2, hβ⟩
    rw [adeleBdd_inf_sup_globalSub hD, ← map_diagonal_lSpace] at hβ'
    obtain ⟨γ, hγ, δ, ⟨f, hf, hfδ⟩, hsum⟩ := Submodule.mem_sup.mp hβ'
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, ?_⟩
    rw [show (lSpaceQuotientToAdeleBddQuotient hD) (Submodule.Quotient.mk ⟨f, hf⟩)
          = Submodule.Quotient.mk ((diagonalHom K F).restrict
              (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) ⟨f, hf⟩) from rfl,
      ← hβeq, Submodule.Quotient.eq]

    refine Submodule.mem_comap.mpr ?_
    show diagonalHom K F f - (β : Place K F → F) ∈ adeleBdd D₁
    have hβsub : diagonalHom K F f - (β : Place K F → F) = -γ := by
      rw [← hsum, hfδ]; ring
    rw [hβsub]; exact (adeleBdd D₁).neg_mem hγ

set_option maxHeartbeats 3200000 in

theorem finrank_adeleBddSup_quotient [IsCurveOver K F] [Nonempty (Place K F)]
    {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) [hL : FiniteDimensional K (LSpace D₂)] :
    Module.Finite K (↥(adeleBdd D₂ ⊔ globalSub K F)
        ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) ∧
      (finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
          ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) : ℤ)
        = (Divisor.degree D₂ - ell D₂) - (Divisor.degree D₁ - ell D₁) := by
  classical

  let A : Submodule K (adeleBdd D₂) := (adeleBdd D₁).comap (adeleBdd D₂).subtype
  let B : Submodule K (adeleBdd D₂) :=
    (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype
  have hAB : A ≤ B := Submodule.comap_mono le_sup_left

  haveI hfinA : Module.Finite K (adeleBdd D₂ ⧸ A) := module_finite_adeleBdd_quotient hD
  have hdimA : (finrank K (adeleBdd D₂ ⧸ A) : ℤ) = Divisor.degree D₂ - Divisor.degree D₁ :=
    finrank_adeleBdd_quotient_eq hD

  have hran : LinearMap.range (lSpaceQuotientToAdeleBddQuotient hD) = B.map A.mkQ :=
    range_lSpaceQuotientToAdeleBddQuotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hdimL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := K)
      ((LSpace D₁).comap (LSpace D₂).subtype)
    rw [← hℓ₁] at h; exact h.symm
  have hdimB : ell D₂ = finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) + ell D₁ := by
    rw [← hran, LinearMap.finrank_range_of_inj
      (lSpaceQuotientToAdeleBddQuotient_injective hD)]
    exact hdimL

  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  haveI hfinB : Module.Finite K (adeleBdd D₂ ⧸ B) := Module.Finite.equiv e3
  have hdim2 : finrank K (adeleBdd D₂ ⧸ A)
      = finrank K (adeleBdd D₂ ⧸ B) + finrank K (B.map A.mkQ : Submodule K _) := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := adeleBdd D₂ ⧸ A)
      (B.map A.mkQ)
    rw [LinearEquiv.finrank_eq e3] at h; omega

  have e2 := LinearMap.quotientInfEquivSupQuotient (R := K)
    (adeleBdd D₂) (adeleBdd D₁ ⊔ globalSub K F)

  have hsup : adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F) = adeleBdd D₂ ⊔ globalSub K F := by
    rw [← sup_assoc, sup_eq_left.mpr (adeleBdd_mono hD)]
  have hB' : (adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype = B := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  let eL : (adeleBdd D₂ ⧸ B) ≃ₗ[K]
      (adeleBdd D₂ ⧸ ((adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
        (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype)) :=
    Submodule.quotEquivOfEq _ _ hB'.symm

  have hfin_iso : Module.Finite K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype) :=
    Module.Finite.equiv (eL.trans e2)
  have hdim_iso : finrank K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype)
      = finrank K (adeleBdd D₂ ⧸ B) :=
    (LinearEquiv.finrank_eq (eL.trans e2)).symm

  have hcast : (finrank K (adeleBdd D₂ ⧸ A) : ℤ)
      = (finrank K (adeleBdd D₂ ⧸ B) : ℤ) + ((ell D₂ : ℤ) - (ell D₁ : ℤ)) := by
    have hb : (ell D₂ : ℤ)
        = (finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) : ℤ) + (ell D₁ : ℤ) := by
      exact_mod_cast hdimB
    push_cast [hdim2]; linarith
  have hgoal : (finrank K (adeleBdd D₂ ⧸ B) : ℤ)
      = Divisor.degree D₂ - ↑(ell D₂) - (Divisor.degree D₁ - ↑(ell D₁)) := by
    linarith [hdimA, hcast]

  clear_value eL
  exact hsup ▸ ⟨hfin_iso, by rw [hdim_iso]; exact hgoal⟩

section Index

variable [IsCurveOver K F] [Nonempty (Place K F)]

theorem adeleBddSup_eq_of_degree_sub_ell_eq {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)]
    (heq : Divisor.degree D₂ - ell D₂ = Divisor.degree D₁ - ell D₁) :
    adeleBdd D₂ ⊔ globalSub K F = adeleBdd D₁ ⊔ globalSub K F := by
  obtain ⟨hfin, hdim⟩ := finrank_adeleBddSup_quotient hD
  rw [heq, sub_self] at hdim

  refine le_antisymm ?_ (sup_le_sup_right (adeleBdd_mono hD) _)
  haveI := hfin
  have hd0 : finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) = 0 := by
    exact_mod_cast hdim
  have hsub : Subsingleton (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) :=
    Module.finrank_zero_iff.mp hd0
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥(adeleBdd D₂ ⊔ globalSub K F)) ∈
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hxc

end Index
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace RiemannGenusReachedAt p2m_export "AlgebraicCurve.RiemannGenusReachedAt" "mk eq isMax rec" end RiemannGenusReachedAt
namespace RiemannGenusReachedAt
p2m_open_scoped "AlgebraicCurve.RiemannGenusReachedAt" in
private theorem _root_.AlgebraicCurve.RiemannGenusReachedAt.eq_of_ge [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by
  haveI := finiteDimensional_lSpace (K := K) D
  have hge : Divisor.degree D₀ - (ell D₀ : ℤ) ≤ Divisor.degree D - ell D := by
    have := ell_sub_ell_le_degree_sub_degree (K := K) hD
    linarith
  exact le_antisymm (h.isMax D) (h.eq ▸ hge)

end RiemannGenusReachedAt
p2m_export "AlgebraicCurve" "RiemannGenusReachedAt.eq_of_ge"
set_option maxHeartbeats 1600000 in

theorem adeleSpace_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    adeleSpace K F = adeleBdd D₀ ⊔ globalSub K F := by
  refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace D₀)

  rw [adeleSpace, iSup_le_iff]
  intro D
  refine le_trans (adeleBdd_mono (le_sup_left : D ≤ D ⊔ D₀)) ?_
  haveI := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have heq : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = Divisor.degree D₀ - ell D₀ :=
    (h.eq_of_ge le_sup_right).trans h.eq.symm
  have hsup := adeleBddSup_eq_of_degree_sub_ell_eq (K := K)
    (le_sup_right : D₀ ≤ D ⊔ D₀) heq
  rw [← hsup]
  exact le_sup_left

set_option maxHeartbeats 2400000 in

theorem indexOfSpecialty_eq_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  classical

  have hDD' : D ≤ D ⊔ D₀ := le_sup_left
  have hD0D' : D₀ ≤ D ⊔ D₀ := le_sup_right
  haveI := finiteDimensional_lSpace (K := K) (D ⊔ D₀)

  have heqD' : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = γ - 1 := h.eq_of_ge hD0D'
  have hsa : adeleSpace K F = adeleBdd (D ⊔ D₀) ⊔ globalSub K F := by
    refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace _)
    rw [adeleSpace_eq_of_genusReached h]
    exact sup_le_sup_right (adeleBdd_mono hD0D') _

  have hABsub : adeleBdd D ⊔ globalSub K F ≤ adeleBdd (D ⊔ D₀) ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hDD') _
  have hBCsub : adeleBdd (D ⊔ D₀) ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _

  have hCB : (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype = ⊤ := by
    rw [← hsa, Submodule.comap_subtype_self]
  haveI hfinCB : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [hCB]
    haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  have hdimCB : finrank K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) = 0 := by
    rw [hCB]
    haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton

  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hDD'

  haveI := hfinBA
  obtain ⟨hfinCA, hdimCA⟩ := Submodule.finrank_quotient_chain
    (A := adeleBdd D ⊔ globalSub K F) (B := adeleBdd (D ⊔ D₀) ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub

  have hieq : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  rw [adeleBddPrincipal_eq_comap]
  refine ⟨hfinCA, ?_⟩
  rw [hieq]
  push_cast [hdimCA, hdimCB]
  linarith [hdimBA, heqD']

theorem riemannIndexFormula_of_genusReached
    (hg : ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
      RiemannGenusReached K F (genus K F)) :
    RiemannIndexFormula K F := by
  intro _ _ D
  obtain ⟨hne, hL0, D₀, hD₀⟩ := hg
  haveI := hne; haveI := hL0
  exact (indexOfSpecialty_eq_of_genusReached hD₀ D).2

theorem gate_riemannInequality_of_genusReached [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have heq := (indexOfSpecialty_eq_of_genusReached h D).2
  have hnn : (0 : ℤ) ≤ indexOfSpecialty D := Int.natCast_nonneg _
  linarith

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adeleSpaceMul_add [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f + g) = adeleSpaceMul K F f + adeleSpaceMul K F g := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.add_apply, Submodule.coe_add,
    Pi.add_apply, add_mul]

theorem adeleSpaceMul_zero [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (0 : F) = 0 := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, LinearMap.zero_apply,
    Submodule.coe_zero, Pi.zero_apply]

theorem weilSmul_add_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f + g) φ = weilSmul K F f φ + weilSmul K F g φ := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_add, LinearMap.add_apply, map_add]

theorem weilSmul_zero_left [HasPrincipalDivisors K F]
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (0 : F) φ = 0 := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_zero, LinearMap.zero_apply, _root_.map_zero]

theorem weilSmul_neg_left [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (-f) φ = -weilSmul K F f φ := by
  have h := weilSmul_add_left (K := K) (F := F) f (-f) φ
  rw [add_neg_cancel, weilSmul_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem weilSmul_sub_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f - g) φ = weilSmul K F f φ - weilSmul K F g φ := by
  rw [sub_eq_add_neg, weilSmul_add_left, weilSmul_neg_left, sub_eq_add_neg]

theorem weilSmul_eq_zero_iff_left [HasPrincipalDivisors K F]
    {f : F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    weilSmul K F f φ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ weilSmul_zero_left φ⟩
  by_contra hf
  exact hφ (weilSmul_injective hf (h.trans (_root_.map_zero (weilSmul K F f)).symm))

theorem weilSmul_left_injective [HasPrincipalDivisors K F]
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    Function.Injective (fun f : F => weilSmul K F f φ) := by
  intro f g hfg
  have hsub : weilSmul K F (f - g) φ = 0 := by
    rw [weilSmul_sub_left, sub_eq_zero]; exact hfg
  exact sub_eq_zero.mp ((weilSmul_eq_zero_iff_left hφ).mp hsub)

variable (K F) in

def doubleResiduePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) :
    LSpace (W - D) × LSpace (W - D) →ₗ[K] omegaSpace D :=
  (residuePairing K F W D hφ).coprod (residuePairing K F W D hμ)

theorem doubleResiduePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (g h : LSpace (W - D)) :
    (doubleResiduePairing K F W D hφ hμ (g, h) : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ + weilSmul K F (h : F) μ := by
  simp only [doubleResiduePairing, LinearMap.coprod_apply, Submodule.coe_add,
    residuePairing_apply_coe]

theorem doubleResiduePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ) :
    Function.Injective (doubleResiduePairing K F W D hφ hμ) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨g, h⟩ heq

  have heq' : weilSmul K F (g : F) φ + weilSmul K F (h : F) μ = 0 := by
    have hcoe := congrArg Subtype.val heq
    rwa [doubleResiduePairing_apply_coe, Submodule.coe_zero] at hcoe

  rcases eq_or_ne (h : F) 0 with hh0 | hh0
  ·
    rw [hh0, weilSmul_zero_left, add_zero] at heq'
    have hg0 : (g : F) = 0 := (weilSmul_eq_zero_iff_left hφ0).mp heq'
    exact Prod.ext (Subtype.ext hg0) (Subtype.ext hh0)
  ·
    exfalso

    have hμeq : weilSmul K F (h : F) μ = -weilSmul K F (g : F) φ := by
      have h2 : weilSmul K F (h : F) μ + weilSmul K F (g : F) φ = 0 := by
        rw [add_comm]; exact heq'
      exact eq_neg_of_add_eq_zero_left h2

    have hLHS : weilSmul K F (h : F)⁻¹ (weilSmul K F (h : F) μ) = μ := by
      rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hh0, weilSmul_one,
        LinearMap.id_apply]
    have hRHS : weilSmul K F (h : F)⁻¹ (-weilSmul K F (g : F) φ)
        = weilSmul K F (-(g : F) * (h : F)⁻¹) φ := by
      rw [_root_.map_neg, ← LinearMap.comp_apply, ← weilSmul_mul, neg_mul, weilSmul_neg_left]
    exact hindep (-(g : F) * (h : F)⁻¹) (by rw [← hLHS, hμeq, hRHS])

theorem two_mul_ell_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)]
    [Module.Finite K (LSpace (K := K) (F := F) (W - D))] :
    2 * ell (W - D) ≤ indexOfSpecialty D := by
  have hinj := doubleResiduePairing_injective W D hφ hμ hφ0 hindep
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, two_mul]
  exact hle

theorem degree_add_one_sub_genus_le_ell_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ) := by
  have hi := hRI D
  have hi0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

theorem omegaSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ)) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by

  have h0 : 0 < finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) := by
    rw [← indexOfSpecialty_eq]
    have hi := hRI D
    have h0' : (0 : ℤ) < (indexOfSpecialty D : ℤ) := by linarith
    exact_mod_cast h0'
  haveI : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
    FiniteDimensional.of_finrank_pos h0
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

theorem lSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < Divisor.degree D + 1 - (genus K F : ℤ)) :
    Module.Finite K (LSpace (K := K) (F := F) D) := by
  have h0 : (0 : ℤ) < (ell D : ℤ) :=
    lt_of_lt_of_le hpos (degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI D)
  exact FiniteDimensional.of_finrank_pos (by exact_mod_cast h0)

theorem exists_weilSmul_eq_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon

  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * genus K F + 2 * (Divisor.degree W).natAbs + 4 with hn

  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, _root_.map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P

  have hg0 : (0 : ℤ) ≤ (genus K F : ℤ) := Int.natCast_nonneg _
  have habs0 : (0 : ℤ) ≤ |Divisor.degree W| := abs_nonneg _
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W := neg_abs_le _
  have habsW' : Divisor.degree W ≤ |Divisor.degree W| := le_abs_self _

  have hn_ge : 3 * (genus K F : ℤ) + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by
    nlinarith [Int.natCast_nonneg n]
  have hndegP_pos : 0 < (n : ℤ) * (P.deg : ℤ) := by nlinarith

  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; linarith)

  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + (genus K F : ℤ) := by
    have h := hRI D
    rw [hellD, hdegD] at h; push_cast at h; linarith

  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - (genus K F : ℤ)
      ≤ (ell (W - D) : ℤ) := by
    have h := degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI (W - D)
    rw [hdegWD] at h; exact h

  have hiDpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ) := by
    rw [hellD, hdegD]; push_cast; nlinarith
  have hellWDpos : 0 < Divisor.degree (W - D) + 1 - (genus K F : ℤ) := by
    rw [hdegWD]; nlinarith
  haveI := omegaSpace_finite_of_riemannIndexFormula hRI hiDpos
  haveI := lSpace_finite_of_riemannIndexFormula hRI hellWDpos

  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon

  rw [hiD] at hdbl
  nlinarith

theorem weilDifferentialRankOne_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem

  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂

  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_riemannIndexFormula hRI hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]
variable (K F)
variable {K F}
variable (K F)
variable {K F}
variable (K F)

def ResiduePairingSurjective : Prop :=
  ∀ [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (_hφ0 : φ ≠ 0)
    (_hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W),
    Function.Surjective (residuePairing K F W D hφ)
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Finiteness

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem omegaSpace_finite_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by
  haveI := (indexOfSpecialty_eq_of_genusReached h D).1
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

end Finiteness
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section ParametricRankOne

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

set_option maxHeartbeats 2400000 in

theorem exists_weilSmul_eq_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon

  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * γ.natAbs + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, _root_.map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
  have habsγ : -(|γ|) ≤ γ ∧ γ ≤ |γ| := ⟨neg_abs_le _, le_abs_self _⟩
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W ∧
      Divisor.degree W ≤ |Divisor.degree W| := ⟨neg_abs_le _, le_abs_self _⟩
  have hn_ge : 3 * |γ| + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by nlinarith [Int.natCast_nonneg n]

  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; nlinarith)

  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + γ := by
    have hidx := (indexOfSpecialty_eq_of_genusReached h D).2
    rw [hellD, hdegD] at hidx; push_cast at hidx; linarith

  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - γ
      ≤ (ell (W - D) : ℤ) := by
    have hlow := gate_riemannInequality_of_genusReached h (W - D)
    rw [hdegWD] at hlow; exact hlow

  haveI := omegaSpace_finite_of_genusReached h D
  haveI := finiteDimensional_lSpace (K := K) (W - D)

  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith [habsγ.1, habsγ.2, habsW.1, habsW.2]

theorem weilDifferentialRankOne_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem
  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_genusReached h hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end ParametricRankOne
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

theorem residuePairing_surjective_of_rankOne_max [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩
  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRankOne hφmem hφ0 hμmem
  rcases eq_or_ne f 0 with rfl | hf0
  ·
    have hμ0 : (⟨μ, hμD⟩ : omegaSpace D) = 0 :=
      Subtype.ext (hf.trans (weilSmul_zero_left φ))
    exact ⟨0, (_root_.map_zero _).trans hμ0.symm⟩
  ·

    obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    have hPinv : ∀ v, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord v, v.ord_inv]
    have hinv : weilSmul K F f⁻¹ μ = φ := by
      rw [hf, ← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf0, weilSmul_one,
        LinearMap.id_apply]
    have hφD : φ ∈ omegaSpace (D + -P) := by
      rw [← hinv]; exact weilSmul_mem_omegaSpace_add (inv_ne_zero hf0) hPinv hμD
    have hDP : D + -P ≤ W := hWmax _ hφD
    have hfL : f ∈ LSpace (W - D) := by
      rw [mem_lSpace_iff_ord]; refine Or.inr fun v => ?_
      have hv := hDP v
      rw [Finsupp.add_apply, Finsupp.neg_apply, hPord v] at hv
      rw [Finsupp.sub_apply]; linarith
    exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩

section Identification

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]
  [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F]

omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F] in

theorem stichtenothGenus_nonneg
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hC : ConstantsAreBase K F) : 0 ≤ γ := by
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [_root_.map_zero, ell_zero_eq_one_of_constantsAreBase hC] at hi0
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty (0 : Divisor K F) : ℤ) := Int.natCast_nonneg _
  push_cast at hi0; linarith

omit [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
  [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] in

theorem genus_eq_degree_div :
    ∃ (ω₀ : Ω[F⁄K]) (hω₀ : ω₀ ≠ 0),
      genus K F = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 := by
  have hne : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  refine ⟨hne.choose, hne.choose_spec, ?_⟩
  rw [genus, dif_pos hne]

end Identification
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.uniformizer_pow_inv_mem_poleSubmodule_self (m : ℕ) :
    (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (m + 2) :=
  (gate_poleSubmodule_strictMono v (m + 1)).1

p2m_export "AlgebraicCurve.Place" "uniformizer_pow_inv_mem_poleSubmodule_self"
private theorem _root_.AlgebraicCurve.Place.higherPoleMonomial_sum_mem_poleSubmodule {s : Finset ℕ} {N : ℕ}
    (hs : ∀ m ∈ s, m < N) (c : ℕ → K) :
    ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (N + 1) :=
  Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ <|
      v.poleSubmodule_mono (by have := hs m hm; omega)
        (v.uniformizer_pow_inv_mem_poleSubmodule_self m)

p2m_export "AlgebraicCurve.Place" "higherPoleMonomial_sum_mem_poleSubmodule"
private theorem _root_.AlgebraicCurve.Place.higherPoleMonomial_coeff_eq_zero_of_mem (s : Finset ℕ) (c : ℕ → K)
    (hmem : ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule 1) :
    ∀ m ∈ s, c m = 0 := by
  induction s using Finset.induction_on_max with
  | empty => intro m hm; exact absurd hm (Finset.notMem_empty m)
  | insert N s hN ih =>
    have hNs : N ∉ s := fun h => absurd (hN N h) (lt_irrefl N)
    rw [Finset.sum_insert hNs] at hmem

    have hrest : ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (N + 1) :=
      v.higherPoleMonomial_sum_mem_poleSubmodule hN c

    have hwhole := v.poleSubmodule_mono (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)) hmem

    have htop : c N • (v.uniformizer ^ (N + 2))⁻¹ ∈ v.poleSubmodule (N + 1) := by
      have hsub := (v.poleSubmodule (N + 1)).sub_mem hwhole hrest
      rwa [add_sub_cancel_right] at hsub

    have hcN : c N = 0 := by
      by_contra hcN
      exact (gate_poleSubmodule_strictMono v (N + 1)).2 <|
        (inv_smul_smul₀ hcN ((v.uniformizer ^ (N + 2))⁻¹)) ▸
          (v.poleSubmodule (N + 1)).smul_mem (c N)⁻¹ htop

    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm'
    · exact hcN
    · refine ih ?_ m hm'
      rwa [hcN, zero_smul, zero_add] at hmem

p2m_export "AlgebraicCurve.Place" "higherPoleMonomial_coeff_eq_zero_of_mem"
private theorem _root_.AlgebraicCurve.Place.linearIndependent_higherPoleMonomial_mkQ :
    LinearIndependent K
      (fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)) := by
  rw [linearIndependent_iff']
  intro s c hsum m hm
  refine v.higherPoleMonomial_coeff_eq_zero_of_mem s c ?_ m hm
  have h := hsum
  simp only [← map_smul, ← map_sum] at h
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h

p2m_export "AlgebraicCurve.Place" "linearIndependent_higherPoleMonomial_mkQ"
private def _root_.AlgebraicCurve.Place.higherPoleCorrectionAux :
    Submodule.span K
        (Set.range fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹))
      →ₗ[K] v.ResidueField :=
  (Basis.span v.linearIndependent_higherPoleMonomial_mkQ).constr K
    (fun m => v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹))

p2m_export "AlgebraicCurve.Place" "higherPoleCorrectionAux"
private def _root_.AlgebraicCurve.Place.higherPoleCorrection : F →ₗ[K] v.ResidueField :=
  v.higherPoleCorrectionAux.exists_extend.choose ∘ₗ (v.poleSubmodule 1).mkQ

p2m_export "AlgebraicCurve.Place" "higherPoleCorrection"
private theorem _root_.AlgebraicCurve.Place.higherPoleCorrection_apply_of_mem {f : F} (hf : f ∈ v.poleSubmodule 1) :
    v.higherPoleCorrection f = 0 := by
  unfold higherPoleCorrection
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hf,
    _root_.map_zero]

p2m_export "AlgebraicCurve.Place" "higherPoleCorrection_apply_of_mem"
private theorem _root_.AlgebraicCurve.Place.higherPoleCorrection_uniformizer_pow_inv (m : ℕ) :
    v.higherPoleCorrection ((v.uniformizer ^ (m + 2))⁻¹)
      = v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹) := by

  have hmem : (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)
      ∈ Submodule.span K
          (Set.range fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)) :=
    Submodule.subset_span ⟨m, rfl⟩
  have hext := DFunLike.congr_fun v.higherPoleCorrectionAux.exists_extend.choose_spec
    ⟨(v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹), hmem⟩

  refine hext.trans ?_

  unfold higherPoleCorrectionAux
  have hb := (Basis.span v.linearIndependent_higherPoleMonomial_mkQ).constr_basis K
    (fun m => v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹)) m
  rwa [Basis.span_apply] at hb

p2m_export "AlgebraicCurve.Place" "higherPoleCorrection_uniformizer_pow_inv"
private def _root_.AlgebraicCurve.Place.canonicalLocalResidueDataKOfExtend : v.CanonicalLocalResidueDataK where
  res := v.localResidueExtend - v.higherPoleCorrection
  res_of_mem f hf := by
    have h1 : f ∈ v.poleSubmodule 1 :=
      v.poleSubmodule_one ▸ v.mem_simplePoleSubmodule_of_mem hf
    rw [LinearMap.sub_apply, v.higherPoleCorrection_apply_of_mem h1, sub_zero,
      v.localResidueExtend_apply_of_mem (v.mem_simplePoleSubmodule_of_mem hf),
      v.simplePoleResidueAux_eq_zero_of_mem hf]
  res_simplePole f hf := by
    have h1 : f ∈ v.poleSubmodule 1 := v.poleSubmodule_one ▸ hf
    rw [LinearMap.sub_apply, v.higherPoleCorrection_apply_of_mem h1, sub_zero,
      v.localResidueExtend_apply_of_mem hf, simplePoleResidueAux_apply]
  res_higherPoleMonomial n hn := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + m + 1 = m + 2 from by omega, LinearMap.sub_apply,
      v.higherPoleCorrection_uniformizer_pow_inv m, sub_self]

p2m_export "AlgebraicCurve.Place" "canonicalLocalResidueDataKOfExtend"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

set_option maxHeartbeats 6400000

p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve
namespace KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem aCoeff_zero (v : Place K F) (S : Lg37CompletionSection v)
    (x : lg37_completion v) :
    aCoeff v S 0 x = lg37_residueHat v x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S 1 x)
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S 1 x) with ha_def
  rw [Finset.sum_range_one, pow_zero, mul_one] at ha
  have hres : lg37_residueHat v (x - S.lift (a 0)) = lg37_residueHat v 0 :=
    mp72a102_t3_residueHat_congr_of_depth_one v (by rw [ha, _root_.map_zero])
  rw [map_sub, S.residueHat_lift, _root_.map_zero, sub_eq_zero] at hres
  simp only [aCoeff, ← ha_def]
  exact hres.symm

theorem aCoeff_add (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ)
    (x y : lg37_completion v) :
    aCoeff v S m (x + y) = aCoeff v S m x + aCoeff v S m y := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y)
  have hxy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set ay := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y) with hay_def
  set axy := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
    with haxy_def
  have hsum : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift ((fun i => ax i + ay i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e : (x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i
        = (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          + (y - ∑ i ∈ Finset.range (m + 1), S.lift (ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_add, add_mul]),
        Finset.sum_add_distrib]
      ring
    rw [e, mp72a102_t3_evalDepth_add, hx, hy, add_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1), S.lift ((fun i => (ax i + ay i) - axy i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1), S.lift ((ax i + ay i) - axy i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (axy i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hxy, hsum, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => (ax i + ay i) - axy i) key m (Nat.lt_succ_self m)
  have han : axy m = ax m + ay m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hay_def, ← haxy_def]
  exact han

theorem aCoeff_smul (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ) (c : K)
    (x : lg37_completion v) :
    aCoeff v S m (algebraMap K (lg37_completion v) c * x)
      = algebraMap K v.ResidueField c * aCoeff v S m x := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hcx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set acx := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x)) with hacx_def
  have hsmul : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((algebraMap K (lg37_completion v) c * x)
        - ∑ i ∈ Finset.range (m + 1),
            S.lift ((fun i => algebraMap K v.ResidueField c * ax i) i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have e : (algebraMap K (lg37_completion v) c * x)
          - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap K (lg37_completion v) c
          * (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hlift : S.lift (algebraMap K v.ResidueField c * ax i)
          = algebraMap K (lg37_completion v) c * S.lift (ax i) := by
        rw [← Algebra.smul_def c (ax i), map_smul, Algebra.smul_def]
      rw [hlift, mul_assoc]
    rw [e, mp72a102_t3_evalDepth_mul, hx, mul_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1),
          S.lift ((fun i => algebraMap K v.ResidueField c * ax i - acx i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1),
            S.lift (algebraMap K v.ResidueField c * ax i - acx i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (acx i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hcx, hsmul, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => algebraMap K v.ResidueField c * ax i - acx i) key m (Nat.lt_succ_self m)
  have han : acx m = algebraMap K v.ResidueField c * ax m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hacx_def]
  exact han

theorem aCoeff_shift (v : Place K F) (S : Lg37CompletionSection v) (n : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
      = aCoeff v S n x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)
  have hpx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x) with ha_def
  set b := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
    with hb_def

  set c : ℕ → v.ResidueField :=
    fun i => Nat.rec (motive := fun _ => v.ResidueField) 0 (fun j _ => a j) i with hc_def

  have hshift : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
        - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have hmul := mp72a102_t3_evalₐ_succ_mul_eq_zero (maximalIdeal v.toValuationSubring)
      v.uniformizerSubring_mem_maximalIdeal ha
    have e : (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
          - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (x - ∑ i ∈ Finset.range (n + 1), S.lift (a i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      have hc0 : c 0 = 0 := rfl
      have hcs : ∀ i, c (i + 1) = a i := fun _ => rfl
      rw [Finset.sum_range_succ', hc0, _root_.map_zero, zero_mul, add_zero, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcs i, pow_succ]
      ring
    rw [e]
    exact hmul

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      (∑ i ∈ Finset.range (n + 2), S.lift ((fun i => c i - b i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 2), S.lift (c i - b i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (b i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hpx, hshift, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 2)
    (fun i => c i - b i) key (n + 1) (Nat.lt_succ_self (n + 1))
  have hcn : c (n + 1) = a n := rfl
  have hbn : b (n + 1) = a n := by
    have := sub_eq_zero.mp hzero
    rw [hcn] at this
    exact this.symm
  simp only [aCoeff, ← ha_def, ← hb_def]
  exact hbn

theorem aCoeff_shift_pow (v : Place K F) (S : Lg37CompletionSection v) (n k : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + k)
        ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring) ^ k
          * x)
      = aCoeff v S n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring) ^ (k + 1) * x
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ((algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring) ^ k * x) := by
      rw [pow_succ]; ring
    rw [show n + (k + 1) = (n + k) + 1 from by omega, hstep, aCoeff_shift, ih]

theorem aCoeff_one_eq_zero (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : aCoeff v S n 1 = 0 := by
  have hc := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1)
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1) with hcc_def

  set e : ℕ → v.ResidueField := fun i => if i = 0 then 1 else 0 with he_def
  have hesum : (∑ i ∈ Finset.range (n + 1), S.lift (e i)
      * algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring ^ i) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [he_def]
    · intro i _ hi; simp [he_def, hi]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hevalid : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    rw [hesum, sub_self, _root_.map_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      (∑ i ∈ Finset.range (n + 1), S.lift ((fun i => e i - cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 1), S.lift (e i - cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hc, hevalid, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 1)
    (fun i => e i - cc i) key n (Nat.lt_succ_self n)
  have hen : e n = 0 := by simp [he_def, Nat.one_le_iff_ne_zero.mp hn]
  have : e n - cc n = 0 := hzero
  rw [hen, zero_sub, neg_eq_zero] at this
  simp only [aCoeff, ← hcc_def]
  exact this

theorem clearPow_mem (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    v.uniformizer ^ (N + 1) * f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; exact zero_mem _
  · refine (v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero _) hf0)).mpr ?_
    rw [v.ord_mul (v.uniformizer_pow_ne_zero _) hf0, v.ord_uniformizer_pow]
    have h := Int.self_le_toNat (-v.ord f)
    have hNc : ((-v.ord f).toNat : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega

noncomputable def clearedHat (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    lg37_completion v :=
  algebraMap v.toValuationSubring (lg37_completion v)
    ⟨v.uniformizer ^ (N + 1) * f, clearPow_mem v f hN⟩

noncomputable def resStar (v : Place K F) (S : Lg37CompletionSection v) (f : F) :
    v.ResidueField :=
  aCoeff v S ((-v.ord f).toNat) (clearedHat v f (le_refl _))

theorem aCoeff_clearedHat_of_le (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    aCoeff v S N (clearedHat v f hN) = resStar v S f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  unfold clearedHat resStar
  have hfac : (⟨v.uniformizer ^ (((-v.ord f).toNat + k) + 1) * f,
        clearPow_mem v f hN⟩ : v.toValuationSubring)
      = v.uniformizerSubring ^ k
        * ⟨v.uniformizer ^ ((-v.ord f).toNat + 1) * f, clearPow_mem v f (le_refl _)⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, map_pow]
  exact aCoeff_shift_pow v S ((-v.ord f).toNat) k _

theorem resStar_add (v : Place K F) (S : Lg37CompletionSection v) (f g : F) :
    resStar v S (f + g) = resStar v S f + resStar v S g := by
  set N := (-v.ord f).toNat ⊔ (-v.ord g).toNat ⊔ (-v.ord (f + g)).toNat with hN
  have hf : (-v.ord f).toNat ≤ N := le_trans le_sup_left le_sup_left
  have hg : (-v.ord g).toNat ≤ N := le_trans le_sup_right le_sup_left
  have hfg : (-v.ord (f + g)).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S f hf, ← aCoeff_clearedHat_of_le v S g hg,
    ← aCoeff_clearedHat_of_le v S (f + g) hfg, ← aCoeff_add]
  congr 1
  unfold clearedHat
  rw [← map_add]
  congr 1
  apply Subtype.ext
  push_cast
  ring

theorem resStar_smul (v : Place K F) (S : Lg37CompletionSection v) (c : K) (f : F) :
    resStar v S (c • f) = c • resStar v S f := by
  set N := (-v.ord (c • f)).toNat ⊔ (-v.ord f).toNat with hN
  have hcf : (-v.ord (c • f)).toNat ≤ N := le_sup_left
  have hf : (-v.ord f).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S (c • f) hcf, ← aCoeff_clearedHat_of_le v S f hf,
    Algebra.smul_def c (aCoeff v S N (clearedHat v f hf)), ← aCoeff_smul]
  congr 1
  unfold clearedHat
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring (lg37_completion v) c, ← map_mul]
  congr 1
  apply Subtype.ext
  push_cast [v.coe_algebraMap, Algebra.smul_def]
  ring

noncomputable def resStarₗ (v : Place K F) (S : Lg37CompletionSection v) :
    F →ₗ[K] v.ResidueField where
  toFun := resStar v S
  map_add' := resStar_add v S
  map_smul' c f := by rw [RingHom.id_apply]; exact resStar_smul v S c f

theorem resStar_simplePole (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    resStar v S f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ := by
  have hM : (-v.ord f).toNat ≤ 1 := by
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [v.ord_zero]; simp
    · have hge : (0 : ℤ) ≤ v.ord (v.uniformizer * f) :=
        (v.mem_iff_ord_nonneg (mul_ne_zero v.uniformizer_ne_zero hf0)).mp hf
      rw [v.ord_mul v.uniformizer_ne_zero hf0, v.ord_uniformizer] at hge
      have := Int.self_le_toNat (-v.ord f)
      omega
  rw [← aCoeff_clearedHat_of_le v S f hM]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ (1 + 1) * f, clearPow_mem v f hM⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨v.uniformizer * f, hf⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, aCoeff_shift, aCoeff_zero, lg37_residueHat_algebraMap]

theorem resStar_of_mem (v : Place K F) (S : Lg37CompletionSection v) {f : F}
    (hf : f ∈ v.toValuationSubring) : resStar v S f = 0 := by
  rw [resStar_simplePole v S f (mul_mem v.uniformizer_mem hf), IsLocalRing.residue_eq_zero_iff]
  have : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal

theorem resStar_higherPoleMonomial (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : resStar v S (v.uniformizer ^ (n + 1))⁻¹ = 0 := by
  have hord : v.ord (v.uniformizer ^ (n + 1))⁻¹ = -((n : ℤ) + 1) := by
    rw [v.ord_inv, v.ord_uniformizer_pow]; push_cast; ring
  have hM : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat = n + 1 := by
    rw [hord]; simp
  have hle : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat ≤ n + 1 := le_of_eq hM
  rw [← aCoeff_clearedHat_of_le v S (v.uniformizer ^ (n + 1))⁻¹ hle]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ ((n + 1) + 1) * (v.uniformizer ^ (n + 1))⁻¹,
        clearPow_mem v (v.uniformizer ^ (n + 1))⁻¹ hle⟩ : v.toValuationSubring)
      = v.uniformizerSubring := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    rw [pow_succ, mul_right_comm, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), one_mul]
  rw [hfac]
  have : algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
      = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * 1 := by
    rw [mul_one]
  rw [this, aCoeff_shift, aCoeff_one_eq_zero v S hn]

noncomputable def canonicalLocalResidueDataKStar (v : Place K F)
    (S : Lg37CompletionSection v) : v.CanonicalLocalResidueDataK where
  res := resStarₗ v S
  res_of_mem _f hf := resStar_of_mem v S hf
  res_simplePole f hf := resStar_simplePole v S f hf
  res_higherPoleMonomial _n hn := resStar_higherPoleMonomial v S hn

section WitnessW
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))
include hℓ

end WitnessW
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end ModularCurve.KwNo6Pin
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_lSpace_of_weilSmul_mem_omegaSpace [HasPrincipalDivisors K F]
    {W D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W)
    {f : F} (hfφ : weilSmul K F f φ ∈ omegaSpace D) :
    f ∈ LSpace (W - D) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact (LSpace (W - D)).zero_mem
  ·
    obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    have hPinv : ∀ v : Place K F, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord, v.ord_inv]

    have hφshift : φ ∈ omegaSpace (D - P) := by
      have hinv : weilSmul K F f⁻¹ (weilSmul K F f φ) = φ := by
        rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf, weilSmul_one,
          LinearMap.id_apply]
      have h := weilSmul_mem_omegaSpace_add (inv_ne_zero hf) hPinv hfφ
      rwa [hinv, ← sub_eq_add_neg] at h

    have hle := hWmax (D - P) hφshift
    refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
    have hlev := hle v
    rw [Finsupp.sub_apply, hPord v] at hlev
    rw [Finsupp.sub_apply]
    linarith
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairing_surjective [HasPrincipalDivisors K F]
    (hRk1 : WeilDifferentialRankOne K F) (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩

  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRk1 hφmem hφ0 hμmem

  have hfL : f ∈ LSpace (W - D) :=
    mem_lSpace_of_weilSmul_mem_omegaSpace hWmax (hf ▸ hμD)
  exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairingSurjective_of_weilDifferentialRankOne [HasPrincipalDivisors K F]
    (hRk1 : WeilDifferentialRankOne K F) : ResiduePairingSurjective K F := by
  intro _ W D φ hφ hφ0 hWmax
  exact residuePairing_surjective hRk1 W D hφ hφ0 hWmax
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairingSurjective_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F) : ResiduePairingSurjective K F :=
  residuePairingSurjective_of_weilDifferentialRankOne
    (weilDifferentialRankOne_of_riemannIndexFormula hRI)
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
p2m_open "AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField"
section CanonicalKResidueTerm
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
section SupportMachinery
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable (K F)
variable {K F}

theorem weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK [HasPrincipalDivisors K F]
    (hRT : ResidueTheoremK K F) (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehlerK Rfam hω ∈ omegaSpace (canonicalDivisorOf hω) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilOfKaehlerK_vanish_adeleBdd_canonical Rfam hω (Submodule.mem_comap.mp hβ)]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have hγ' : γ = ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ := Subtype.ext hf.symm
  rw [hγ', hRT Rfam hω f, add_zero]
end SupportMachinery
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end CanonicalKResidueTerm
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Single

end Single
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section SingleEval

variable [HasCanonicalLocalResidueKStar K F]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

end SingleEval
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section SimplePoleProbe

variable [HasCanonicalLocalResidueKStar K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

def simplePoleProbe {ω : Ω[F⁄K]} (_hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) : adeleSpace K F :=
  adeleSingle v ((c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹)

open scoped _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in
omit [Nontrivial Ω[F⁄K]] in

theorem simplePoleProbe_mem_adeleBdd {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) {D : Divisor K F} (hDv : canonicalDivisorOf hω v < D v) :
    (simplePoleProbe hω v c : Place K F → F) ∈ adeleBdd D := by
  unfold simplePoleProbe
  rw [adeleSingle_coe]
  refine single_mem_adeleBdd v _ D ?_
  rcases eq_or_ne (c : F) 0 with hc | hc
  · rw [hc, zero_mul, zero_mul, Valuation.map_zero]; exact zero_le'
  · set g : F := (c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹ with hg
    have hg0 : g ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω))
    rw [v.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp, neg_le]

    rw [hg, v.ord_mul (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω)),
      v.ord_mul hc (inv_ne_zero v.uniformizer_ne_zero),
      v.ord_inv, v.ord_uniformizer, v.ord_inv]
    have hcnn : 0 ≤ v.ord (c : F) := v.ord_nonneg_of_mem c.2
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hDv
    linarith

end SimplePoleProbe
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.exists_trace_residue_ne_zero [HasSeparableResidue K F] (v : Place K F) :
    ∃ c : v.toValuationSubring,
      Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) ≠ 0 := by
  have htr := HasSeparableResidue.trace_ne_zero (K := K) (F := F) v
  rw [ne_eq, LinearMap.ext_iff, not_forall] at htr
  obtain ⟨x, hx⟩ := htr
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨c, by simpa using hx⟩

end Place
p2m_export "AlgebraicCurve" "Place.exists_trace_residue_ne_zero"
section Nonvanishing

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Nonvanishing
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Maximality

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Maximality
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Discharge

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Discharge
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_riemannGenusReachedAt_of_bounded
    [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  obtain ⟨γ, hγ⟩ := hbdd

  obtain ⟨M, ⟨D₀, hD₀⟩, hMmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n => ∃ D : Divisor K F, Divisor.degree D - ell D = n)
      ⟨γ, fun n ⟨D, hD⟩ => hD ▸ hγ D⟩
      ⟨Divisor.degree (0 : Divisor K F) - ell (0 : Divisor K F), 0, rfl⟩
  refine ⟨M + 1, D₀, ?_, ?_, ?_⟩
  · exact finiteDimensional_lSpace D₀
  · rw [hD₀]; ring
  · intro D
    have := hMmax (Divisor.degree D - ell D) ⟨D, rfl⟩
    linarith
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem stichtenothGenusExists_of_bounded
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    StichtenothGenusExists K F :=
  ⟨‹_›, ‹_›, exists_riemannGenusReachedAt_of_bounded hbdd⟩
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
set_option maxHeartbeats 6400000
p2m_open "Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin
open Mp72a102T1
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem completionSection_nonempty_generic (v : Place K F)
    [FiniteDimensional K v.ResidueField] [Algebra.IsSeparable K v.ResidueField] :
    Nonempty (Lg37CompletionSection v) := by
  obtain ⟨ᾱ, htop⟩ := Field.exists_primitive_element K v.ResidueField
  have hint : IsIntegral K ᾱ := Algebra.IsIntegral.isIntegral ᾱ
  have hmon : (minpoly K ᾱ).Monic := minpoly.monic hint
  have hsep : (minpoly K ᾱ).Separable := Algebra.IsSeparable.isSeparable K ᾱ
  have haevalbar : (aeval ᾱ) (minpoly K ᾱ) = 0 := minpoly.aeval K ᾱ
  obtain ⟨αhat, hαroot, hαres⟩ :=
    mp72a102_t1_exists_completion_root_of_residue_root v hmon hsep haevalbar
  exact ⟨sectionOfPrimitiveRoot v hint htop αhat hαroot hαres⟩
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_lSpace_add {D E : Divisor K F} {f g : F}
    (hf : f ∈ LSpace D) (hg : g ∈ LSpace E) :
    f * g ∈ LSpace (D + E) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]; exact (LSpace _).zero_mem
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun v => ?_
  rw [Finsupp.add_apply, neg_add, v.ord_mul hf0 hg0]
  exact add_le_add ((mem_lSpace_iff_ord.mp hf).resolve_left hf0 v)
    ((mem_lSpace_iff_ord.mp hg).resolve_left hg0 v)

theorem pow_mem_lSpace_nsmul {B : Divisor K F} {f : F} (hf : f ∈ LSpace B) (j : ℕ) :
    f ^ j ∈ LSpace (j • B) := by
  induction j with
  | zero => simpa using one_mem_lSpace_zero (K := K) (F := F)
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lSpace_add ih hf

structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where

  x : F

  B : Divisor K F

  hB_eff : 0 ≤ B

  hx_mem : x ∈ LSpace B

  n : ℕ

  hn_pos : 0 < n

  degB_eq : Divisor.degree B = n

  c : ℕ

  u : Fin n → F

  hu_mem : ∀ i, u i ∈ LSpace (c • B)

  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

variable (K F) in

def HasPoleDivisorPackage : Prop := Nonempty (PoleDivisorPackage K F)

namespace PoleDivisorPackage

variable (P : PoleDivisorPackage K F)

theorem pow_mul_u_mem_lSpace (j : ℕ) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace ((j + P.c) • P.B) := by
  rw [add_nsmul]
  exact mul_mem_lSpace_add (pow_mem_lSpace_nsmul P.hx_mem j) (P.hu_mem i)

theorem pow_mul_u_mem_lSpace_of_le {j m : ℕ} (hjm : j + P.c ≤ m) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace (m • P.B) := by
  refine lSpace_mono ?_ (P.pow_mul_u_mem_lSpace j i)
  intro v
  have hBv : (0 : ℤ) ≤ P.B v := P.hB_eff v
  show ((j + P.c) • P.B) v ≤ (m • P.B) v
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hBv

set_option maxHeartbeats 1600000 in

theorem ell_nsmul_poleDivisor_ge [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    (P.n : ℤ) * (m - P.c + 1) ≤ ell (m • P.B) := by
  haveI := finiteDimensional_lSpace (K := K) (m • P.B)

  set g : Fin (m - P.c + 1) × Fin P.n → LSpace (m • P.B) :=
    fun p => ⟨P.x ^ (p.1 : ℕ) * P.u p.2,
      P.pow_mul_u_mem_lSpace_of_le (by have := p.1.isLt; omega) p.2⟩
    with hgdef

  have hsub : LinearIndependent K (fun p => (g p : F)) := by
    have heq : (fun p => (g p : F))
        = (fun p : ℕ × Fin P.n => P.x ^ p.1 * P.u p.2)
            ∘ (fun p : Fin (m - P.c + 1) × Fin P.n => ((p.1 : ℕ), p.2)) := by
      funext p; rfl
    rw [heq]
    refine P.lin_indep.comp _ ?_
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.val_injective hpq.1) hpq.2

  have hg : LinearIndependent K g := hsub.of_comp (LSpace (m • P.B)).subtype

  have hcard := hg.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hZ : ((m - P.c + 1) * P.n : ℤ) ≤ (ell (m • P.B) : ℤ) := by exact_mod_cast hcard
  have heq : (((m - P.c + 1 : ℕ) : ℤ) * P.n : ℤ) = (P.n : ℤ) * ((m : ℤ) - P.c + 1) := by
    rw [Nat.cast_add, Nat.cast_sub hm, Nat.cast_one]; ring
  linarith

theorem degree_nsmul_sub_ell_le [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    Divisor.degree (m • P.B) - ell (m • P.B) ≤ (P.n : ℤ) * (P.c - 1) := by
  have hge := P.ell_nsmul_poleDivisor_ge hm
  have hdeg : Divisor.degree (m • P.B) = (m : ℤ) * P.n := by
    rw [show m • P.B = (m : ℤ) • P.B from (natCast_zsmul _ _).symm,
      Divisor.degree.map_zsmul, smul_eq_mul, P.degB_eq]
  linarith

end PoleDivisorPackage
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

theorem PoleDivisorPackage.ell_nsmul_sub_pos [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) {A : Divisor K F} (hA : 0 ≤ A) {m : ℕ} (hm : P.c ≤ m)
    (hbig : Divisor.degree A < (P.n : ℤ) * (m - P.c + 1)) :
    0 < ell (m • P.B - A) := by
  haveI := finiteDimensional_lSpace (K := K) (m • P.B)
  have hle : m • P.B - A ≤ m • P.B := by
    intro v
    have hAv : (0 : ℤ) ≤ A v := hA v
    rw [Finsupp.sub_apply]
    linarith

  have h48 := ell_sub_ell_le_degree_sub_degree (K := K) hle
  rw [map_sub, sub_sub_cancel] at h48

  have h412 := P.ell_nsmul_poleDivisor_ge hm

  have : (0 : ℤ) < (ell (m • P.B - A) : ℤ) := by linarith
  exact_mod_cast this

set_option maxHeartbeats 1600000 in

theorem PoleDivisorPackage.degree_sub_ell_le [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (P.n : ℤ) * (P.c - 1) := by
  classical

  set D' : Divisor K F := D ⊔ 0 with hD'def
  have hD'eff : 0 ≤ D' := le_sup_right
  have hDD' : D ≤ D' := le_sup_left
  haveI := finiteDimensional_lSpace (K := K) D'
  have hmono : Divisor.degree D - (ell D : ℤ) ≤ Divisor.degree D' - ell D' := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hDD'
    linarith

  set m : ℕ := P.c + (Divisor.degree D').toNat with hmdef
  have hcm : P.c ≤ m := Nat.le_add_right _ _
  have hdegD' : 0 ≤ Divisor.degree D' := Divisor.degree_nonneg_of_nonneg hD'eff
  have hbig : Divisor.degree D' < (P.n : ℤ) * (m - P.c + 1) := by
    have hcast : ((m : ℤ) - P.c) = Divisor.degree D' := by
      simp only [hmdef, Nat.cast_add, add_sub_cancel_left, Int.toNat_of_nonneg hdegD']
    rw [hcast]
    have hn1 : (1 : ℤ) ≤ P.n := by exact_mod_cast P.hn_pos
    nlinarith

  have hellpos := P.ell_nsmul_sub_pos hD'eff hcm hbig
  have hnebot : LSpace (m • P.B - D') ≠ ⊥ :=
    fun h => by rw [ell, h, finrank_bot] at hellpos; exact lt_irrefl 0 hellpos
  obtain ⟨z, hzL, hz0⟩ := (Submodule.ne_bot_iff _).mp hnebot

  obtain ⟨Dz, hDzord, hDzdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzmem := (mem_lSpace_iff_ord.mp hzL).resolve_left hz0
  have hD'le : D' ≤ m • P.B + Dz := by
    intro v
    have := hzmem v
    simp only [Finsupp.add_apply, Finsupp.sub_apply, neg_sub] at this ⊢
    rw [hDzord]; linarith

  have hellshift : ell (m • P.B + Dz) = ell (m • P.B) :=
    (LinearEquiv.finrank_eq (lSpaceShiftEquiv (m • P.B) hz0 hDzord)).symm
  have hdegshift : Divisor.degree (m • P.B + Dz) = Divisor.degree (m • P.B) := by
    rw [map_add, hDzdeg, add_zero]

  haveI := finiteDimensional_lSpace (K := K) (m • P.B + Dz)
  have hmono' : Divisor.degree D' - (ell D' : ℤ)
      ≤ Divisor.degree (m • P.B + Dz) - ell (m • P.B + Dz) := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hD'le
    linarith
  rw [hellshift, hdegshift] at hmono'
  have h412 := P.degree_nsmul_sub_ell_le hcm
  linarith

theorem riemannGenusBounded_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    RiemannGenusBounded K F :=
  ⟨(P.n : ℤ) * (P.c - 1), P.degree_sub_ell_le⟩

theorem stichtenothGenusExists_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_bounded (riemannGenusBounded_of_poleDivisorPackage P)

theorem stichtenothGenusExists_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage h.some

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where

  x : E

  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)

  v : Place K E

  hvdeg : v.deg = 1

  hxv : v.ord x = -1

  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
variable (T : TranscendenceTower K E F)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem x_ne_zero : T.x ≠ 0 := fun h => by
  have := T.hxv; rw [h, Place.ord_zero] at this; exact absurd this (by decide)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

abbrev xF : F := algebraMap E F T.x

def poleDivisor : Divisor K F := Divisor.pullback F (Finsupp.single T.v 1)

omit [FiniteDimensional E F] in

theorem poleDivisor_apply (w : Place K F) :
    T.poleDivisor w = (w.ramificationIndex E : ℤ) * (Finsupp.single T.v 1) (w.restrict E) :=
  Divisor.pullback_apply (Finsupp.single T.v 1) w

omit [FiniteDimensional E F] in

theorem poleDivisor_nonneg : 0 ≤ T.poleDivisor := by
  classical
  intro w
  rw [Finsupp.coe_zero, Pi.zero_apply, T.poleDivisor_apply, Finsupp.single_apply]
  refine mul_nonneg (Int.natCast_nonneg _) ?_
  split_ifs <;> simp

omit [FiniteDimensional E F] in

theorem xF_mem_lSpace_poleDivisor : T.xF ∈ LSpace T.poleDivisor := by
  classical
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [T.poleDivisor_apply, Place.ord_restrict, Finsupp.single_apply]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, T.hxv, ite_true, mul_one, mul_neg_one, le_refl]
  · simp only [if_neg (Ne.symm hw), mul_zero, _root_.neg_zero]
    exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

theorem degree_poleDivisor_eq_finrank :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by
  rw [poleDivisor, Divisor.degree_pullback, Divisor.degree_single, T.hvdeg]
  push_cast; ring

omit [FiniteDimensional E F] in

theorem mem_lSpace_nsmul_poleDivisor_of_regular_outside {f : F}
    (hreg : ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f)
    {c : ℕ} (hc : ∀ w ∈ T.v.fiber F, -(c : ℤ) ≤ w.ord f) :
    f ∈ LSpace (c • T.poleDivisor) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [Finsupp.smul_apply, T.poleDivisor_apply, Finsupp.single_apply, nsmul_eq_mul]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  ·
    simp only [hw, ite_true, mul_one]
    have he : (1 : ℤ) ≤ w.ramificationIndex E := by
      exact_mod_cast w.ramificationIndex_pos (F := E)
    have hbdd := hc w (Place.mem_fiber.mpr hw)
    nlinarith [Int.natCast_nonneg c]
  ·
    simp only [if_neg (Ne.symm hw), mul_zero, _root_.neg_zero]
    exact hreg w hw

omit [FiniteDimensional E F] in

theorem exists_forall_mem_lSpace_nsmul_poleDivisor {n : ℕ} (u : Fin n → F)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • T.poleDivisor) := by
  classical

  refine ⟨(Finset.univ : Finset (Fin n)).sup fun i =>
    (T.v.fiber F).sup fun w => (-(w.ord (u i))).toNat,
    fun i => T.mem_lSpace_nsmul_poleDivisor_of_regular_outside (hreg i) ?_⟩
  intro w hw

  have h1 : (-(w.ord (u i))).toNat
      ≤ (T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat :=
    Finset.le_sup (f := fun w' => (-(w'.ord (u i))).toNat) hw
  have h2 : ((T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat)
      ≤ (Finset.univ : Finset (Fin n)).sup fun i' =>
          (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat :=
    Finset.le_sup (f := fun i' => (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat)
      (Finset.mem_univ i)
  have htnat : -(w.ord (u i)) ≤ ((-(w.ord (u i))).toNat : ℤ) := Int.self_le_toNat _
  omega

end TranscendenceTower
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

structure IntegralBasisInLSpace (T : TranscendenceTower K E F) where

  c : ℕ

  u : Fin (Module.finrank E F) → F

  hu_indep : LinearIndependent E u

  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in

def HasIntegralBasisInLSpace (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

def IntegralBasisInLSpace.ofRegularOutside (T : TranscendenceTower K E F)
    (u : Fin (Module.finrank E F) → F) (hu_indep : LinearIndependent E u)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    IntegralBasisInLSpace T where
  c := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose
  u := u
  hu_indep := hu_indep
  hu_mem := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose_spec

variable (K E F) in

def HasIntegralBasisRegularOutside (T : TranscendenceTower K E F) : Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

omit [FiniteDimensional E F] in

theorem hasIntegralBasisInLSpace_of_regularOutside (T : TranscendenceTower K E F)
    (h : HasIntegralBasisRegularOutside K E F T) :
    HasIntegralBasisInLSpace K E F T := by
  obtain ⟨u, hu_indep, hreg⟩ := h
  exact ⟨IntegralBasisInLSpace.ofRegularOutside T u hu_indep hreg⟩

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem linearIndependent_pow_mul {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by
  have heq : (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2)
      = (fun p : ℕ × Fin n => (x ^ p.1) • u p.2) := by
    funext p
    rw [Algebra.smul_def, map_pow]
  rw [heq]
  exact linearIndependent_smul (R := K) (S := E) (A := F) hx hu

def PoleDivisorPackage.ofTranscendenceTower (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    PoleDivisorPackage K F where
  x := T.xF
  B := T.poleDivisor
  hB_eff := T.poleDivisor_nonneg
  hx_mem := T.xF_mem_lSpace_poleDivisor
  n := Module.finrank E F
  hn_pos := Module.finrank_pos
  degB_eq := T.degree_poleDivisor_eq_finrank
  c := IB.c
  u := IB.u
  hu_mem := IB.hu_mem
  lin_indep := linearIndependent_pow_mul T.hx_indep IB.hu_indep

theorem hasPoleDivisorPackage_of_transcendenceTower
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    HasPoleDivisorPackage K F :=
  ⟨PoleDivisorPackage.ofTranscendenceTower T IB⟩

theorem hasPoleDivisorPackage_of_hasIntegralBasisInLSpace
    (T : TranscendenceTower K E F) (h : HasIntegralBasisInLSpace K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_transcendenceTower T h.some

theorem hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside
    (T : TranscendenceTower K E F) (h : HasIntegralBasisRegularOutside K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisInLSpace T
    (hasIntegralBasisInLSpace_of_regularOutside T h)

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral {f : F} (hf : _root_.IsIntegral w.toValuationSubring f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hf
  exact hy ▸ y.2

p2m_export "AlgebraicCurve.Place" "mem_of_isIntegral"
private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_algebraMap_mem {A : Type*} [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : _root_.IsIntegral A f) : f ∈ w.toValuationSubring := by

  letI : Algebra A w.toValuationSubring :=
    ((algebraMap A F).codRestrict w.toValuationSubring.toSubring hA).toAlgebra
  haveI : IsScalarTower A w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  exact w.mem_of_isIntegral hf.tower_top

p2m_export "AlgebraicCurve.Place" "mem_of_isIntegral_of_algebraMap_mem"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Bridge

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable {A : Type*} [CommRing A] [Algebra A E] [Algebra A F] [IsScalarTower A E F]

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.mem_of_isIntegral_of_restrict [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : _root_.IsIntegral A f) : f ∈ w.toValuationSubring := by

  refine w.mem_of_isIntegral_of_algebraMap_mem (fun a => ?_) hf
  rw [IsScalarTower.algebraMap_apply A E F, ← w.mem_restrict_iff, hw]
  exact hA a

end Place
p2m_export "AlgebraicCurve" "Place.mem_of_isIntegral_of_restrict"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_of_restrict [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : _root_.IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_restrict hw hA hf)

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_isIntegral_of_restrict"
variable (A) in

def TranscendenceTower.RegularOutside (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

theorem TranscendenceTower.ord_nonneg_of_isIntegral_of_regularOutside
    [Algebra.IsIntegral E F] (T : TranscendenceTower K E F) (hA : T.RegularOutside A)
    {f : F} (hf : _root_.IsIntegral A f) :
    ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f := fun w hw =>
  w.ord_nonneg_of_isIntegral_of_restrict rfl (hA _ hw) hf

end Bridge
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section Headline

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

variable (K E F) in

def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in

theorem linearIndependent_reindex_basis {s : Finset F} (b : Basis s E F) :
    LinearIndependent E (fun i : Fin (Module.finrank E F) =>
      b ((Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm i)) :=
  b.linearIndependent.comp _ (Equiv.injective _)

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasIntegralBasisRegularOutside K E F T := by

  obtain ⟨s, b, hint⟩ := FiniteDimensional.exists_is_basis_integral A E F

  set e : Fin (Module.finrank E F) ≃ s :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  refine ⟨fun i => b (e i), linearIndependent_reindex_basis b, fun i w hw => ?_⟩

  exact T.ord_nonneg_of_isIntegral_of_regularOutside hA (hint (e i)) w hw

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨A, hfrac, hreg⟩ := h

  haveI : IsFractionRing A E := hfrac
  exact hasIntegralBasisRegularOutside_of_isFractionRing (A := A) T
    (fun u hu a => hreg u hu (a : E) a.property)

theorem hasPoleDivisorPackage_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T h)

theorem stichtenothGenusExists_of_hasRegularFractionSubring [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_hasRegularFractionSubring T h)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem TranscendenceTower.adjoin_x_regularOutside (T : TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v →
      ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ u.toValuationSubring := by
  intro u hu a ha

  let S : Subalgebra K E :=
    { u.toValuationSubring.toSubsemiring with
      algebraMap_mem' := u.algebraMap_mem' }
  suffices h : a ∈ S from h
  refine Algebra.adjoin_le ?_ ha
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  show T.x ∈ u.toValuationSubring
  exact u.mem_of_ord_nonneg T.x_ne_zero (T.hxreg u hu)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasRegularFractionSubring K E F T :=
  ⟨Algebra.adjoin K {T.x}, hfrac, T.adjoin_x_regularOutside⟩

theorem stichtenothGenusExists_of_adjoin_x_isFractionRing [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

end Headline
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

noncomputable section

p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"

section Transcendental

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem linearIndependent_pow_of_transcendental {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx

  have hXj : LinearIndependent K (fun j : ℕ => (X : K[X]) ^ j) := by
    have hb := (Polynomial.basisMonomials K).linearIndependent
    simp only [Polynomial.coe_basisMonomials] at hb
    convert hb using 2 with j
    exact (Polynomial.monomial_one_right_eq_X_pow j).symm
  have heq : (fun j : ℕ => x ^ j)
      = (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (X ^ j)) := by
    funext j; simp
  rw [heq]
  exact hXj.map' (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)

end Transcendental
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem algebraMap_polynomial_mem_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ u.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty u with ⟨w, hw⟩ | hw
  · subst hw; exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd hw hu

theorem ord_X_nonneg_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact u.ord_nonneg_of_mem (algebraMap_polynomial_mem_of_ne_placeInfty K hu Polynomial.X)

variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

def transcendenceTower : TranscendenceTower K (RatFunc K) F where
  x := RatFunc.X
  hx_indep := linearIndependent_pow_of_transcendental RatFunc.transcendental_X
  v := placeInfty K
  hvdeg := deg_placeInfty K
  hxv := ord_placeInfty_X K
  hxreg := fun _ hu => ord_X_nonneg_of_ne_placeInfty K hu

omit [DecidableEq (RatFunc K)] in

theorem aeval_X_eq_algebraMap (q : K[X]) :
    (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K)) q
      = algebraMap K[X] (RatFunc K) q := by
  have hext : (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K))
      = IsScalarTower.toAlgHom K K[X] (RatFunc K) :=
    Polynomial.algHom_ext (by simp [RatFunc.algebraMap_X])
  rw [hext]; rfl

omit [DecidableEq (RatFunc K)] in

theorem algebraMap_polynomial_mem_adjoin_X (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Algebra.adjoin K {(RatFunc.X : RatFunc K)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, aeval_X_eq_algebraMap K q⟩

omit [DecidableEq (RatFunc K)] in

theorem isFractionRing_adjoin_X :
    IsFractionRing (Algebra.adjoin K {(RatFunc.X : RatFunc K)}) (RatFunc K) := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  refine ⟨⟨algebraMap K[X] (RatFunc K) z.num, algebraMap_polynomial_mem_adjoin_X K z.num⟩,
    ⟨algebraMap K[X] (RatFunc K) z.denom, algebraMap_polynomial_mem_adjoin_X K z.denom⟩, ?_⟩
  show z = algebraMap K[X] (RatFunc K) z.num / algebraMap K[X] (RatFunc K) z.denom
  exact z.num_div_denom.symm

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

variable [HasPrincipalDivisors K F]

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem stichtenothGenusExists_of_ratFunc_tower :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
section LyingOver
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
attribute [local instance 0] Place.valuationSubringAlgebra
omit [DecidableEq (RatFunc K)] [Algebra K F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] in

private theorem not_isField_integralClosureAt' (v : Place K (RatFunc K)) :
    ¬IsField (Place.integralClosureAt F v) := fun hf =>
  ValuationSubring.not_isField_of_ne_top _ v.ne_top'
    ((Algebra.IsIntegral.isField_iff_isField
      (R := v.toValuationSubring) (S := Place.integralClosureAt F v)
      (Place.algebraMap_integralClosureAt_injective v)).mpr hf)
end LyingOver
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
section LyingOver
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
attribute [local instance 0] Place.valuationSubringAlgebra
omit [DecidableEq (RatFunc K)] in

theorem exists_restrict_eq (v : Place K (RatFunc K)) :
    ∃ w : Place K F, w.restrict (RatFunc K) = v := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Place.integralClosureAt F v)
  haveI := hM
  exact ⟨Place.placeOfPrime (v := v)
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
        (not_isField_integralClosureAt' K F v)⟩,
    Place.restrict_placeOfPrime _⟩
end LyingOver
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
section LyingOver
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
attribute [local instance 0] Place.valuationSubringAlgebra

theorem nonempty_place_of_ratFunc_tower : Nonempty (Place K F) :=
  (exists_restrict_eq K F (placeInfty K)).nonempty
end LyingOver
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
omit [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] in

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  rw [show LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) from hC]
  exact LinearMap.finiteDimensional_range _
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

set_option autoImplicit false
noncomputable section
p2m_open "Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module Polynomial P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic"
p2m_open "AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "algebraMap_mem_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F]

theorem stichtenothGenusExists (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  haveI := nonempty_place_of_ratFunc_tower K F
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  stichtenothGenusExists_of_ratFunc_tower K F
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
noncomputable section
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"
namespace ModularCurve
local notation "Qbar" => AlgebraicClosure ℚ
p2m_open "IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing"
section AlgClosedEngine
variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [DecidableEq (RatFunc K)]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsAlgClosed K] [IsCurveOver K F]

theorem p0n20_rr_constantsAreBase_of_isAlgClosed : ConstantsAreBase K F := by
  obtain ⟨v⟩ := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  exact constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)
end AlgClosedEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section
section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero Module P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module IsLocalRing P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing Module.IsLocalRing"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve"

namespace ModularCurve

local notation "Qbar" => AlgebraicClosure ℚ

section CanonicalProbe

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

open scoped _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in

theorem p0n25_wkc_kaehlerResidueTermKFam_single_of_ne
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    {v : Place K F} (g : F) {w : Place K F} (hw : w ≠ v) :
    kaehlerResidueTermKFam Rfam ω (Pi.single v g) w = 0 := by
  rw [kaehlerResidueTermKFam_apply, Pi.single_eq_of_ne hw, zero_mul, _root_.map_zero, _root_.map_zero]

theorem p0n25_wkc_localResidueData_res_mul_uniformizer_inv
    {v : Place K F} (R : v.LocalResidueData) (c : v.toValuationSubring) :
    R.res ((c : F) * v.uniformizer⁻¹) = IsLocalRing.residue _ c := by
  have hmul : v.uniformizer * ((c : F) * v.uniformizer⁻¹) = (c : F) := by
    rw [mul_comm (c : F), ← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
  have hmem : v.uniformizer * ((c : F) * v.uniformizer⁻¹) ∈ v.toValuationSubring := by
    rw [hmul]; exact c.2
  rw [R.res_simplePole _ hmem]
  congr 1
  exact Subtype.ext hmul

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

open scoped _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in

theorem p0n25_wkc_weilOfKaehlerK_single
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :
    weilOfKaehlerK Rfam hω (adeleSingle v g)
      = Algebra.trace K v.ResidueField ((Rfam v).res (g * v.differentialCoeff ω)) := by
  rw [weilOfKaehlerK_apply, adeleSingle_coe]
  refine (finsum_eq_single _ v
    fun w hw => p0n25_wkc_kaehlerResidueTermKFam_single_of_ne Rfam ω g hw).trans ?_
  rw [kaehlerResidueTermKFam_apply, Pi.single_eq_same]

theorem p0n25_wkc_weilOfKaehlerK_simplePoleProbe
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (c : v.toValuationSubring) :
    weilOfKaehlerK Rfam hω (simplePoleProbe hω v c)
      = Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) := by
  unfold simplePoleProbe
  rw [p0n25_wkc_weilOfKaehlerK_single Rfam hω,
    mul_assoc, inv_mul_cancel₀ (v.differentialCoeff_ne_zero hω), mul_one,
    p0n25_wkc_localResidueData_res_mul_uniformizer_inv (Rfam v).toLocalResidueData c]

end CanonicalProbe
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section CanonicalNonvanishingMaximality

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem p0n25_wkc_weilOfKaehlerK_ne_zero [HasSeparableResidue K F] [Nonempty (Place K F)]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : weilOfKaehlerK Rfam hω ≠ 0 := by
  obtain ⟨v⟩ := ‹Nonempty (Place K F)›
  obtain ⟨c, hc⟩ := v.exists_trace_residue_ne_zero
  intro h
  apply hc
  rw [← p0n25_wkc_weilOfKaehlerK_simplePoleProbe Rfam hω v c, h, LinearMap.zero_apply]

theorem p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehlerK Rfam hω ∈ omegaSpace D)
    {v : Place K F} (hDv : canonicalDivisorOf hω v < D v) :
    (Algebra.trace K v.ResidueField : _ →ₗ[K] K) = 0 := by
  ext x
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  rw [LinearMap.zero_apply, ← p0n25_wkc_weilOfKaehlerK_simplePoleProbe Rfam hω v c]
  exact omegaSpace_vanishBdd hD (simplePoleProbe_mem_adeleBdd hω v c hDv)

theorem p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical [HasSeparableResidue K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehlerK Rfam hω ∈ omegaSpace D) :
    D ≤ canonicalDivisorOf hω := by
  intro v
  rcases le_or_gt (D v) (canonicalDivisorOf hω v) with h | h
  · exact h
  · exact absurd (p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem Rfam hω hD h)
      (HasSeparableResidue.trace_ne_zero v)

end CanonicalNonvanishingMaximality
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section CanonicalSupply

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem p0n25_wkc_exists_weilMax_of_residueTheoremK
    [HasSeparableResidue K F] [Nonempty (Place K F)] [HasPrincipalDivisors K F]
    (hRTK : ResidueTheoremK K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    ∃ φ : Module.Dual K (adeleSpace K F), φ ≠ 0 ∧
      φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω :=
  ⟨weilOfKaehlerK (fun v => v.canonicalLocalResidueDataKOfExtend) hω,
    p0n25_wkc_weilOfKaehlerK_ne_zero _ hω,
    weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK hRTK _ hω,
    fun _ hD => p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical _ hω hD⟩

end CanonicalSupply
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section MirrorIdentification

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {φ : Module.Dual K (adeleSpace K F)} (hne : φ ≠ 0)
    (hmem : φ ∈ omegaSpace (canonicalDivisorOf hω))
    (hmax : ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (D : Divisor K F) :
    Module.finrank K (omegaSpace (K := K) (F := F) D) = ell (canonicalDivisorOf hω - D) := by
  have hinj := residuePairing_injective (canonicalDivisorOf hω) D hmem hne
  have hsurj := residuePairing_surjective_of_rankOne_max
    (weilDifferentialRankOne_of_genusReached h) hmem hne hmax D
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq.symm

theorem p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = γ := by
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hΩ0 := p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    h hω hne hmem hmax 0
  rw [sub_zero] at hΩ0
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩ0, _root_.map_zero,
    ell_zero_eq_one_of_constantsAreBase hC] at hi0
  push_cast at hi0
  linarith

theorem p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * γ - 2 := by
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hΩW := p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    h hω hne hmem hmax (canonicalDivisorOf hω)
  rw [sub_self] at hΩW
  have hiW := (indexOfSpecialty_eq_of_genusReached h (canonicalDivisorOf hω)).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩW,
    ell_zero_eq_one_of_constantsAreBase hC] at hiW
  have hℓW := p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax h hsup hC hω
  push_cast at hiW
  linarith

theorem p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    γ = (genus K F : ℤ) := by
  obtain ⟨ω₀, hω₀, hgen⟩ := genus_eq_degree_div (K := K) (F := F)
  have hdeg := p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax h hsup hC hω₀
  have hγ0 := stichtenothGenus_nonneg h hC
  rw [hgen, hdeg]
  have h2 : (2 * γ - 2 + 2).toNat / 2 = γ.toNat := by omega
  rw [h2]
  exact (Int.toNat_of_nonneg hγ0).symm

end MirrorIdentification
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section MirrorAssembly

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]

theorem p0n25_wkc_riemannGenusReached_of_weilMax
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    RiemannGenusReached K F (genus K F) := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := RationalFunctionField.stichtenothGenusExists K F hC
  haveI := hne
  haveI := hL0
  have hγeq := p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax hD₀ hsup hC
  exact ⟨hne, hL0, D₀, hγeq ▸ hD₀⟩

theorem p0n25_wkc_riemannIndexFormula_of_weilMax
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    RiemannIndexFormula K F := by
  refine riemannIndexFormula_of_genusReached ?_
  intro _ _
  exact p0n25_wkc_riemannGenusReached_of_weilMax K F hsup hC

theorem p0n25_wkc_weilOmegaEllAgrees_of_weilMax [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω) :
    WeilOmegaEllAgrees K F := by
  have hSurj : ResiduePairingSurjective K F :=
    residuePairingSurjective_of_riemannIndexFormula hRI
  intro _ _ _ ω hω D
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hinj := residuePairing_injective (canonicalDivisorOf hω) D hmem hne
  have hsurj := hSurj (canonicalDivisorOf hω) D hmem hne hmax
  exact_mod_cast (LinearEquiv.ofBijective
    (residuePairing K F (canonicalDivisorOf hω) D hmem) ⟨hinj, hsurj⟩).finrank_eq.symm

theorem p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    FunctionFieldRiemannRoch K F := by
  have hRI : RiemannIndexFormula K F :=
    p0n25_wkc_riemannIndexFormula_of_weilMax K F hsup hC
  haveI := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  have hΩℓ : WeilOmegaEllAgrees K F :=
    p0n25_wkc_weilOmegaEllAgrees_of_weilMax K F hRI hsup
  have hWDA : WeilDualityAdelic K F := weilDualityAdelic_of_residueRows K F hΩℓ
  have hWD : WeilDuality K F := weilDuality_of_riemannIndex_of_adelic K F hRI hWDA
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_riemann_and_duality K F hWD hω D

theorem p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK
    [HasSeparableResidue K F]
    (hRTK : ResidueTheoremK K F) (hC : ConstantsAreBase K F) :
    FunctionFieldRiemannRoch K F := by
  haveI := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  intro _ _ _ ω hω D
  exact p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase K F
    (fun {ω'} hω' => p0n25_wkc_exists_weilMax_of_residueTheoremK hRTK hω') hC hω D

end MirrorAssembly
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

section TrivialTowerLanding

end TrivialTowerLanding
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place"

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by
  intro _ _ _
  exact ModularCurve.p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK K F
    (hRTK := hRTK) (hC := ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed K F)

end S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed (solution)
