-- Prove2me | Definitions.Def_OAIQ096A020
-- name    : OAIQ096A020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:47:16.421988+00:00
-- url     : https://prove2.me/theorems/088f3d91-dcc7-48a9-b15e-9c7805b2d03f
-- title:
--   Definitions bundle OAIQ096A020 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 23 definitions and 2 instances. The definitions and types are `OAI.CubicFirstMoment.squarefreeCoordinateError`, `OAI.CubicFirstMoment.structuredAngularTwistCharacter`, `OAI.CubicFirstMoment.structuredFrequencySupport`, `OAI.CubicFirstMoment.structuredTwistCharacter`, `OAI.CubicFirstMoment.tailHighOrdinaryArity`, `OAI.CubicFirstMoment.tailHighUpperArity`, `OAI.CubicFirstMoment.tailPrimeOrdinaryTuple`, `OAI.CubicFirstMoment.tailPrimeOrdinaryTupleSum`, `OAI.CubicFirstMoment.tailPrimeTupleIndependentSum`, `OAI.CubicFirstMoment.tailPrimeTupleTail`, `OAI.CubicFirstMoment.tailPrimeUpperTuple`, `OAI.CubicFirstMoment.tailPrimeUpperTupleSum`, `OAI.CubicFirstMoment.tailScaleDoubleRow`, `OAI.CubicFirstMoment.twistedCoprimeMellinMass`, `OAI.CubicFirstMoment.upperLowArity`, `OAI.CubicFirstMoment.upperLowTail`, `OAI.CubicFirstMoment.upperNoStopArity`, `OAI.CubicFirstMoment.upperNoStopTail`, `OAI.CubicFirstMoment.upperStoppedBeta`, `OAI.CubicFirstMoment.upperStoppedEnvelopeTail`, `OAI.CubicFirstMoment.upperStoppedFilteredArity`, `OAI.CubicFirstMoment.upperStoppedWindow`, `OAI.CubicFirstMoment.upperTailStoppedDyad`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Angular_AngularResidueLift`, `CubicMoment_Estimates_HeightCoprimeContinuity`, `CubicMoment_Estimates_SquarefreeCoordinateErrors`, `CubicMoment_Estimates_StructuredFrequencyPolynomial`, `CubicMoment_Estimates_StructuredMomentTwists`, `CubicMoment_Estimates_TailHighDecomposition`, `CubicMoment_Estimates_TailHighOrdinaryNegligible`, `CubicMoment_Estimates_TailHighUpperNegligible`, `CubicMoment_Estimates_TailPrimeExpansion`, `CubicMoment_Estimates_TailPrimeOrdinaryTuple`, `CubicMoment_Estimates_TailPrimeRegroup`, `CubicMoment_Estimates_TailPrimeTailGeometry`, `CubicMoment_Estimates_TailPrimeUpperTuple`, `CubicMoment_Estimates_UpperLowTail`, `CubicMoment_Estimates_UpperNoStopNegligible`, `CubicMoment_Estimates_UpperStoppedSuffix`, `CubicMoment_Estimates_UpperTailAggregation`, `CubicMoment_Estimates_UpperTailGeometry`, `CubicMoment_Theta_CubicThetaRamifiedMass`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A011`, `OAIQ096A013` and `OAIQ096A015` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_CubicFirstMoment_cubicThetaScalarRankinKernel_residue`, `OAI.CubicFirstMoment.cubicTheta_radial_upperNoStopTail_isLittleO`, `OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power`, `OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO`, `OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform` and `OAI.CubicFirstMoment.upperStoppedFilteredTail_isLittleO_uniform`; the proofs of `OAI.CubicFirstMoment.ProfileControl.low_poisson_dyadic_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_weighted_bilinear`, `OAI_CubicFirstMoment_angularKummerPrimeExplicitEstimate_of_primitive`, `OAI_CubicFirstMoment_angular_balanced_common_normalized_exponents`, `OAI_CubicFirstMoment_angular_balanced_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_angular_corrected_dispersion_asymptotic_actual`, `OAI_CubicFirstMoment_angular_dominant_balanced_full_factor_neighborhood`, `OAI_CubicFirstMoment_angular_dominant_first_full_factor_neighborhood`, `OAI.CubicFirstMoment.angular_exceptional_residual_moment`, `OAI_CubicFirstMoment_angular_first_common_prime_exponents`, `OAI_CubicFirstMoment_angular_first_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving`, `OAI.CubicFirstMoment.angular_height_signed_mellin_saving`, `OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving`, `OAI_CubicFirstMoment_angular_logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form`, `OAI.CubicFirstMoment.angular_tailHighUpperArity_isLittleO_uniform`, `OAI_CubicFirstMoment_angular_two_prime_transition_height`, `OAI_CubicFirstMoment_angular_typeI_low_proved`, `OAI_CubicFirstMoment_angular_typeI_selected_height_ranges_proved`, `OAI.CubicFirstMoment.angular_upperStoppedFilteredTail_isLittleO_uniform`, `OAI_CubicFirstMoment_balanced_twisted_vonMangoldt_neighborhood`, `OAI.CubicFirstMoment.bounded_poisson_dyadic`, `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq`, `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO`, `OAI_CubicFirstMoment_cubicTheta_radial_productTypeICutoffWindow_bound`, `OAI.CubicFirstMoment.cubicTheta_radial_upperNoStopTail_isLittleO`, `OAI_CubicFirstMoment_dominant_first_full_factor_neighborhood`, `OAI_CubicFirstMoment_first_common_coordinate_exponents`, `OAI.CubicFirstMoment.first_unweighted_structured_moment`, `OAI.CubicFirstMoment.height_radial_form_saving`, `OAI_CubicFirstMoment_kummer_unweighted_from_primitive`, `OAI_CubicFirstMoment_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_low_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_metaplectic_actual_retained_mean`, `OAI_CubicFirstMoment_normalized_angular_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_normalized_twisted_primitive_ideal_cubic_moment`, `OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power`, `OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving`, `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved`, `OAI_CubicFirstMoment_rough_prime_corrected_bilinear_actual`, `OAI_CubicFirstMoment_stopped_corrected_dispersion_log_saving_actual`, `OAI.CubicFirstMoment.stopped_noncube_radial_form`, `OAI_CubicFirstMoment_stopped_product_bilinear_log_saving_actual`, `OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO`, `OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform`, `OAI_CubicFirstMoment_typeI_product_low_integral_actual`, `OAI.CubicFirstMoment.uniform_core_block_polynomial_height` and `OAI.CubicFirstMoment.upperStoppedFilteredTail_isLittleO_uniform`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A013
import Definitions.Def_OAIQ096A015

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMomentTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact modulus and unit condition for the numerator/exclusion twist. -/
noncomputable section
namespace CubicFirstMoment

def structuredTwistCharacter (hpub : CubicSupplementaryPeriodicity)
    (v e : Eisenstein) (hv : v ≠ 0) : MulChar (Residues (structuredTwistModulus v e)) ℂ :=
  productResidueChar (1 : MulChar (Residues (1:Eisenstein)) ℂ)
    (productResidueChar (cubicNumeratorChar hpub v hv) (1 : MulChar (Residues e) ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularResidueLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor above three compensates the fixed infinity type.
It is one on every primary element, so it does not change the original sums. -/
noncomputable section
namespace CubicFirstMoment

def structuredAngularTwistCharacter (hperiod : CubicSupplementaryPeriodicity)
    (v e : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) :
    MulChar (Residues (structuredAngularTwistModulus v e)) ℂ :=
  angularLiftResidueChar (structuredTwistCharacter hperiod v e hv) ℓ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightCoprimeContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domination and continuity for the genuine divisor-restricted mass
as its independent arithmetic height varies. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def twistedCoprimeMellinMass (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (y : Eisenstein → ℝ) (u s : ℝ) : ℝ :=
  coprimeMellinMass S H U (fun a => star (β a*mellinPhase u (norm a)))
    (fun a => star (β a*mellinPhase u (norm a))) y s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual squarefree replacement errors in the two exceptional regions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreeCoordinateError (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinatePrimeCutoff W X Y,
    squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*V (norm z/Y))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredFrequencyPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact squarefree frequency polynomial with the numerator, height and
excluded-prime factors retained in its actual coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredFrequencySupport (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter Squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeRegroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-tuple regrouping for the Gauss height tail. The original
product envelope and finite weights survive both support changes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeTupleIndependentSum (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) : ℂ :=
  ∑ f ∈ Fintype.piFinset (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k)),
    (∏ a, largeTupleCoordinateWeight ξ X k a (norm (f a)/largeTupleNormScale k a))*
      productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (∏ a, f a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact bounded-arity expansion of the remaining Gauss height rows.
The original total-product envelope is retained before independent regrouping. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailScaleDoubleRow (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (H U X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      roughTupleCoefficient j (Real.exp primeProductWeights.radius*X)
        primeDetectorCutoff (X^ξ) u *
        productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (r*u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperNoStopNegligible
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper-height no-stop contribution is negligible, with one mesh
for all finite arities and all actual height windows. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperNoStopArity (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(1/3-2*κ) then
          upperTailNoStopRow i 0 κ ρ ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def upperNoStopTail (m : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, upperNoStopArity i κ ρ ξ H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperTailGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual upper stopped dyads have a short side just below X^(1/3).
All size bounds follow from a nonzero coefficient and the product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperStoppedBeta (i : ℕ) (κ ρ ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) : Eisenstein → ℂ :=
  stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1
      0 (X^(1/3-κ)) (X^(1/3-κ)) true)

def upperTailStoppedDyad (i : ℕ) (ℓ : ℤ) (κ ρ ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*upperStoppedBeta i κ ρ ξ X d q b*
        (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperTailAggregation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Aggregate the literal upper-height stopped terms over their original
labels, side dyads and distinguished-prime scales. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperStoppedEnvelopeTail (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        upperTailStoppedRow i 0 κ ρ ξ H (T*(3/2:ℝ)^s) X d
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperStoppedSuffix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper portion of the actual stopped height sum is an aligned
full tail. This preserves cancellation when the ordinary heights are removed. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def upperStoppedWindow (i : ℕ) (κ ρ ξ H U X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      upperTailStoppedRow i 0 κ ρ ξ H U X d else 0

def upperStoppedFilteredArity (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      upperStoppedWindow i κ ρ ξ H (T*(3/2:ℝ)^s) X else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperLowTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full low distinguished-scale branch at upper heights is negligible.
The single stopping identity is applied before either analytic bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperLowArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(1/3-2*κ) then
          scaleFirstTailScaleRow i 0 ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def upperLowTail (m : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, upperLowArity i κ ξ H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighDecomposition
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the original prime Gauss tail into the two
low-scale contributions, the remaining prime groups, and semiprimes. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailHighOrdinaryArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      tailHighScaleRows i 0 ξ H (T*(3/2:ℝ)^s) X (X^(69/200:ℝ)) else 0

def tailHighUpperArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      tailHighScaleRows i 0 ξ H (T*(3/2:ℝ)^s) X (X^(1/3-2*κ)) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeTailGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One surviving height window fixes independent prime groups for the
entire signed tail. Their choice therefore does not depend on frequency. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def tailPrimeTupleTail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeOrdinaryTuple
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A surviving ordinary prefix fixes independent prime groups. Constants
and logarithmic thresholds are uniform over the finite choices of group. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeOrdinaryTuple (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
      tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighOrdinaryNegligible
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full ordinary high-scale contribution, including the finite arity
expansion and all smooth norm partitions. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeOrdinaryTupleSum (i j : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      tailPrimeOrdinaryTuple i j ξ H T X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeUpperTuple
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each upper-height tuple is one aligned suffix. A surviving term chooses
one group for the whole suffix, before applying any norm estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeUpperTuple (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^v then
      tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighUpperNegligible
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete upper high-scale prime contribution, including all norm
partitions and the finite arity expansion. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeUpperTupleSum (i j : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      tailPrimeUpperTuple i j ξ H T X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMass
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact six-unit multiplicity in the squared theta coefficients.
The order congruent to one has precisely the two real units. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
instance instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
instance instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 : Fintype Eisensteinˣ := Fintype.ofFinite _

end CubicFirstMoment

end

end OAI
end


