-- Prove2me | Definitions.Def_OAIQ096A014
-- name    : OAIQ096A014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:43:42.938164+00:00
-- url     : https://prove2.me/theorems/e39436c0-5b18-48d5-9c1a-58f22f618817
-- title:
--   Definitions bundle OAIQ096A014 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 227 declarations of OpenAI's Lean: 55 definitions and 172 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaAuxiliarySeries`, `OAI.CubicFirstMoment.cubicThetaBorelSheet`, `OAI.CubicFirstMoment.cubicThetaCircleFrequency`, `OAI.CubicFirstMoment.cubicThetaCommonArgument`, `OAI.CubicFirstMoment.cubicThetaCommonCoordinates`, `OAI.CubicFirstMoment.cubicThetaCommonNumerator`, `OAI.CubicFirstMoment.cubicThetaCoreArgument`, `OAI.CubicFirstMoment.cubicThetaCoreFreeArgument`, `OAI.CubicFirstMoment.cubicThetaCuspCoefficient`, `OAI.CubicFirstMoment.cubicThetaDirichlet`, `OAI.CubicFirstMoment.cubicThetaDirichletNormMass`, `OAI.CubicFirstMoment.cubicThetaDualCube`, `OAI.CubicFirstMoment.cubicThetaEisensteinSection`, `OAI.CubicFirstMoment.cubicThetaFourierProfileSeries`, `OAI.CubicFirstMoment.cubicThetaFourierProfileTerm`, `OAI.CubicFirstMoment.cubicThetaFreeCubeJoin`, `OAI.CubicFirstMoment.cubicThetaFullGaussian`, `OAI.CubicFirstMoment.cubicThetaFullGaussianMellinTerm`, `OAI.CubicFirstMoment.cubicThetaFullHeightMass`, `OAI.CubicFirstMoment.cubicThetaFullPoleWeightIntegral`, `OAI.CubicFirstMoment.cubicThetaFullRowCoordinates`, `OAI.CubicFirstMoment.cubicThetaFullRowEquiv`, `OAI.CubicFirstMoment.cubicThetaFullRowMultiply`, `OAI.CubicFirstMoment.cubicThetaHighRemainderWeight`, `OAI.CubicFirstMoment.cubicThetaHighWindowSection`, `OAI.CubicFirstMoment.cubicThetaIncomingWindow`, `OAI.CubicFirstMoment.cubicThetaIncomingWindowSection`, `OAI.CubicFirstMoment.cubicThetaIncomingWindowTerm`, `OAI.CubicFirstMoment.cubicThetaInverseNine`, `OAI.CubicFirstMoment.cubicThetaInvertedFrequencyDirichlet`, `OAI.CubicFirstMoment.cubicThetaInvertedNonzeroTerm`, `OAI.CubicFirstMoment.cubicThetaInvertedTerm`, `OAI.CubicFirstMoment.cubicThetaLevelAngularRoot`, `OAI.CubicFirstMoment.cubicThetaNonzeroRowQuadratic`, `OAI.CubicFirstMoment.cubicThetaOrdinaryCoordinate`, `OAI.CubicFirstMoment.cubicThetaPositiveFourierProfileSection`, `OAI.CubicFirstMoment.cubicThetaPositiveRadialTest`, `OAI.CubicFirstMoment.cubicThetaPositiveStripRepresentative`, `OAI.CubicFirstMoment.cubicThetaPrimaryFourierSeries`, `OAI.CubicFirstMoment.cubicThetaPrimaryFourierTerm` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Estimates_ShortMoebiusPolynomials`, `CubicMoment_Estimates_SmallPrimeParts`, `CubicMoment_Theta_CubicThetaArithmeticModelSection`, `CubicMoment_Theta_CubicThetaBorelTransport`, `CubicMoment_Theta_CubicThetaCircleActual`, `CubicMoment_Theta_CubicThetaCoefficientPrimaryReduction`, `CubicMoment_Theta_CubicThetaCommonIndex`, `CubicMoment_Theta_CubicThetaComplexRadialTest`, `CubicMoment_Theta_CubicThetaContinuity`, `CubicMoment_Theta_CubicThetaCoreArguments`, `CubicMoment_Theta_CubicThetaCoreCoordinates`, `CubicMoment_Theta_CubicThetaCubeCancellation`, `CubicMoment_Theta_CubicThetaCuspCoefficients`, `CubicMoment_Theta_CubicThetaDirichletBounds`, `CubicMoment_Theta_CubicThetaExponential`, `CubicMoment_Theta_CubicThetaFiniteConductor`, `CubicMoment_Theta_CubicThetaFourierProfileSeries`, `CubicMoment_Theta_CubicThetaFreeCubeIndex`, `CubicMoment_Theta_CubicThetaFreeLocalVoronoi`, `CubicMoment_Theta_CubicThetaFrequencyContinuation`, `CubicMoment_Theta_CubicThetaFullEisensteinFourier`, `CubicMoment_Theta_CubicThetaFullGaussian`, `CubicMoment_Theta_CubicThetaFullGaussianMellin`, `CubicMoment_Theta_CubicThetaFullLevelRows`, `CubicMoment_Theta_CubicThetaFunction`, `CubicMoment_Theta_CubicThetaGaussParity`, `CubicMoment_Theta_CubicThetaGramCubeResidueBound`, `CubicMoment_Theta_CubicThetaHeightDecay`, `CubicMoment_Theta_CubicThetaHighWindowSeries`, `CubicMoment_Theta_CubicThetaHighWindowSmooth`, `CubicMoment_Theta_CubicThetaIncomingCompactIntegral`, `CubicMoment_Theta_CubicThetaIncomingWindow`, `CubicMoment_Theta_CubicThetaInvertedCoefficients`, `CubicMoment_Theta_CubicThetaInvertedFiniteFourier`, `CubicMoment_Theta_CubicThetaInvertedFrequencyBounds`, `CubicMoment_Theta_CubicThetaInvertedIncoming`, `CubicMoment_Theta_CubicThetaInvertedRowFourier`, `CubicMoment_Theta_CubicThetaInvertedRowMellin`, `CubicMoment_Theta_CubicThetaInvertedRows`, `CubicMoment_Theta_CubicThetaInvertedTorus`, `CubicMoment_Theta_CubicThetaInvertedUnfold`, `CubicMoment_Theta_CubicThetaLevelAngularReciprocity`, `CubicMoment_Theta_CubicThetaMellin`, `CubicMoment_Theta_CubicThetaNineCusp`, `CubicMoment_Theta_CubicThetaNinePhase`, `CubicMoment_Theta_CubicThetaNonzeroRowHeat`, `CubicMoment_Theta_CubicThetaObservationScaling`, `CubicMoment_Theta_CubicThetaPoleRadialScaling`, `CubicMoment_Theta_CubicThetaPositiveFourierObservable`, `CubicMoment_Theta_CubicThetaPositiveFourierProfile`, `CubicMoment_Theta_CubicThetaPositiveFourierSmooth`, `CubicMoment_Theta_CubicThetaPositivePoleScaling`, `CubicMoment_Theta_CubicThetaPositiveRadialMellin`, `CubicMoment_Theta_CubicThetaPositiveRadialNormalization`, `CubicMoment_Theta_CubicThetaPositiveStripRepresentative`, `CubicMoment_Theta_CubicThetaPrimaryConstant`, `CubicMoment_Theta_CubicThetaPrimaryFourierTwist`, `CubicMoment_Theta_CubicThetaPrimaryNineFourier`, `CubicMoment_Theta_CubicThetaPrimaryNineSum`, `CubicMoment_Theta_CubicThetaPrimaryResidueNine`, `CubicMoment_Theta_CubicThetaPrimarySeriesRamification`, `CubicMoment_Theta_CubicThetaPrimaryUnitTwist`, `CubicMoment_Theta_CubicThetaPrimeAdditiveGauss`, `CubicMoment_Theta_CubicThetaPrimeConjugate`, `CubicMoment_Theta_CubicThetaPrimeCriticalFactors`, `CubicMoment_Theta_CubicThetaPrimeCubeResidueTestWeight`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootHorizontal`, `CubicMoment_Theta_CubicThetaPrimeCubeRootStripBound`, `CubicMoment_Theta_CubicThetaPrimeCubeRows`, `CubicMoment_Theta_CubicThetaPrimeFourier`, `CubicMoment_Theta_CubicThetaPrimeGauss`, `CubicMoment_Theta_CubicThetaPrimeHeckeContinuation`, `CubicMoment_Theta_CubicThetaPrimeHeckeRelation`, `CubicMoment_Theta_CubicThetaPrimeResidueObstruction`, `CubicMoment_Theta_CubicThetaPrimeRowRecurrence`, `CubicMoment_Theta_CubicThetaPrimeShiftRows`, `CubicMoment_Theta_CubicThetaPrimeValuation`, `CubicMoment_Theta_CubicThetaPrimitiveRowFactorization`, `CubicMoment_Theta_CubicThetaRadialMellinIdentity`, `CubicMoment_Theta_CubicThetaRadialNonzero`, `CubicMoment_Theta_CubicThetaRadialRealPositive`, `CubicMoment_Theta_CubicThetaRamifiedAllRows`, `CubicMoment_Theta_CubicThetaRamifiedContraction`, `CubicMoment_Theta_CubicThetaRamifiedDenominator`, `CubicMoment_Theta_CubicThetaRamifiedLowFactor`, `CubicMoment_Theta_CubicThetaRamifiedNineGauss`, `CubicMoment_Theta_CubicThetaRamifiedPhaseRows`, `CubicMoment_Theta_CubicThetaRamifiedPhaseTransport`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryFactor`, `CubicMoment_Theta_CubicThetaRamifiedPrimarySeries`, `CubicMoment_Theta_CubicThetaRamifiedRowConductor`, `CubicMoment_Theta_CubicThetaRamifiedRowInflation`, `CubicMoment_Theta_CubicThetaRamifiedRowValue`, `CubicMoment_Theta_CubicThetaRamifiedTopPhase`, `CubicMoment_Theta_CubicThetaRamifiedTrace`, `CubicMoment_Theta_CubicThetaRamifiedUnitConductor`, `CubicMoment_Theta_CubicThetaRamifiedUnitCube`, `CubicMoment_Theta_CubicThetaRamifiedUnitGauss`, `CubicMoment_Theta_CubicThetaRamifiedUnitInflation`, `CubicMoment_Theta_CubicThetaRamifiedUnitValue`, `CubicMoment_Theta_CubicThetaRemainderWeights`, `CubicMoment_Theta_CubicThetaResidueNormalization`, `CubicMoment_Theta_CubicThetaResiduePrimarySupport`, `CubicMoment_Theta_CubicThetaResidueWhittaker`, `CubicMoment_Theta_CubicThetaRowCompletionTranslation`, `CubicMoment_Theta_CubicThetaScalarFactorization`, `CubicMoment_Theta_CubicThetaScalarHeightCutoff`, `CubicMoment_Theta_CubicThetaScalarRankinKernel`, `CubicMoment_Theta_CubicThetaSeries`, `CubicMoment_Theta_CubicThetaTailCoordinates`, `CubicMoment_Theta_CubicThetaTorusCellTransport`, `CubicMoment_Theta_CubicThetaWeightFactor`, `CubicMoment_Theta_CubicThetaWeightedResidue`, `CubicMoment_Theta_CubicThetaWindowEquation`, `CubicMoment_Transform_MetaplecticTailLevel`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A007`, `OAIQ096A008`, `OAIQ096A009` and `OAIQ096A010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A018` and `OAIQ096A019`; the statements `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_large_power`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_small_power`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_radial_model_low_power`, `OAI_CubicFirstMoment_ProfileControl_smallB_radial_form_height_power`, `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_dilated_long_mean`, `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_dilated_negative_long_mean`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_smooth_bilinear_all_lengths`, `OAI_CubicFirstMoment_angular_balanced_common_normalized_exponents`, `OAI_CubicFirstMoment_angular_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_angular_dominant_balanced_full_factor_neighborhood`, `OAI_CubicFirstMoment_angular_dominant_first_full_factor_neighborhood`, `OAI_CubicFirstMoment_angular_first_common_prime_exponents`, `OAI_CubicFirstMoment_angular_first_weighted_tuple_neighborhood`, `OAI_CubicFirstMoment_angular_full_exceptional_structured_moment`, `OAI_CubicFirstMoment_angular_height_all_frequency_cutoff_mass`, `OAI_CubicFirstMoment_angular_large_core_block_moment`, `OAI_CubicFirstMoment_angular_logarithmic_prime_typeI_mixed_full_actual`, `OAI_CubicFirstMoment_angular_low_noncube_mass`, `OAI_CubicFirstMoment_angular_noncube_signed_mellin_integral_saving`, `OAI_CubicFirstMoment_angular_stoppedBeta_long_bins_log_saving`, `OAI_CubicFirstMoment_angular_stopped_twisted_cutoff_tail`, `OAI_CubicFirstMoment_angular_tailPrime_high_group_uniform`, `OAI_CubicFirstMoment_angular_tailPrime_low_group`, `OAI_CubicFirstMoment_angular_two_prime_transition_height`, `OAI_CubicFirstMoment_angular_typeI_low_proved`, `OAI_CubicFirstMoment_angular_typeI_selected_height_ranges_proved`, `OAI_CubicFirstMoment_balanced_common_squarefree_exponents`, `OAI_CubicFirstMoment_balanced_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_bounded_divisor_arithmetic_mellin_tail`, `OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit`, `OAI_CubicFirstMoment_cubicTheta_radial_productTypeICutoffWindow_bound`, `OAI_CubicFirstMoment_first_squarefreeCoordinateError_moment`, `OAI_CubicFirstMoment_full_exceptional_structured_moment`, `OAI_CubicFirstMoment_hecke_dyadic_prime_bound_of_analytic_pair`, `OAI_CubicFirstMoment_hecke_dyadic_prime_bound_of_square_disk`, `OAI_CubicFirstMoment_height_all_frequency_cutoff_mass`, `OAI_CubicFirstMoment_height_signed_mellin_saving`, `OAI_CubicFirstMoment_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_low_core_mellin_integral_all_exponents`, `OAI_CubicFirstMoment_low_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_low_noncube_mass`, `OAI_CubicFirstMoment_noncube_signed_mellin_integral_saving`, `OAI_CubicFirstMoment_stoppedBeta_distinguished_log_saving_all`, `OAI_CubicFirstMoment_stoppedBeta_long_bins_log_saving`, `OAI_CubicFirstMoment_stopped_noncube_mass`, `OAI_CubicFirstMoment_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_stopped_selected_prime_row_saving`, `OAI_CubicFirstMoment_stopped_twisted_cutoff_tail`, `OAI_CubicFirstMoment_tailPrime_hecke_group`, `OAI_CubicFirstMoment_tailPrime_high_group_uniform`, `OAI_CubicFirstMoment_uniform_cubicTheta_centered_subpower` and `OAI_CubicFirstMoment_uniform_cubicTheta_radial_remainder_low`; the proofs of `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_large_power`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_small_power`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_radial_model_low_power`, `OAI_CubicFirstMoment_ProfileControl_large_common_nonzero_power`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_smooth_bilinear_all_lengths`, `OAI_CubicFirstMoment_all_frequency_outer_sieve`, `OAI_CubicFirstMoment_angular_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_angular_cube_poisson_log_saving`, `OAI_CubicFirstMoment_angular_first_weighted_tuple_neighborhood`, `OAI_CubicFirstMoment_angular_height_all_frequency_cutoff_mass`, `OAI_CubicFirstMoment_angular_large_core_block_moment`, `OAI_CubicFirstMoment_angular_low_noncube_mass`, `OAI_CubicFirstMoment_angular_noncube_signed_mellin_integral_saving`, `OAI_CubicFirstMoment_angular_scaleFirstOrdinaryLowTail_two_stage`, `OAI_CubicFirstMoment_angular_scaleFirstTailNoStopRow_finite_bound_proved`, `OAI_CubicFirstMoment_angular_stoppedBeta_long_bins_log_saving`, `OAI_CubicFirstMoment_angular_stopped_cube_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_angular_stopped_noncube_core_blocks`, `OAI_CubicFirstMoment_angular_stopped_product_transfer`, `OAI_CubicFirstMoment_angular_stopped_reflected_arithmetic_mellin_integral`, `OAI_CubicFirstMoment_angular_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_angular_stopped_selected_prime_row_saving`, `OAI_CubicFirstMoment_angular_stopped_twisted_cutoff_tail`, `OAI_CubicFirstMoment_angular_tailPrime_high_group_uniform`, `OAI_CubicFirstMoment_angular_tailPrime_low_group`, `OAI_CubicFirstMoment_angular_upperLowTail_stopping`, `OAI_CubicFirstMoment_angular_upperTailNoStopRow_finite_bound_proved`, `OAI_CubicFirstMoment_balanced_common_squarefree_exponents`, `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_bounded_divisor_arithmetic_mellin_tail`, `OAI_CubicFirstMoment_cube_poisson_log_saving`, `OAI_CubicFirstMoment_first_squarefreeCoordinateError_moment`, `OAI_CubicFirstMoment_height_all_frequency_cutoff_mass`, `OAI_CubicFirstMoment_height_signed_mellin_saving`, `OAI_CubicFirstMoment_huxleyAdditiveLargeSieve_proved`, `OAI_CubicFirstMoment_low_core_mellin_integral_all_exponents`, `OAI_CubicFirstMoment_low_noncube_mass`, `OAI_CubicFirstMoment_noncube_signed_mellin_integral_saving`, `OAI_CubicFirstMoment_ordinary_sparse_centered_bilinear`, `OAI_CubicFirstMoment_primeGroupTail_core_block_sieve`, `OAI_CubicFirstMoment_primitiveResidueHeckeInput_proved`, `OAI_CubicFirstMoment_smallB_core_block_sieve`, `OAI_CubicFirstMoment_stoppedBeta_distinguished_log_saving_all`, `OAI_CubicFirstMoment_stoppedBeta_long_bins_log_saving`, `OAI_CubicFirstMoment_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_stopped_noncube_mass`, `OAI_CubicFirstMoment_stopped_product_transfer`, `OAI_CubicFirstMoment_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_stopped_selected_prime_row_saving`, `OAI_CubicFirstMoment_stopped_twisted_cutoff_tail` and `OAI_CubicFirstMoment_tailPrime_high_group_uniform`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A009
import Definitions.Def_OAIQ096A010

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusPolynomials
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short ideal convolution identity evaluated on actual primary
character polynomials. All sums below are finite divisor sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealPrimaryGenerator_add {a : Eisenstein} (ha : primary a)
    {ν κ : EisensteinIdealExponent} (h : ν+κ ≤ idealExponentOf a) :
    idealPrimaryGenerator (ν+κ) = idealPrimaryGenerator ν * idealPrimaryGenerator κ := by
  have hν : ν ≤ idealExponentOf a := (le_add_of_nonneg_right zero_le).trans h
  have hκ : κ ≤ idealExponentOf a := (le_add_of_nonneg_left zero_le).trans h
  apply primary_associated_eq (idealPrimaryGenerator_primary ha h)
    (primary_mul (idealPrimaryGenerator_primary ha hν) (idealPrimaryGenerator_primary ha hκ))
  apply (primaryNormalize_associated (idealExponentGenerator (ν+κ))).symm.trans
  rw [idealExponentGenerator_add]
  exact (primaryNormalize_associated _).mul_mul (primaryNormalize_associated _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPrimeParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual small-prime partition of squarefree cubic moduli. Its
parts divide the small modulus, so their number has a proved subpower bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primarySmallPart_primary (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primary (primarySmallPart v a) := idealPrimaryGenerator_primary ha (supportedIdealPart_le v _)

lemma primaryOutsidePart_primary (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primary (primaryOutsidePart v a) := idealPrimaryGenerator_primary ha (outsideIdealPart_le v _)

lemma primary_small_outside_mul (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    primarySmallPart v a*primaryOutsidePart v a = a := by
  have hle : supportedIdealPart v (idealExponentOf a)+outsideIdealPart v (idealExponentOf a) ≤
      idealExponentOf a := by rw [supported_add_outside]
  rw [primarySmallPart,primaryOutsidePart,← idealPrimaryGenerator_add ha hle,
    supported_add_outside,idealPrimaryGenerator_at_element ha]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the cubic theta Fourier expansion on its actual
common cusp frequency lattice lambda^{-4} Z[omega]. The coefficient here includes the
factor 1/|mu| when the Whittaker function is evaluated at |mu|v. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaFrequency_pos {n : Eisenstein} (hn : n ≠ 0) :
    0 < ‖cubicThetaFrequency n‖ := by
  apply norm_pos_iff.mpr
  exact div_ne_zero (fun h => hn (Subtype.ext h)) (pow_ne_zero 4 traceLambda_ne_zero)

lemma cubicThetaFrequency_sq (n : Eisenstein) :
    ‖cubicThetaFrequency n‖^2 = norm n/81 := by
  rw [←Complex.normSq_eq_norm_sq]
  unfold cubicThetaFrequency
  rw [Complex.normSq_div,map_pow,traceLambda_normSq]
  norm_num
  rfl

lemma cubicThetaFrequency_power {n : Eisenstein} (hn : n ≠ 0) :
    ‖cubicThetaFrequency n‖^(-14/3:ℝ) = 81^(7/3:ℝ)*norm n^(-7/3:ℝ) := by
  have hp := cubicThetaFrequency_pos hn
  have hN := norm_pos_of_ne_zero hn
  calc
    _ = (‖cubicThetaFrequency n‖^2)^(-7/3:ℝ) := by
      rw [←Real.rpow_natCast_mul hp.le]
      norm_num
    _ = (norm n/81)^(-7/3:ℝ) := by rw [cubicThetaFrequency_sq]
    _ = norm n^(-7/3:ℝ) / 81^(-7/3:ℝ) :=
      Real.div_rpow hN.le (by norm_num) _
    _ = 81^(7/3:ℝ)*norm n^(-7/3:ℝ) := by
      have he : ((81:ℝ)^(-7/3:ℝ))⁻¹ = 81^(7/3:ℝ) := by
        rw [←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 81)]
        congr 1
        ring
      calc
        _ = norm n^(-7/3:ℝ)*((81:ℝ)^(-7/3:ℝ))⁻¹ := div_eq_mul_inv _ _
        _ = _ := by rw [he]; ring

lemma cubicThetaWhittaker_frequency_bound {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerPowerConstant 3*81^(7/3:ℝ))*v^(-14/3:ℝ)*norm n^(-7/3:ℝ) := by
  have hb := cubicThetaWhittaker_power_bound 3 (by omega)
    (mul_pos (cubicThetaFrequency_pos hn) hv)
  norm_num only [Nat.cast_ofNat] at hb
  rw [show -(14/3:ℝ) = -14/3 by ring,
    Real.mul_rpow (cubicThetaFrequency_pos hn).le hv.le,cubicThetaFrequency_power hn] at hb
  convert hb using 1 <;> first | rfl | ring

lemma cubicThetaSeriesTerm_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 0 < v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm a z v n‖ ≤
      (C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)*v^(-14/3:ℝ))*norm n^(-4/3:ℝ) := by
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true, if_true,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ 3)).le) (by positivity))
      (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  · simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,norm_mul,Circle.norm_coe,mul_one]
    have hN := norm_pos_of_ne_zero hn
    calc
      _ ≤ (C*norm n)*((cubicWhittakerPowerConstant 3*81^(7/3:ℝ))*v^(-14/3:ℝ)*norm n^(-7/3:ℝ)) :=
        mul_le_mul (ha n hn) (cubicThetaWhittaker_frequency_bound hn hv)
          (_root_.norm_nonneg _) (mul_nonneg hC hN.le)
      _ = _ := by
        have he : norm n*norm n^(-7/3:ℝ) = norm n^(-4/3:ℝ) := by
          calc
            _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
            _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
            _ = _ := by congr 1; ring
        calc
          _ = (C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)*v^(-14/3:ℝ))*
            (norm n*norm n^(-7/3:ℝ)) := by ring
          _ = _ := by rw [he]

/-- Absolute convergence needs only this coarse coefficient bound; the
arithmetic theta coefficient formulas are constructed separately. -/
theorem cubicThetaSeries_summable {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 0 < v) (z : ℂ) : Summable (cubicThetaSeriesTerm a z v) := by
  apply ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)*v^(-14/3:ℝ))).of_norm_bounded
  intro n
  simpa only [neg_div] using cubicThetaSeriesTerm_bound hC ha hv z n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locally uniform convergence and continuity of the actual cusp Fourier
series in horizontal position and positive height. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaSeriesTerm_continuousAt (a : Eisenstein → ℂ) (n : Eisenstein)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun q : ℂ × ℝ => cubicThetaSeriesTerm a q.1 q.2 n) p := by
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true, if_true]
    exact continuousAt_const
  · simp only [cubicThetaSeriesTerm,hn,ite_false, if_false]
    have hw : ContinuousAt (fun q : ℂ × ℝ =>
        cubicThetaWhittaker (‖cubicThetaFrequency n‖*q.2)) p :=
      (cubicThetaWhittaker_continuousAt (mul_pos (cubicThetaFrequency_pos hn) hp)).comp
        (f := fun q : ℂ × ℝ => ‖cubicThetaFrequency n‖*q.2) (by fun_prop)
    have he : ContinuousAt (fun q : ℂ × ℝ =>
        (Real.fourierChar (tracePair (cubicThetaFrequency n) q.1):ℂ)) p := by
      unfold tracePair
      fun_prop
    exact (continuousAt_const.mul hw).mul he

lemma cubicThetaNonconstant_continuousOn_strip {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hb : 0 < b) :
    ContinuousOn (cubicThetaNonconstant a) {p : ℂ × ℝ | b < p.2} := by
  let K := C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC
    (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ 3)).le) (by positivity)
  have hs := (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (K*b^(-14/3:ℝ))
  apply continuousOn_tsum
    (fun n p hp => (cubicThetaSeriesTerm_continuousAt a n (hb.trans hp)).continuousWithinAt) hs
  intro n p hp
  change b < p.2 at hp
  have hpower : p.2^(-14/3:ℝ) ≤ b^(-14/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hb hp.le (by norm_num)
  calc
    _ ≤ (K*p.2^(-14/3:ℝ))*norm n^(-4/3:ℝ) :=
      cubicThetaSeriesTerm_bound hC ha (hb.trans hp) p.1 n
    _ ≤ _ := by
      simpa only [neg_div] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK)
          (Real.rpow_nonneg (norm_nonneg n) (-4/3:ℝ))

/-- The Fourier series defines a continuous function on hyperbolic 3-space. -/
theorem cubicThetaNonconstant_continuousAt {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    {p : ℂ × ℝ} (hp : 0 < p.2) : ContinuousAt (cubicThetaNonconstant a) p := by
  have hs := cubicThetaNonconstant_continuousOn_strip hC ha
    (show 0 < p.2/2 by positivity)
  have ho : IsOpen {q : ℂ × ℝ | p.2/2 < q.2} := isOpen_lt continuous_const continuous_snd
  exact hs.continuousAt (ho.mem_nhds (by change p.2/2 < p.2; linarith))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeightDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary power decay at the infinite cusp, derived from the actual
Whittaker integral and a single absolutely convergent lattice majorant. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaFrequency_rpow {n : Eisenstein} (hn : n ≠ 0) (s : ℝ) :
    ‖cubicThetaFrequency n‖^s = 81^(-s/2)*norm n^(s/2) := by
  have hp := cubicThetaFrequency_pos hn
  have hN := norm_pos_of_ne_zero hn
  calc
    _ = (‖cubicThetaFrequency n‖^2)^(s/2) := by
      rw [←Real.rpow_natCast_mul hp.le]
      congr 1
      push_cast
      ring
    _ = (norm n/81)^(s/2) := by rw [cubicThetaFrequency_sq]
    _ = norm n^(s/2)/81^(s/2) := Real.div_rpow hN.le (by norm_num) _
    _ = 81^(-s/2)*norm n^(s/2) := by
      rw [neg_div,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 81)]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExponential
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exponential decay of the nonconstant cubic cusp expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_lower {n : Eisenstein} (hn : n ≠ 0) :
    (1/9:ℝ) ≤ ‖cubicThetaFrequency n‖ := by
  have hN := one_le_norm hn
  have hsq := cubicThetaFrequency_sq n
  have hp := (cubicThetaFrequency_pos hn).le
  nlinarith

lemma cubicThetaWhittaker_frequency_exp_bound {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 1 ≤ v) :
    ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerMixedConstant*81^(8/3:ℝ))*norm n^(-8/3:ℝ)*
        Real.exp (-(Real.pi/9)*v) := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hp := cubicThetaFrequency_pos hn
  have hw := cubicThetaWhittaker_mixed_bound (mul_pos hp hv0)
  rw [Real.mul_rpow hp.le hv0.le,cubicThetaFrequency_rpow hn] at hw
  have h1 : -(-16/3:ℝ)/2 = 8/3 := by norm_num
  have h2 : (-16/3:ℝ)/2 = -8/3 := by norm_num
  rw [h1,h2] at hw
  have hvp : v^(-16/3:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hv (by norm_num)
  have he : Real.exp (-Real.pi*(‖cubicThetaFrequency n‖*v)) ≤
      Real.exp (-(Real.pi/9)*v) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (cubicThetaFrequency_lower hn) hv0.le
    nlinarith [Real.pi_pos]
  apply hw.trans
  have hD := cubicWhittakerMixedConstant_pos.le
  have hnp := Real.rpow_nonneg (norm_nonneg n) (-8/3:ℝ)
  calc
    _ ≤ cubicWhittakerMixedConstant*(81^(8/3:ℝ)*norm n^(-8/3:ℝ)*1)*
        Real.exp (-(Real.pi/9)*v) := by gcongr
    _ = _ := by ring

lemma cubicThetaSeriesTerm_exp_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 1 ≤ v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm a z v n‖ ≤
      (C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*Real.exp (-(Real.pi/9)*v)*
        norm n^(-5/3:ℝ) := by
  have hD := cubicWhittakerMixedConstant_pos.le
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true, if_true,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hD) (by positivity))
      (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  · simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,norm_mul,Circle.norm_coe,mul_one]
    have hN := norm_pos_of_ne_zero hn
    calc
      _ ≤ (C*norm n)*((cubicWhittakerMixedConstant*81^(8/3:ℝ))*norm n^(-8/3:ℝ)*
          Real.exp (-(Real.pi/9)*v)) := mul_le_mul (ha n hn)
        (cubicThetaWhittaker_frequency_exp_bound hn hv) (_root_.norm_nonneg _) (mul_nonneg hC hN.le)
      _ = _ := by
        have he : norm n*norm n^(-8/3:ℝ) = norm n^(-5/3:ℝ) := by
          calc
            _ = norm n^(1:ℝ)*norm n^(-8/3:ℝ) := by rw [Real.rpow_one]
            _ = norm n^(1+(-8/3:ℝ)) := (Real.rpow_add hN _ _).symm
            _ = _ := by congr 1; ring
        calc
          _ = ((C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*Real.exp (-(Real.pi/9)*v))*
              (norm n*norm n^(-8/3:ℝ)) := by ring
          _ = _ := by rw [he]

/-- An explicit exponential bound uniform in horizontal position. -/
theorem cubicThetaNonconstant_exponential_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 1 ≤ v) (z : ℂ) :
    ‖cubicThetaNonconstant a (z,v)‖ ≤ cubicThetaExpConstant C*Real.exp (-(Real.pi/9)*v) := by
  have hs := cubicThetaSeries_summable hC ha (zero_lt_one.trans_le hv) z
  let D := (C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*Real.exp (-(Real.pi/9)*v)
  have hmajor : Summable (fun n : Eisenstein => D*norm n^(-5/3:ℝ)) := by
    simpa only [neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 5/3)).mul_left D
  calc
    _ ≤ ∑' n : Eisenstein, ‖cubicThetaSeriesTerm a z v n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Eisenstein, D*norm n^(-5/3:ℝ) :=
      Summable.tsum_le_tsum (cubicThetaSeriesTerm_exp_bound hC ha hv z) hs.norm hmajor
    _ = _ := by rw [tsum_mul_left]; dsimp [D,cubicThetaExpConstant]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two additional arithmetic families in DR v3 (5.13)--(5.14),
normalized by |mu| on the common lambda^-4 frequency lattice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaCuspCoefficient (j : Fin 3) (n : Eisenstein) : ℂ :=
  if h : Nonempty (CubicThetaCoordinates n) then (Classical.choice h).cuspCoefficient j else 0

lemma cubicThetaCuspCoefficient_norm_le (j : Fin 3) (n : Eisenstein) :
    ‖cubicThetaCuspCoefficient j n‖ ≤ 81 := by
  unfold cubicThetaCuspCoefficient
  split_ifs with h
  · exact (Classical.choice h).cuspCoefficient_norm_le j
  · norm_num

lemma cubicThetaCuspCoefficient_bound (j : Fin 3) (n : Eisenstein) (hn : n ≠ 0) :
    ‖cubicThetaCuspCoefficient j n‖ ≤ 81*norm n :=
  (cubicThetaCuspCoefficient_norm_le j n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFunction
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete theta and auxiliary Fourier series from DR v3 (5.6),
(5.7), (5.13) and (5.14), with their proved analytic properties. Modular
transformation identities remain to be established. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaAuxiliarySeries (j : Fin 3) (p : ℂ × ℝ) : ℂ :=
  cubicThetaNonconstant (cubicThetaCuspCoefficient j) p

lemma cubicThetaAuxiliarySeries_exponential_bound (j : Fin 3) (z : ℂ)
    {v : ℝ} (hv : 1 ≤ v) :
    ‖cubicThetaAuxiliarySeries j (z,v)‖ ≤ cubicThetaExpConstant 81*Real.exp (-(Real.pi/9)*v) :=
  cubicThetaNonconstant_exponential_bound (by norm_num : (0:ℝ) ≤ 81)
    (cubicThetaCuspCoefficient_bound j) hv z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable transport of the quotient's chosen representatives back
upstairs, with the actual cubic character. No smooth representative is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaBorelSheet (g : cubicThetaPrincipalGroup) : Set CubicThetaPoint :=
  {p | g • cubicThetaBorelSection (cubicThetaQuotientMap p)=p}

lemma cubicThetaBorelSheet_disjoint {g h : cubicThetaPrincipalGroup} (hne : g≠h) :
    Disjoint (cubicThetaBorelSheet g) (cubicThetaBorelSheet h) := by
  apply Set.disjoint_left.mpr
  intro p hg hh
  exact hne (IsCancelSMul.right_cancel g h _ (hg.trans hh.symm))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact measurable transport between the arithmetic period cell and
the torus. This also applies to measurable L2 representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaTorusCellPoint (u : UnitAddTorus (Fin 2)) : ℂ :=
  cubicThetaPeriodCell ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)) u).val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMellinIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial observation factor is an entire Mellin transform of one
fixed rapidly decaying kernel. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaFourierRadialTest_dilated (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) :
    cubicThetaFourierRadialTest h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^2*
        (∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v (cubicThetaRowHeatScale h) u) := by
  unfold cubicThetaFourierRadialTest
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  have hv0 : 0<v := by linarith [hv]
  have hd := cubicThetaHeat_height_dilation hv0 (cubicThetaRowHeatScale h) s
  calc
    _ = star (W v)/(v:ℂ)^3*((v:ℂ)^s*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)) := by ring
    _ = _ := by
      rw [hd]
      field_simp [Complex.ofReal_ne_zero.mpr hv0.ne']

theorem cubicThetaFourierRadialTest_mellin {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) (s : ℂ) :
    cubicThetaFourierRadialTest h W s=
      mellin (cubicThetaAveragedHeat W (cubicThetaRowHeatScale h)) (s-1) := by
  rw [cubicThetaFourierRadialTest_dilated]
  have hi := cubicThetaRadialMellin_integrable W (cubicThetaRowHeatScale_pos hh) s
  calc
    _ = ∫ v in Ioi (2:ℝ), ∫ u in Ioi (0:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      unfold cubicThetaRadialMellinIntegrand
      ring
    _ = ∫ u in Ioi (0:ℝ), ∫ v in Ioi (2:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) :=
      integral_integral_swap hi
    _ = _ := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards with u
      simp only [show s-1-1=s-2 by ring,smul_eq_mul,cubicThetaAveragedHeat]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold cubicThetaRadialMellinIntegrand
      ring

theorem cubicThetaFourierRadialTest_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) : Differentiable ℂ (cubicThetaFourierRadialTest h W) := by
  have he : cubicThetaFourierRadialTest h W=
      (fun s : ℂ => mellin (cubicThetaAveragedHeat W (cubicThetaRowHeatScale h)) (s-1)) :=
    funext (cubicThetaFourierRadialTest_mellin hh W)
  rw [he]
  exact (cubicThetaAveragedHeat_mellin_entire W (cubicThetaRowHeatScale_pos hh)).comp
    (differentiable_id.sub_const 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed radial test is nontrivial: its value at s=2 is strictly
positive. This supplies a genuine analytic denominator for continuation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaFourierRadialTest_nonzero {h : Eisenstein} (hh : h≠0) :
    cubicThetaFourierRadialTest h cubicThetaRadialTestWeight 2≠0 := by
  let A := cubicThetaRowHeatScale h
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  have hi : IntegrableOn (cubicThetaAveragedHeat cubicThetaRadialTestWeight A) (Ioi (0:ℝ)) := by
    have hm := mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      ((cubicThetaAveragedHeat_continuous cubicThetaRadialTestWeight hA).locallyIntegrableOn measurableSet_Ioi)
      (cubicThetaAveragedHeat_top cubicThetaRadialTestWeight hA)
      (cubicThetaAveragedHeat_bottom cubicThetaRadialTestWeight hA 0)
      (s:=(1:ℂ)) (by norm_num)
    simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul] using hm
  have hp : 0<∫ u in Ioi (0:ℝ), (cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re :=
    cubicThetaPositive_setIntegral
      ((Complex.continuous_re.comp_continuousOn
        (cubicThetaAveragedHeat_continuous cubicThetaRadialTestWeight hA))) hi.re
      (fun u hu => (cubicThetaAveragedHeat_test_re_pos hA hu).le) (x:=1) (by norm_num)
      (cubicThetaAveragedHeat_test_re_pos hA (by norm_num))
  have hr := integral_re hi
  change (∫ u in Ioi (0:ℝ), (cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re)=
    (∫ u in Ioi (0:ℝ), cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re at hr
  rw [hr] at hp
  rw [cubicThetaFourierRadialTest_mellin hh,mellin]
  norm_num only [show (2:ℂ)-1-1=0 by norm_num,Complex.cpow_zero,one_smul]
  intro hz
  change 0<(∫ u in Ioi (0:ℝ), cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re at hp
  rw [hz] at hp
  exact (lt_irrefl 0) hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Meromorphic continuation of the literal nonzero arithmetic Fourier
Dirichlet coefficients, obtained from the actual automorphic resolvent. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRadialTest_eventually_ne_zero {h : Eisenstein} (hh : h≠0) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, cubicThetaFourierRadialTest h cubicThetaRadialTestWeight z≠0 := by
  have ha := (cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).analyticAt
  rcases (ha s).eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · have hg : AnalyticOnNhd ℂ (cubicThetaFourierRadialTest h cubicThetaRadialTestWeight) univ :=
      fun z _ => ha z
    have he := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s) hz
    exact False.elim (cubicThetaFourierRadialTest_nonzero hh (he (mem_univ 2)))
  · exact hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRealPositive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen test has no real zeros, throughout the spectral line. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaFourierRadialTest_real_pos {h : Eisenstein} (hh : h≠0) (σ : ℝ) :
    0<(cubicThetaFourierRadialTest h cubicThetaRadialTestWeight σ).re := by
  let A := cubicThetaRowHeatScale h
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  let F := fun u : ℝ => (u:ℂ)^((σ:ℂ)-2)*cubicThetaAveragedHeat cubicThetaRadialTestWeight A u
  have hi : IntegrableOn F (Ioi (0:ℝ)) := by
    have hm := cubicThetaAveragedHeat_mellinConvergent cubicThetaRadialTestWeight hA ((σ:ℂ)-1)
    simpa only [MellinConvergent,smul_eq_mul,show (σ:ℂ)-1-1=(σ:ℂ)-2 by ring] using hm
  have hc : ContinuousOn (fun u => (F u).re) (Ioi (0:ℝ)) := by
    intro u hu
    have hp := Complex.continuousAt_ofReal_cpow_const u ((σ:ℂ)-2) (Or.inr (ne_of_gt hu))
    have ha := (cubicThetaAveragedHeat_continuous cubicThetaRadialTestWeight hA).continuousAt
      (isOpen_Ioi.mem_nhds hu)
    exact (Complex.continuous_re.continuousAt.comp (hp.mul ha)).continuousWithinAt
  have hp : ∀ u∈Ioi (0:ℝ), 0<(F u).re := by
    intro u hu
    dsimp only [F]
    rw [cubicThetaRadialMellin_real_part σ hu]
    exact mul_pos (Real.rpow_pos_of_pos hu _) (cubicThetaAveragedHeat_test_re_pos hA hu)
  have hpos := cubicThetaPositive_setIntegral hc hi.re (fun u hu => (hp u hu).le)
    (x:=1) (by norm_num) (hp 1 (by norm_num))
  have hr := integral_re hi
  change (∫ u in Ioi (0:ℝ), (F u).re)=(∫ u in Ioi (0:ℝ), F u).re at hr
  rw [hr] at hpos
  rw [cubicThetaFourierRadialTest_mellin hh,mellin]
  simpa only [show (σ:ℂ)-1-1=(σ:ℂ)-2 by ring,smul_eq_mul] using hpos

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueWhittaker
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral residue observations have the same fixed
Whittaker kernel as the explicit arithmetic theta expansion. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoleRadialTest_whittaker {h : Eisenstein} (hh : h≠0) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierRadialTest h W (4/3)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        ∫ v in Ioi (2:ℝ), star (W v)*cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)/(v:ℂ)^3 := by
  rw [cubicThetaFourierRadialTest,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  rw [show star (W v)*(v:ℂ)^(4/3:ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t)/(v:ℂ)^3=
      star (W v)*((v:ℂ)^(4/3:ℂ)*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t))/(v:ℂ)^3 by ring,
    cubicThetaPoleHeat_whittaker hh (by linarith)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the actual residue's constant term and frequency lattice with
the normalization of Patterson's theta expansion. This does not identify
the nonzero arithmetic coefficients. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRowFrequency_index (h : Eisenstein) :
    cubicThetaFrequency (-lambdaE*h)=cubicThetaRowFrequency h := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  unfold cubicThetaFrequency cubicThetaRowFrequency
  push_cast
  rw [lambdaE_coe,h4]
  field_simp [traceLambda_ne_zero]
  linear_combination -(3*(h:ℂ))*hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowCompletionTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two integral completions of a primitive bottom row differ by the
actual level-three unipotent stabilizer. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_completion (h : Eisenstein)
    (g k : cubicThetaPrincipalGroup) (he : cubicThetaBottomRow g=cubicThetaBottomRow k)
    (p : CubicThetaPoint) :
    cubicThetaHorizontalCharacter h (g • p).val.1=
      cubicThetaHorizontalCharacter h (k • p).val.1 := by
  obtain ⟨w,rfl⟩ := cubicThetaBottomRow_equal_translation g k he
  rw [mul_smul]
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) (k • p).val).1=_
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
  have hw : ((3*w:Eisenstein):ℂ)=3*(w:ℂ) := by
    rw [Subalgebra.coe_mul]
    congr 1
  rw [hw]
  exact cubicThetaHorizontalCharacter_periodic h w (k • p).val.1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierProfileSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Poincare profiles with an actual nonzero horizontal character.
The completion phase is independent of the chosen primitive-row completion. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment

def cubicThetaFourierProfileTerm (h : Eisenstein) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  cubicThetaRadialProfileTerm r p W*
    cubicThetaHorizontalCharacter h (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) p).1

def cubicThetaFourierProfileSeries (h : Eisenstein) (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∑' r : CubicThetaBottomRow,cubicThetaFourierProfileTerm h r p W

lemma cubicThetaFourierProfileTerm_translate (h : Eisenstein) (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierProfileTerm h r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaFourierProfileTerm h (r.rightMul g) p W := by
  have hrow : cubicThetaBottomRow (r.completion*g)=cubicThetaBottomRow (r.rightMul g).completion := by
    rw [(r.rightMul g).completion_row]
    rfl
  have hc := cubicThetaHorizontalCharacter_completion h (r.completion*g)
    (r.rightMul g).completion hrow (⟨p,hp⟩:CubicThetaPoint)
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex (r.completion*g)) p).1=
    cubicThetaHorizontalCharacter h
      (cubicThetaMobius (cubicThetaPrincipalComplex (r.rightMul g).completion) p).1 at hc
  rw [map_mul,←cubicThetaMobius_comp _ _ hp] at hc
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex r.completion)
      (cubicThetaMobius (cubicThetaPrincipalComplex g) p)).1=
    cubicThetaHorizontalCharacter h
      (cubicThetaMobius (cubicThetaPrincipalComplex (r.rightMul g).completion) p).1 at hc
  unfold cubicThetaFourierProfileTerm
  rw [cubicThetaRadialProfileTerm_translate r g hp W,hc]
  ring

theorem cubicThetaFourierProfileSeries_automorphy (h : Eisenstein)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierProfileSeries h (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaFourierProfileSeries h p W := by
  unfold cubicThetaFourierProfileSeries
  simp_rw [cubicThetaFourierProfileTerm_translate h _ g hp W]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaFourierProfileTerm h r p W)

lemma cubicThetaFourierProfileTerm_zero (h : Eisenstein) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) (hz : W (r.height p)=0) :
    cubicThetaFourierProfileTerm h r p W=0 := by
  simp only [cubicThetaFourierProfileTerm,cubicThetaRadialProfileTerm,hz,mul_zero,zero_mul]

lemma cubicThetaFourierProfileTerm_continuousAt (h : Eisenstein) (r : CubicThetaBottomRow)
    (W : C_c(ℝ,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaFourierProfileTerm h r q W) p := by
  have hr := r.height_contDiffAt hp
  have hm := cubicThetaMobius_continuousAt (cubicThetaPrincipalComplex r.completion) hp
  exact (continuousAt_const.mul (W.continuous.continuousAt.comp hr.continuousAt)).mul
    ((cubicThetaHorizontalCharacter_continuous h).continuousAt.comp
      (continuousAt_fst.comp hm))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Additive conductors of the actual finite Fourier pairing. A function
that factors through a smaller residue ring has Fourier support in the
annihilator of the reduction kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem residueFourier_inflation_support {q d : Eisenstein} (hq : q≠0)
    [Fintype (Residues q)] (hd : d ∣ q) (f : Residues d → ℂ) (h : Eisenstein)
    (hF : (∑ x : Residues q, f (residueReduction hd x) * residueFourierChar q hq
      (Ideal.Quotient.mk (modulus q) h*x))≠0) : q ∣ d*h := by
  apply residueFourier_reduction_support hq _ h _ hF
  intro x b
  congr 1
  rw [map_add,map_mul,residueReduction_mk]
  have hz : Ideal.Quotient.mk (modulus d) d=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl d))
  rw [hz,zero_mul,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three local cubic Fourier factors. Positive powers are periodic
modulo three; the trivial cubic power is the exact Ramanujan factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFourier_period {p : Eisenstein} (hp : primaryPrime p)
    {n : ℕ} (hn : n≠0) (h : Eisenstein) :
    cubicThetaPrimeFourier p hp (n+3) h=cubicThetaPrimeFourier p hp n h := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeFourier_gaussSum hp (by omega),cubicThetaPrimeFourier_gaussSum hp hn,
    pow_add,cubicResidueChar_cube hp,mul_one]

lemma cubicThetaPrimeFourier_unit {p : Eisenstein} (hp : primaryPrime p)
    {n : ℕ} (hn : n≠0) (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeFourier p hp n h=
      star ((cubicSymbol p h)^n)*cubicThetaPrimeFourier p hp n 1 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hh
  rw [cubicThetaPrimeFourier_gaussSum hp hn,cubicThetaPrimeFourier_gaussSum hp hn]
  have he : (Ideal.Quotient.mk (modulus p)) h=(u:Residues p) := hu.symm
  rw [he,gaussSum_mulShift_eq,← MulChar.star_apply',MulChar.pow_apply' _ hn]
  rw [hu,cubicResidueChar_mk,← cubicSymbol_prime hp,map_one,AddChar.mulShift_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the first local cubic Fourier factor. The inverse
different in the additive pairing contributes exactly the cubic character
of lambda; the remaining Gauss sum is the original normalized one. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaResidueFourier_lambda {p : Eisenstein} (hp : primaryPrime p) :
    (residueFourierChar p hp.2.ne_zero).mulShift (Ideal.Quotient.mk (modulus p) lambdaE)=
      residueAddChar p hp.2.ne_zero := by
  ext x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AddChar.mulShift_apply,← map_mul,residueFourierChar_mk,residueAddChar_mk,
    additivePhase_fourierChar]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  field_simp [traceLambda_ne_zero]

theorem cubicThetaPrimeFourier_one_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFourier p hp 1 1=
      cubicSymbol p lambdaE*(Real.sqrt (norm p):ℂ)*gauss p := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime (primary_coprime_lambda hp.1)
  have hg := gaussSum_mulShift (cubicResidueChar p hp) (residueFourierChar p hp.2.ne_zero) u
  have hc : cubicResidueChar p hp (u:Residues p)=cubicSymbol p lambdaE := by
    rw [hu,cubicResidueChar_mk,← cubicSymbol_prime hp]
  rw [hu,cubicThetaResidueFourier_lambda hp] at hg
  have hn : gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero)=
      (Real.sqrt (norm p):ℂ)*gauss p := by
    rw [gauss_prime hp,gaussAtPrime_eq_gaussSum hp]
    have hpN : (Real.sqrt (norm p):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hp.2.ne_zero)))
    rw [mul_inv_cancel_left₀ hpN]
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),map_one,AddChar.mulShift_one,pow_one]
  calc
    _ = cubicSymbol p lambdaE*gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero) := by
      rw [← hg]
      congr 1
      simpa only [hu] using hc
    _ = _ := by rw [hn]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeConjugate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second local cubic Fourier factor is the conjugate of the first.
The additive character uses the same inverse-different normalization. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFourier_two_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFourier p hp 2 1=star (cubicThetaPrimeFourier p hp 1 1) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicResidueChar p hp
  let ψ := residueFourierChar p hp.2.ne_zero
  have hi : χ^2=χ⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact cubicResidueChar_cube hp
  have hm : χ (-1:Residues p)=1 := by
    have he : (-1:Residues p)=Ideal.Quotient.mk (modulus p) (-1:Eisenstein) := by simp
    rw [he]
    change cubicResidueChar p hp (Ideal.Quotient.mk (modulus p) (-1:Eisenstein))=1
    rw [cubicResidueChar_mk,← cubicSymbol_prime hp,cubicSymbol_neg hp.1,cubicSymbol_prime hp]
    exact cubicSymbolAtPrime_one hp
  have hmi : χ⁻¹ (-1:Residues p)=1 := by
    rw [← MulChar.star_apply',hm,star_one]
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),cubicThetaPrimeFourier_gaussSum hp (by norm_num)]
  simp only [map_one,AddChar.mulShift_one,pow_one]
  change gaussSum (χ^2) ψ=star (gaussSum χ ψ)
  rw [star_gaussSum_eq,hi]
  have he := mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ
  rw [hmi,one_mul] at he
  exact he.symm

theorem cubicThetaPrimeFourier_two_unit {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeFourier p hp 2 h=
      cubicSymbol p h*star (cubicThetaPrimeFourier p hp 1 1) := by
  rw [cubicThetaPrimeFourier_unit hp (by norm_num) h hh,cubicThetaPrimeFourier_two_one hp,
    cubicSymbol_sq_eq_star hp.1,star_star]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAdditiveGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic Gauss factors with the additive character of the original
arithmetic normalization. These are the off-diagonal finite factors needed
in the unramified critical intertwining calculation. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeAdditiveGauss_fourier {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) :
    cubicThetaPrimeAdditiveGauss p hp n h=cubicThetaPrimeFourier p hp n (lambdaE*h) := by
  unfold cubicThetaPrimeAdditiveGauss cubicThetaPrimeFourier
  apply tsum_congr
  intro y
  rw [←cubicThetaResidueFourier_lambda hp,AddChar.mulShift_apply,
    map_mul (Ideal.Quotient.mk (modulus p)) lambdaE h]
  congr 2
  ring

lemma cubicThetaPrimeAdditiveGauss_two {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 2 h=star (cubicThetaPrimeAdditiveGauss p hp 1 h) := by
  have hcop : IsCoprime p (lambdaE*h) := (primary_coprime_lambda hp.1).mul_right hh
  rw [cubicThetaPrimeAdditiveGauss_fourier,cubicThetaPrimeAdditiveGauss_fourier,
    cubicThetaPrimeFourier_two_unit hp _ hcop,cubicThetaPrimeFourier_unit hp (by norm_num) _ hcop,
    pow_one,star_mul,star_star]
  ring

lemma cubicThetaPrimeAdditiveGauss_product {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 1 h*cubicThetaPrimeAdditiveGauss p hp 2 h=(norm p:ℂ) := by
  rw [cubicThetaPrimeAdditiveGauss_two hp h hh]
  have hn := cubicThetaPrimeAdditiveGauss_norm hp h hh
  have hq := Real.sq_sqrt (norm_nonneg p)
  rw [Complex.star_def,Complex.mul_conj',hn,←Complex.ofReal_pow,hq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussParity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evenness of the genuine arithmetic Fourier coefficients follows by
negating the lower-left row and the frequency simultaneously. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_neg_c (c d : Eisenstein) :
    cubicThetaEisensteinWeight (-c) d=cubicThetaEisensteinWeight c d := by
  have hc : IsCoprime (-c) d ↔ IsCoprime c d :=
    ⟨fun h => by simpa using h.neg_left,fun h => h.neg_left⟩
  unfold cubicThetaEisensteinWeight
  rw [hc]
  split_ifs with h
  · exact cubicSymbol_neg h.1 c
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The difference of incoming cutoffs at heights one and two is a
literal compact smooth automorphic section. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

def cubicThetaIncomingWindowTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicThetaIncomingWindowCutoff (r.height p)*cubicThetaEisensteinTerm r p s

def cubicThetaIncomingWindow (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaIncomingWindowTerm r p s

lemma cubicThetaIncomingWindowTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingWindowTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingWindowTerm (r.rightMul g) p s := by
  rw [cubicThetaIncomingWindowTerm,cubicThetaIncomingWindowTerm,
    ← CubicThetaBottomRow.height_rightMul r g hp,cubicThetaEisensteinTerm_translate r g hp s]
  ring

theorem cubicThetaIncomingWindow_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingWindow (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingWindow p s := by
  unfold cubicThetaIncomingWindow
  simp_rw [cubicThetaIncomingWindowTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq
    (fun r => cubicThetaIncomingWindowTerm r p s)

theorem cubicThetaIncomingWindow_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaIncomingWindow p s=∑ r∈S, cubicThetaIncomingWindowTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ?_⟩
  apply tsum_eq_sum
  intro r hr
  unfold cubicThetaIncomingWindowTerm
  rw [cubicThetaIncomingWindowCutoff_low (hS p hp r hr).le,zero_mul]

lemma cubicThetaIncomingWindowTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaIncomingWindowTerm r q s) p := by
  have hh := r.height_contDiffAt hp
  have hc := cubicThetaIncomingWindowCutoff_smooth.contDiffAt.comp p hh
  have hpow := (cubicThetaHeightPower_analytic s (r.height_pos hp)).contDiffAt.comp p hh
  exact hc.mul (contDiffAt_const.mul hpow)

theorem cubicThetaIncomingWindow_contDiffOn (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaIncomingWindow p s) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaIncomingWindow_compact_sum hK hKpos
  have he : (fun q => cubicThetaIncomingWindow q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaIncomingWindowTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaIncomingWindowTerm r q s) p :=
    ContDiffAt.sum (fun r _ => cubicThetaIncomingWindowTerm_contDiffAt r s hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

def cubicThetaIncomingWindowSection (s : ℂ) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaIncomingWindow p.val s,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaIncomingWindow_contDiffOn s).contDiffAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.continuousAt.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaIncomingWindow_automorphy g p.property s⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high defect is an actual compact automorphic section supported
in the single principal cusp above height two. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaHighWindowSeries_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaHighWindowSeries p s=∑ r∈S, cubicThetaHighWindowTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ?_⟩
  apply tsum_eq_sum
  intro r hr
  unfold cubicThetaHighWindowTerm
  rw [cubicThetaHighWindowForcing_low s (by linarith [hS p hp r hr]),mul_zero]

lemma cubicThetaHighWindowSeries_continuousOn (s : ℂ) :
    ContinuousOn (fun p => cubicThetaHighWindowSeries p s) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaHighWindowSeries_compact_sum hK hKpos
  have he : (fun q => cubicThetaHighWindowSeries q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContinuousAt (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (continuousAt_const.mul ((cubicThetaHighWindowForcing_continuous s).continuousAt.comp
        (r.height_contDiffAt hp).continuousAt)).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

def cubicThetaHighWindowSection (s : ℂ) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaHighWindowSeries p.val s,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaHighWindowSeries_continuousOn s).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaHighWindowSeries_automorphy g p.property s⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact incoming window satisfies its exact global differential
equation, with the original forcing minus the high annular forcing. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingWindowTerm_equation (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x y v) s+
        cubicThetaForcingTerm r (cubicThetaCartesianPoint x y v) s-
        cubicThetaHighWindowTerm r (cubicThetaCartesianPoint x y v) s := by
  have hf : ContDiffAt ℝ 2 (cubicThetaWindowHeight s)
      (cubicThetaRowHeightCoordinates r x y v) :=
    (cubicThetaWindowHeight_smooth s).contDiffAt.of_le (by norm_num)
  have he : (fun a b t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s)=
      (fun a b t => star r.phase*cubicThetaWindowHeight s
        (cubicThetaRowHeightCoordinates r a b t)) := by
    funext a b t
    unfold cubicThetaIncomingWindowTerm cubicThetaEisensteinTerm
      cubicThetaWindowHeight cubicThetaRowHeightCoordinates
    ring
  rw [he,cubicThetaHyperbolicOperator_const_mul,cubicThetaRowHeight_operator r x y hv hf,
    cubicThetaWindowHeight_equation s 0 0]
  unfold cubicThetaIncomingWindowTerm cubicThetaEisensteinTerm cubicThetaWindowHeight
    cubicThetaForcingTerm cubicThetaHighWindowTerm cubicThetaRowHeightCoordinates
  ring

lemma window_coordinate_smooth (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint t y v) s) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x t v) s) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x y t) s) v := by
  have hr := cubicThetaIncomingWindowTerm_contDiffAt r s (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  have ht : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(hr.comp x hx.contDiffAt).of_le (by norm_num),
    (hr.comp y hy.contDiffAt).of_le (by norm_num),
    (hr.comp v ht.contDiffAt).of_le (by norm_num)⟩

lemma cubicThetaIncomingWindowFinite_equation (S : Finset CubicThetaBottomRow)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => ∑ r∈S, cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*(∑ r∈S, cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x y v) s)+
        (∑ r∈S, cubicThetaForcingTerm r (cubicThetaCartesianPoint x y v) s)-
        ∑ r∈S, cubicThetaHighWindowTerm r (cubicThetaCartesianPoint x y v) s := by
  have hcoords := fun r => window_coordinate_smooth r s x y hv
  rw [cubicThetaHyperbolicOperator_finite S
    (fun r a b t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s) x y v
    (fun r _ => (hcoords r).1) (fun r _ => (hcoords r).2.1) (fun r _ => (hcoords r).2.2)]
  simp_rw [cubicThetaIncomingWindowTerm_equation _ s x y hv]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]

theorem cubicThetaIncomingWindow_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingWindow (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingWindow (cubicThetaCartesianPoint x y v) s+
        cubicThetaForcingSeries (cubicThetaCartesianPoint x y v) s-
        cubicThetaHighWindowSeries (cubicThetaCartesianPoint x y v) s := by
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood
    (p:=cubicThetaCartesianPoint x y v) hv
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hKpos
  have hw (p) (hp : p∈K) : cubicThetaIncomingWindow p s=∑ r∈S, cubicThetaIncomingWindowTerm r p s := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_left (cubicThetaIncomingWindowCutoff_low (hS p hp r hr).le) _
  have hf (p) (hp : p∈K) : cubicThetaForcingSeries p s=∑ r∈S, cubicThetaForcingTerm r p s := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (cubicThetaIncomingForcing_zero s (Or.inl (hS p hp r hr)))
  have hh (p) (hp : p∈K) : cubicThetaHighWindowSeries p s=∑ r∈S, cubicThetaHighWindowTerm r p s := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s (by linarith [hS p hp r hr]))
  have he : (fun p => cubicThetaIncomingWindow p s)=ᶠ[𝓝 (cubicThetaCartesianPoint x y v)]
      (fun p => ∑ r∈S, cubicThetaIncomingWindowTerm r p s) := by
    filter_upwards [hKn] with p hp
    exact hw p hp
  have hpK : cubicThetaCartesianPoint x y v∈K := mem_of_mem_nhds hKn
  rw [cubicThetaHyperbolicOperator_germ x y v he,
    cubicThetaIncomingWindowFinite_equation S s x y hv,
    ← hw _ hpK,← hf _ hpK,← hh _ hpK]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexRadialTest
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial tests separate the Fourier heat kernel at every
parameter in Re(s)>1. The test may depend on the parameter. -/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaComplexRadialTest_nonzero {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ W : C_c(ℝ,ℂ), (∀ v≤(2:ℝ), W v=0) ∧ cubicThetaFourierRadialTest h W s≠0 := by
  let A := cubicThetaRowHeatScale h
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  let F (v : ℝ) := cubicThetaComplexHeightIntegral s A (v:ℂ)/(v:ℂ)^2
  have hc : ContinuousOn F (Ioi (2:ℝ)) := by
    intro v hv
    have hp : 0<v := by have := hv; change 2<v at this; linarith
    have hk := (cubicThetaComplexHeightIntegral_analytic s hA (z:=(v:ℂ)) (by simpa)).continuousAt
    exact ((hk.comp Complex.continuous_ofReal.continuousAt).div
      (Complex.continuous_ofReal.continuousAt.pow 2)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hp.ne'))).continuousWithinAt
  obtain ⟨v,hv,hn⟩ := cubicThetaHighHeat_nonzero hs hA
  have hFn : F v≠0 := div_ne_zero
    (mt (cubicThetaComplexHeightIntegral_real_zero_iff s A (by linarith)).mp hn)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (by linarith : v≠0)))
  by_contra hnone
  push Not at hnone
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hc.locallyIntegrableOn measurableSet_Ioi) (fun g hg hgc hgu => by
      let W : C_c(ℝ,ℂ) := {
        toFun := fun v => (g v:ℂ)
        continuous_toFun := Complex.continuous_ofReal.comp hg.continuous
        hasCompactSupport' := hgc.comp_left (g:=fun r : ℝ => (r:ℂ)) (by simp) }
      have hW : ∀ v≤(2:ℝ), W v=0 := by
        intro v hv
        have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun ht => (not_lt_of_ge hv) (hgu ht))
        change (g v:ℂ)=0
        rw [hz,Complex.ofReal_zero]
      have he : (∫ v : ℝ, g v • F v)=cubicThetaFourierRadialTest h W s := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (2:ℝ)) (fun v hv => by
          have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun ht => hv (hgu ht))
          rw [hz,zero_smul])]
        rw [cubicThetaFourierRadialTest_dilated]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        dsimp only [F]
        rw [cubicThetaComplexHeightIntegral_real]
        change (g v:ℂ)*((∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u)/(v:ℂ)^2)=
          star (g v:ℂ)/(v:ℂ)^2*(∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u)
        simp only [Complex.star_def,Complex.conj_ofReal]
        ring
      exact he.trans (hnone W hW))
  have hae' : F=ᵐ[volume.restrict (Ioi (2:ℝ))] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae hae] with t ht he
    exact he ht
  have he := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hc continuousOn_const
  exact hFn (he hv)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting an unramified primary factor from the actual Eisenstein
row weight. Common-factor zeros are retained in every identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_factor {u : Eisenstein} (hu : primary u)
    (c d : Eisenstein) :
    cubicThetaEisensteinWeight (u*c) d=
      cubicSymbol u d*cubicThetaEisensteinWeight c d := by
  by_cases hd : primary d
  · by_cases hcu : IsCoprime u d
    · unfold cubicThetaEisensteinWeight
      rw [IsCoprime.mul_left_iff,and_iff_right hcu]
      split_ifs with hcd
      · rw [cubicSymbol_mul_upper hd,cubic_reciprocity hd hu]
      · simp
    · have hz := cubicSymbol_eq_zero_of_not_isCoprime hu hcu
      have huc : ¬IsCoprime (u*c) d := fun h => hcu h.of_mul_left_left
      simp only [cubicThetaEisensteinWeight,huc,and_false,ite_false, if_false,hz,zero_mul]
  · simp [cubicThetaEisensteinWeight,hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRowRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local prime-power recurrences for the genuine arithmetic row coefficient. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSymbolFourier_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaSymbolFourier p hp.2.ne_zero h=cubicThetaPrimeFourier p hp 1 h := by
  unfold cubicThetaSymbolFourier cubicThetaPrimeFourier
  apply tsum_congr
  intro x
  rw [pow_one,cubicSymbol_prime hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeValuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique separation of an unramified prime power in an actual admissible
Eisenstein denominator. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimePowerDenominator (p : Eisenstein) (hp : primaryPrime p)
    (v : ℕ × CubicThetaPrimeFreeDenominator p) : CubicThetaDenominator :=
  ⟨p^v.1*v.2.val,dvd_mul_of_dvd_right v.2.property.1 _,
    mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) v.2.property.2.1⟩

theorem cubicThetaPrimePowerDenominator_bijective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Bijective (cubicThetaPrimePowerDenominator p hp) := by
  constructor
  · intro v w he
    have hv := congrArg Subtype.val he
    obtain ⟨hn,hc⟩ := cubicThetaPrimePower_unique hp.2.ne_zero v.2.property.2.2 w.2.property.2.2 hv
    exact Prod.ext hn (Subtype.ext hc)
  · intro c
    obtain ⟨n,d,hpd,he⟩ := WfDvdMonoid.max_power_factor c.property.2 hp.2.irreducible
    have hd0 : d≠0 := (mul_ne_zero_iff.mp (he ▸ c.property.2)).2
    have h3p : IsCoprime (3:Eisenstein) p :=
      isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
    have h3d : (3:Eisenstein) ∣ d := (h3p.pow_right).dvd_of_dvd_mul_left (he ▸ c.property.1)
    refine ⟨(n,⟨d,h3d,hd0,hpd⟩),?_⟩
    exact Subtype.ext he.symm

def cubicThetaPrimePowerDenominatorEquiv (p : Eisenstein) (hp : primaryPrime p) :
    (ℕ × CubicThetaPrimeFreeDenominator p) ≃ CubicThetaDenominator :=
  Equiv.ofBijective _ (cubicThetaPrimePowerDenominator_bijective hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five possible local rows at a cubically multiplied frequency. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFree_phaseCube {p : Eisenstein} (hp : primaryPrime p)
    (d : CubicThetaPrimeFreeDenominator p) :
    (cubicSymbol p (3*d.val)*cubicSymbol p d.val)^3=1 := by
  have hpd : IsCoprime p d.val := hp.2.coprime_iff_not_dvd.mpr d.property.2.2
  have hp3 : IsCoprime p (3:Eisenstein) :=
    (isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))).symm
  rw [mul_pow,cubicSymbol_cube_of_isCoprime hp.1 _ (hp3.mul_right hpd),
    cubicSymbol_cube_of_isCoprime hp.1 _ hpd,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeShiftRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three possible rows when a prime-free frequency is multiplied by
one primary prime. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFree_unit {p : Eisenstein} (hp : primaryPrime p)
    (d : CubicThetaPrimeFreeDenominator p) :
    cubicSymbol p d.val*star (cubicSymbol p d.val)=1 := by
  rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hp.1
    (hp.2.coprime_iff_not_dvd.mpr d.property.2.2)]
  norm_num

lemma cubicThetaPrimeFree_secondPhase {p : Eisenstein} (hp : primaryPrime p)
    (d : CubicThetaPrimeFreeDenominator p) :
    (cubicSymbol p (3*d.val)*cubicSymbol p d.val)^2*
      star (cubicSymbol p lambdaE)*star (cubicSymbol p d.val)=1 := by
  rw [cubicSymbol_mul_upper hp.1,mul_pow,mul_pow,cubicSymbol_sq_eq_star hp.1]
  have hd := cubicThetaPrimeFree_unit hp d
  have hl := congrArg star (cubicSymbol_three_lambda hp.1)
  rw [cubicSymbol_mul_upper hp.1,star_mul,star_one] at hl
  calc
    _ = (star (cubicSymbol p 3)*star (cubicSymbol p lambdaE))*
        (cubicSymbol p d.val*star (cubicSymbol p d.val))^2 := by
      rw [← cubicSymbol_sq_eq_star hp.1 d.val]
      ring
    _ = 1 := by rw [mul_comm (star (cubicSymbol p 3)),hl,hd]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeHeckeRelation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eliminate the two actual prime-free twists to obtain the unramified
three-frequency relation in the initial half-plane. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFactors_product {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaPrimeFirstFactor p s h*cubicThetaPrimeSecondFactor p s h=
      (norm p:ℂ)^2*((norm p:ℂ)^(-s))^3 := by
  have hc : cubicSymbol p h*star (cubicSymbol p h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hp.1
      (hp.2.coprime_iff_not_dvd.mpr hh)]
    norm_num
  have hg : gauss p*star (gauss p)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_gauss_of_squarefree hp.1 hp.2.squarefree]
    norm_num
  have hq : (Real.sqrt (norm p):ℂ)^2=(norm p:ℂ) := by
    exact_mod_cast Real.sq_sqrt (norm_nonneg p)
  unfold cubicThetaPrimeFirstFactor cubicThetaPrimeSecondFactor
  calc
    _ = (cubicSymbol p h*star (cubicSymbol p h))*(gauss p*star (gauss p))*
        (Real.sqrt (norm p):ℂ)^2*(norm p:ℂ)*((norm p:ℂ)^(-s))^3 := by ring
    _ = _ := by rw [hc,hg,hq]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeHeckeContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local three-frequency identity holds for the actual meromorphic
continuation, hence for its holomorphic pole-cleared representative. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaPrimeFirstFactor_analytic {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (s : ℂ) : AnalyticAt ℂ (fun z => cubicThetaPrimeFirstFactor p z h) s := by
  exact analyticAt_const.mul (cubicThetaPrimeNormPower_analytic hp s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCriticalFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the critical finite Gauss factors with the exact Euler factors
of the constructed arithmetic Fourier family. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeFirstFactor_critical {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeFirstFactor p (4/3) h=
      (cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ))*cubicThetaPrimeCriticalScale p := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have he : (norm p:ℂ)^(-(4/3:ℂ))=(norm p:ℂ)⁻¹*cubicThetaPrimeCriticalScale p := by
    unfold cubicThetaPrimeCriticalScale
    rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ hq]
    congr 1
    norm_num
  rw [cubicThetaPrimeFirstFactor,cubicThetaPrimeAdditiveGauss_one hp h hh,he]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primitive rows at the inverted cusp. This identifies the
actual transformed Eisenstein series before taking its constant term. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaInvertedTerm (r : CubicThetaInvertedRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicSymbol r.c r.d*(r.height p:ℂ)^s

theorem cubicThetaBottomRow_height_inverted (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p)=
      (cubicThetaInvertedRowEquiv r).height p := by
  rw [cubicThetaBottomRow_height_full r _ hp]
  simp only [cubicThetaFullInversion,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_zero,mul_one,mul_neg_one,
    zero_add,add_zero]
  rfl

theorem cubicThetaEisensteinTerm_inverted (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisensteinTerm r
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      cubicThetaInvertedTerm (cubicThetaInvertedRowEquiv r) p s := by
  rw [cubicThetaEisensteinTerm,CubicThetaBottomRow.phase,star_star,
    cubicThetaBottomRow_height_inverted r hp]
  unfold cubicThetaInvertedTerm
  change cubicSymbol r.d r.c*_ = cubicSymbol r.d (-r.c)*_
  rw [cubicSymbol_neg r.d_primary]

theorem cubicThetaEisenstein_inverted {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' r : CubicThetaInvertedRow, cubicThetaInvertedTerm r p s := by
  unfold cubicThetaEisenstein
  simp_rw [cubicThetaEisensteinTerm_inverted _ hp]
  exact cubicThetaInvertedRowEquiv.tsum_eq
    (fun r : CubicThetaInvertedRow => cubicThetaInvertedTerm r p s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedIncoming
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming cutoff vanishes at the inverted high cusp. The actual
inverted Eisenstein series is consequently square integrable on that strip. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInvertedRow_height_le_one (r : CubicThetaInvertedRow)
    {p : ℂ × ℝ} (hp : 1<p.2) : r.height p≤1 := by
  have hn := one_le_norm (primary_ne_zero r.c_primary)
  have hd : 0<Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2 := by
    nlinarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d),sq_nonneg (p.2-1)]
  change p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)≤1
  apply (div_le_one hd).mpr
  nlinarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d),sq_nonneg (p.2-1)]

theorem cubicThetaIncomingEisenstein_inverted_zero {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=0 := by
  have hz : ∀ r : CubicThetaBottomRow, cubicThetaIncomingTerm r
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=0 := by
    intro r
    unfold cubicThetaIncomingTerm
    rw [cubicThetaBottomRow_height_inverted r (by linarith),
      cubicThetaCuspCutoff_zero (cubicThetaInvertedRow_height_le_one _ hp),zero_mul]
  simp only [cubicThetaIncomingEisenstein,hz,tsum_zero]

lemma cubicThetaArithmeticRemainder_inverted {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s := by
  rw [cubicThetaArithmeticRemainder,cubicThetaIncomingEisenstein_inverted_zero hp,sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Fourier Poincare profiles remain genuine sections after a
positive dilation of the cutoff. No unit-height lower bound is required. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveFourierProfile_compact_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K,0<p.2) :
    ∃ S : Finset CubicThetaBottomRow,∀ p∈K,
      cubicThetaFourierProfileSeries h p W=∑ r∈S,cubicThetaFourierProfileTerm h r p W := by
  obtain ⟨S,hS⟩ := cubicThetaRows_compact_below hε hK hpos
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact cubicThetaFourierProfileTerm_zero h r p W (hW _ (hS p hp r hr).le)

lemma cubicThetaPositiveFourierProfile_continuousOn (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ContinuousOn (fun p => cubicThetaFourierProfileSeries h p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaPositiveFourierProfile_compact_sum h W hε hW hK hKpos
  have he : (fun q => cubicThetaFourierProfileSeries h q W)=ᶠ[𝓝 p]
      (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContinuousAt (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (cubicThetaFourierProfileTerm_continuousAt h r W hp).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

def cubicThetaPositiveFourierProfileSection (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaFourierProfileSeries h p.val W,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have hc := (cubicThetaPositiveFourierProfile_continuousOn h W hε hW).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact hc.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaFourierProfileSeries_automorphy h g p.property W⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripRepresentative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable coordinate representative of every positive-strip L2
vector, with its first and second moment densities on the literal cell. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment
variable {ε : ℝ}

def cubicThetaPositiveStripRepresentative (F : CubicThetaPositiveStripL2 ε) : ℂ × ℝ → ℂ :=
  Function.extend cubicThetaPointCoordinates (F : CubicThetaPoint → ℂ) 0

lemma cubicThetaPositiveStripRepresentative_coordinates (F : CubicThetaPositiveStripL2 ε) (p : CubicThetaPoint) :
    cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p)=F p :=
  cubicThetaPointInclusion_measurableEmbedding.injective.extend_apply _ _ _

lemma cubicThetaPositiveStripRepresentative_measurable (F : CubicThetaPositiveStripL2 ε) :
    StronglyMeasurable (cubicThetaPositiveStripRepresentative F) :=
  cubicThetaPointInclusion_measurableEmbedding.stronglyMeasurable_extend
    (Lp.stronglyMeasurable F) stronglyMeasurable_zero

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth positive-cutoff Fourier profiles are actual compact smooth
sections, hence belong to the automorphic energy and mass spaces. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_contDiff (h : Eisenstein) :
    ContDiff ℝ ∞ (cubicThetaHorizontalCharacter h) := by
  unfold cubicThetaHorizontalCharacter
  simp only [Real.fourierChar_apply]
  unfold tracePair
  have hr : ContDiff ℝ ∞ (fun z : ℂ => 2*Real.pi*(2*(z*cubicThetaRowFrequency h).re)) :=
    contDiff_const.mul (contDiff_const.mul
      (Complex.reCLM.contDiff.comp (contDiff_id.mul contDiff_const)))
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const)

lemma cubicThetaFourierProfileTerm_contDiffAt (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaFourierProfileTerm h r q W) p := by
  have hrad : ContDiffAt ℝ ∞ (fun q => cubicThetaRadialProfileTerm r q W) p :=
    contDiffAt_const.mul (hsm.contDiffAt.comp p (r.height_contDiffAt hp))
  exact hrad.mul ((cubicThetaHorizontalCharacter_contDiff h).contDiffAt.comp p
    (contDiffAt_fst.comp p (cubicThetaMobius_contDiffAt _ hp)))

lemma cubicThetaPositiveFourierProfile_contDiffOn (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaFourierProfileSeries h p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaPositiveFourierProfile_compact_sum h W hε hW hK hKpos
  have he : (fun q => cubicThetaFourierProfileSeries h q W)=ᶠ[𝓝 p]
      (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) p :=
    ContDiffAt.sum (fun r _ => cubicThetaFourierProfileTerm_contDiffAt h W hsm r hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaObservationScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric normalization of the actual Whittaker observation
under multiplication of its arithmetic frequency. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPoleWeight_mul {u h : Eisenstein} (hu : u≠0) (hh : h≠0) :
    2*(cubicThetaRowHeatScale (u*h))^(1/6:ℝ)/‖cubicThetaRowFrequency (u*h)‖=
      (norm u)^(-(1/3:ℝ))*(2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖) := by
  have he := cubicThetaPoleFactor_mul hu hh
  have hn : (norm u)^(-(1/3:ℝ))=‖(u:ℂ)‖^(-(2/3:ℝ)) := by
    rw [show norm u=‖(u:ℂ)‖^2 from Complex.normSq_eq_norm_sq _,
      ←Real.rpow_natCast ‖(u:ℂ)‖ 2,←Real.rpow_mul (_root_.norm_nonneg _)]
    norm_num
  simpa only [←hn] using he

lemma cubicThetaPoleWeight_cube_mul {p h : Eisenstein} (hp : p≠0) (hh : h≠0) :
    2*(cubicThetaRowHeatScale (p^3*h))^(1/6:ℝ)/‖cubicThetaRowFrequency (p^3*h)‖=
      (norm p)⁻¹*(2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖) := by
  rw [cubicThetaPoleWeight_mul (pow_ne_zero 3 hp) hh,eisenstein_norm_pow,
    ← Real.rpow_natCast (norm p) 3,← Real.rpow_mul (norm_nonneg p)]
  norm_num [Real.rpow_neg_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoleRadialScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous scaling of the frequency and radial test at the cubic pole. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoleRadialTest_weight {h : Eisenstein} (hh : h≠0) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierRadialTest h W (4/3)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        cubicThetaPoleRadialWeightIntegral h W := by
  rw [cubicThetaPoleRadialTest_whittaker hh]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  ring

theorem cubicThetaPoleRadialTest_scale {a h : Eisenstein} (ha : a≠0) (hh : h≠0)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(a:ℂ)‖,W v=0) :
    cubicThetaFourierRadialTest (a*h)
        (cubicThetaRadialWeightScale ‖(a:ℂ)‖
          (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W) (4/3)=
      ((‖(a:ℂ)‖:ℂ)^(4/3:ℂ))*cubicThetaFourierRadialTest h W (4/3) := by
  have hr : 0<‖(a:ℂ)‖ := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hp : ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖^2=‖(a:ℂ)‖^(4/3:ℝ) := by
    rw [←Real.rpow_natCast ‖(a:ℂ)‖ 2,←Real.rpow_add hr]
    norm_num
  rw [cubicThetaPoleRadialTest_weight (mul_ne_zero ha hh),
    cubicThetaPoleRadialTest_weight hh,cubicThetaPoleFactor_mul ha hh,
    cubicThetaPoleRadialWeightIntegral_scale ha h W hW]
  rw [show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hr.le]
  push_cast
  have hpC := congrArg (fun x : ℝ => (x:ℂ)) hp
  push_cast at hpC
  linear_combination
    ((2:ℂ)*(((cubicThetaRowHeatScale h)^(1/6:ℝ) :ℝ):ℂ)/
      (‖cubicThetaRowFrequency h‖:ℂ)*cubicThetaPoleRadialWeightIntegral h W)*hpC

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingCompactIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact strip contribution of the incoming arithmetic series is
entire in the spectral parameter. It contributes no pole to Fourier tests. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaIncomingTerm_point_continuous (r : CubicThetaBottomRow) (s : ℂ) :
    Continuous (fun p : CubicThetaPoint => cubicThetaIncomingTerm r p.val s) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((cubicThetaIncomingTerm_contDiffAt r s p.property).continuousAt.comp
    continuous_subtype_val.continuousAt)

lemma cubicThetaRowLogHeight_point_continuous (r : CubicThetaBottomRow) :
    Continuous (fun p : CubicThetaPoint => Real.log (r.height p.val)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (((r.height_contDiffAt p.property).continuousAt.log (r.height_pos p.property).ne').comp
    continuous_subtype_val.continuousAt)

lemma cubicThetaIncomingTerm_exponential (r : CubicThetaBottomRow) (p : CubicThetaPoint) (s : ℂ) :
    cubicThetaIncomingTerm r p.val s=cubicThetaIncomingTerm r p.val 0*
      Complex.exp (s*(Real.log (r.height p.val):ℂ)) := by
  have hp := r.height_pos p.property
  simp only [cubicThetaIncomingTerm,cubicThetaEisensteinTerm,Complex.cpow_zero,mul_one]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),←Complex.ofReal_log hp.le]
  rw [mul_comm (Real.log (r.height p.val):ℂ) s]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine meromorphic Fourier observable at any positive cutoff.
Its incoming correction is entire and its residue is the actual global mass pairing. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaIncoming_point_continuous (s : ℂ) :
    Continuous (fun p : CubicThetaPoint => cubicThetaIncomingEisenstein p.val s) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (((cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).continuousAt.comp
      continuous_subtype_val.continuousAt)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullEisensteinFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual initial Eisenstein Fourier coefficient on every positive
horosphere, including below the injective cusp. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaEisensteinSection (s : ℂ) (hs : 2 < s.re) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaEisenstein p.val s,by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaEisenstein_continuousAt hs p.property).comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaEisenstein_automorphy g p.property s⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveRadialNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial normalization of the full positive-height Fourier observable. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPositiveRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ)) (ε : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Ioi ε,star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveRadialMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full positive-height radial Fourier factor is entire. All
integral interchanges retain the positive cutoff rather than discarding it. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveRadialTest_dilated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    cubicThetaPositiveRadialTest h W ε s=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^2*
        (∫ u in Ioi (0:ℝ),(u:ℂ)^(s-2)*cubicThetaLinearHeat v (cubicThetaRowHeatScale h) u) := by
  unfold cubicThetaPositiveRadialTest
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hv0 : 0<v := hε.trans hv
  have hd := cubicThetaHeat_height_dilation hv0 (cubicThetaRowHeatScale h) s
  calc
    _ = star (W v)/(v:ℂ)^3*((v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)) := by ring
    _ = _ := by
      rw [hd]
      field_simp [Complex.ofReal_ne_zero.mpr hv0.ne']

theorem cubicThetaPositiveRadialTest_mellin {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    cubicThetaPositiveRadialTest h W ε s=
      mellin (cubicThetaPositiveAveragedHeat W ε (cubicThetaRowHeatScale h)) (s-1) := by
  rw [cubicThetaPositiveRadialTest_dilated h W hε]
  have hi := cubicThetaPositiveRadialMellin_integrable W hε (cubicThetaRowHeatScale_pos hh) s
  calc
    _ = ∫ v in Ioi ε,∫ u in Ioi (0:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      unfold cubicThetaRadialMellinIntegrand
      ring
    _ = ∫ u in Ioi (0:ℝ),∫ v in Ioi ε,
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) :=
      integral_integral_swap hi
    _ = _ := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards with u
      simp only [show s-1-1=s-2 by ring,smul_eq_mul,cubicThetaPositiveAveragedHeat]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold cubicThetaRadialMellinIntegrand
      ring

theorem cubicThetaPositiveRadialTest_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) :
    Differentiable ℂ (cubicThetaPositiveRadialTest h W ε) := by
  have he : cubicThetaPositiveRadialTest h W ε=
      (fun s : ℂ => mellin (cubicThetaPositiveAveragedHeat W ε (cubicThetaRowHeatScale h)) (s-1)) :=
    funext (cubicThetaPositiveRadialTest_mellin hh W hε)
  rw [he]
  exact (cubicThetaPositiveAveragedHeat_mellin_entire W hε (cubicThetaRowHeatScale_pos hh)).comp
    (differentiable_id.sub_const 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositivePoleScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling of the actual pole kernel for arbitrary positive-cutoff tests. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaFullPoleWeightIntegral (h : Eisenstein) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
    cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)

lemma cubicThetaPositivePoleRadialTest_weight {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    cubicThetaPositiveRadialTest h W ε (4/3)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        cubicThetaFullPoleWeightIntegral h W := by
  unfold cubicThetaFullPoleWeightIntegral
  rw [←cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW]
  rw [cubicThetaPositiveRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hv0 : 0<v := hε.trans hv
  rw [show star (W v)*(v:ℂ)^(4/3:ℂ)*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t)/(v:ℂ)^3=
      star (W v)*((v:ℂ)^(4/3:ℂ)*
        (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t))/(v:ℂ)^3 by ring,
    cubicThetaPoleHeat_whittaker hh hv0]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGramCubeResidueBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cubic-frequency residue is controlled by the exact
prime-free Gram correction. No bound for that correction is assumed. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_pole_scale {p : Eisenstein} (hp : primaryPrime p) :
    (‖((p^3:Eisenstein):ℂ)‖:ℂ)^(4/3:ℂ)=(norm p:ℂ)^2 := by
  have hu : 0<‖(p:ℂ)‖ := norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))
  have hn : ‖((p^3:Eisenstein):ℂ)‖=‖(p:ℂ)‖^3 := by
    change ‖(p:ℂ)^3‖=‖(p:ℂ)‖^3
    exact norm_pow _ _
  have he : (‖(p:ℂ)‖^3)^(4/3:ℝ)=(norm p)^2 := by
    rw [←Real.rpow_natCast ‖(p:ℂ)‖ 3,←Real.rpow_mul hu.le]
    norm_num
    rw [show norm p=‖(p:ℂ)‖^2 from Complex.normSq_eq_norm_sq _]
    ring
  rw [hn,show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,
    ←Complex.ofReal_cpow (pow_nonneg hu.le 3),he,Complex.ofReal_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootStripBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal cusp strip has at most one representative in each orbit of
any subgroup of the principal group. Its mass is bounded by fundamental-domain
mass, also for the cubic-root cover. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace CubicFirstMoment

lemma cubicThetaInjective_subgroup_disjoint (K : Subgroup cubicThetaPrincipalGroup)
    {S : Set CubicThetaPoint} (hS : InjOn cubicThetaQuotientMap S) :
    Pairwise (fun g h : K => Disjoint (g • S) (h • S)) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  change g.val • a=x at hga
  change h.val • b=x at hgb
  have he : (h.val⁻¹*g.val) • a=b := by
    rw [mul_smul]
    rw [hga,←hgb]
    exact inv_smul_smul h.val b
  have hq : cubicThetaQuotientMap b=cubicThetaQuotientMap a :=
    cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mpr ⟨h.val⁻¹*g.val,he⟩
  have hab : b=a := hS hb ha hq
  have hone := cubicThetaPrincipal_fixed_eq_one (h.val⁻¹*g.val) a (he.trans hab)
  exact hgh (Subtype.ext (inv_mul_eq_one.mp hone).symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootHorizontal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite cubic-root projections select the corresponding
horizontal Fourier frequencies. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCubeResidueFourier_sum {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k j : Residues (p^3)) (c : ℂ) :
    (∑ r : Residues (p^3),star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
      (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (r*j)*c))=
      (if j=k then (norm (p^3):ℂ) else 0)*c := by
  classical
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  have he (r : Residues (p^3)) : star (ψ (k*r))*(ψ (r*j)*c)=
      (ψ (r*j)*star (ψ (r*k)))*c := by
    rw [mul_comm r k]
    ac_rfl
  change (∑ r : Residues (p^3),star (ψ (k*r))*(ψ (r*j)*c))=_
  simp_rw [he]
  rw [←Finset.sum_mul,cubicThetaResidueFourier_orthogonal (p^3) (pow_ne_zero 3 hp.2.ne_zero) j k]
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    exact congrArg (fun x : ℝ => (x:ℂ)) (normNat_cast (p^3))
  rw [hcard]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact observation scaling under the once-cubic dilation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_height_one {p : Eisenstein} (hp : primaryPrime p) :
    1≤‖(p:ℂ)‖^3 := by
  have hn := one_le_norm hp.2.ne_zero
  change 1≤Complex.normSq (p:ℂ) at hn
  rw [Complex.normSq_eq_norm_sq] at hn
  have hr : 1≤‖(p:ℂ)‖ := by nlinarith [_root_.norm_nonneg (p:ℂ)]
  exact one_le_pow₀ hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeResidueTestWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A high radial test adapted to the cubic dilation. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPrimeCubeResidueTestWeight {p : Eisenstein} (hp : primaryPrime p) : C_c(ℝ,ℂ) :=
  cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)⁻¹
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)))
    cubicThetaRadialTestWeight

lemma cubicThetaPrimeCubeResidueTestWeight_low {p : Eisenstein} (hp : primaryPrime p)
    {v : ℝ} (hv : v≤2*‖(p:ℂ)‖^3) : cubicThetaPrimeCubeResidueTestWeight hp v=0 := by
  change cubicThetaRadialTestWeight ((‖(p:ℂ)‖^3)⁻¹*v)=0
  apply cubicThetaRadialTestWeight_low
  rw [mul_comm,←div_eq_mul_inv,div_le_iff₀
    (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp))]
  exact hv

lemma cubicThetaPrimeCubeResidueTestWeight_scale {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
      (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp))
      (cubicThetaPrimeCubeResidueTestWeight hp)=cubicThetaRadialTestWeight := by
  ext v
  change cubicThetaRadialTestWeight ((‖(p:ℂ)‖^3)⁻¹*(‖(p:ℂ)‖^3*v))=_
  rw [inv_mul_cancel_left₀ (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)).ne']

lemma cubicThetaPrimeCubeResidueTestWeight_radial_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaFourierRadialTest h (cubicThetaPrimeCubeResidueTestWeight hp) (4/3)≠0 := by
  have he := cubicThetaPoleRadialTest_scale (pow_ne_zero 3 hp.2.ne_zero) hh
    (cubicThetaPrimeCubeResidueTestWeight hp) (by
      intro v hv
      apply cubicThetaPrimeCubeResidueTestWeight_low hp
      simpa only [Subalgebra.coe_pow,norm_pow] using hv)
  simp only [Subalgebra.coe_pow,norm_pow] at he
  rw [cubicThetaPrimeCubeResidueTestWeight_scale hp] at he
  intro hz
  rw [hz,mul_zero] at he
  have hpos := cubicThetaFourierRadialTest_real_pos
    (mul_ne_zero (pow_ne_zero 3 hp.2.ne_zero) hh) (4/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hpos
  rw [he,Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact high-cusp forcing is a genuine smooth test section. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaHighWindowSeries_smooth (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaHighWindowSeries p s) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaHighWindowSeries_compact_sum hK hKpos
  have he : (fun q => cubicThetaHighWindowSeries q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) p := by
    apply ContDiffAt.sum
    intro r _
    exact contDiffAt_const.mul ((cubicThetaHighWindowForcing_smooth s).contDiffAt.comp p
      (r.height_contDiffAt hp))
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeResidueObstruction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The critical local image condition is exactly the two missing
unramified residue identities. Neither identity is assumed here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCriticalGauss_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 1 h≠0 := by
  intro hz
  have he := cubicThetaPrimeAdditiveGauss_product hp h hh
  rw [hz,zero_mul] at he
  exact (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne') he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightedResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unramified coefficient laws for the actual arithmetic residue in
the Whittaker normalization. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNorm_cube_cpow (a : Eisenstein) :
    (norm (a^3):ℂ)^(-(1/3:ℂ))=(norm a:ℂ)⁻¹ := by
  have hcast : ((norm a^3:ℝ):ℂ)^(-(1/3:ℂ))=((norm a^3)^(-(1/3:ℝ)):ℝ) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (pow_nonneg (norm_nonneg a) 3) (-(1/3:ℝ))).symm
  rw [eisenstein_norm_pow,hcast,←Complex.ofReal_inv]
  congr 1
  rw [←Real.rpow_natCast (norm a) 3,←Real.rpow_mul (norm_nonneg a)]
  norm_num [Real.rpow_neg_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResiduePrimarySupport
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero primary residue has genuine squarefree/cube support.
Repeated prime cubes are removed by the proved arithmetic periodicity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_primary_cube {p : Eisenstein} (hp : primary p) : primary (p^3) := by
  rw [primary_iff_residue_one,map_pow,((primary_iff_residue_one p).mp hp),one_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedRowConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ramified row weight has conductor dividing nine times its primary
part. Consequently the lambda exponent of a nonzero Fourier row is bounded
by the lambda exponent of its frequency plus two. These are finite character
identities, with the original zero extension retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_lambda_pow (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k) a=
      if primary a then (cubicSymbol a lambdaE)^k else 0 := by
  unfold cubicThetaEisensteinWeight
  by_cases ha : primary a
  · rw [ite_eq_left ⟨ha,(primary_coprime_lambda ha).symm.pow_left⟩,ite_eq_left ha,
      cubicSymbol_pow_upper ha]
  · rw [ite_eq_right (fun h => ha h.1),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_lambda_periodic (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k) (a+9*b)=
      cubicThetaEisensteinWeight (lambdaE^k) a := by
  have hp : primary (a+9*b) ↔ primary a := by
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t-3*b,by linear_combination ht⟩
    · rintro ⟨t,ht⟩
      exact ⟨t+3*b,by linear_combination ht⟩
  rw [cubicThetaEisensteinWeight_lambda_pow,cubicThetaEisensteinWeight_lambda_pow]
  by_cases ha : primary a
  · rw [ite_eq_left (hp.mpr ha),ite_eq_left ha,
      cubicSymbol_lambda_periodic (hp.mpr ha) ha ⟨b,by ring⟩]
  · rw [ite_eq_right (fun h => ha (hp.mp h)),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_ramified_periodic {u : Eisenstein}
    (hu : primary u) (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k*u) (a+9*u*b)=
      cubicThetaEisensteinWeight (lambdaE^k*u) a := by
  rw [mul_comm (lambdaE^k) u,cubicThetaEisensteinWeight_factor hu,
    cubicThetaEisensteinWeight_factor hu]
  have hc : cubicSymbol u (a+9*u*b)=cubicSymbol u a := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    exact ⟨9*b,by ring⟩
  rw [hc,show a+9*u*b=a+9*(u*b) by ring,
    cubicThetaEisensteinWeight_lambda_periodic]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedRowInflation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reduce every ramified row to one fixed residue ring. Only three
ramified exponents remain in its weight; the frequency and primary part
are retained exactly. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_lambda_mod (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k) a=
      cubicThetaEisensteinWeight (lambdaE^(k%3)) a := by
  rw [cubicThetaEisensteinWeight_lambda_pow,cubicThetaEisensteinWeight_lambda_pow]
  by_cases ha : primary a
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hc := cubicSymbol_cube_of_isCoprime ha lambdaE (primary_coprime_lambda ha)
    conv_lhs => rw [← Nat.mod_add_div k 3]
    rw [pow_add,pow_mul,hc,one_pow,mul_one]
  · rw [ite_eq_right ha,ite_eq_right ha]

lemma cubicThetaEisensteinWeight_ramified_mod {u : Eisenstein}
    (hu : primary u) (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight (lambdaE^k*u) a=
      cubicThetaEisensteinWeight (lambdaE^(k%3)*u) a := by
  rw [mul_comm (lambdaE^k) u,mul_comm (lambdaE^(k%3)) u,
    cubicThetaEisensteinWeight_factor hu,cubicThetaEisensteinWeight_factor hu,
    cubicThetaEisensteinWeight_lambda_mod]

lemma cubicThetaEisensteinWeight_ramified_congr {u : Eisenstein}
    (hu : primary u) (k : ℕ) {a b : Eisenstein} (hab : (9*u) ∣ a-b) :
    cubicThetaEisensteinWeight (lambdaE^k*u) a=
      cubicThetaEisensteinWeight (lambdaE^k*u) b := by
  obtain ⟨t,ht⟩ := hab
  have ha : a=b+9*u*t := by linear_combination ht
  rw [ha,cubicThetaEisensteinWeight_ramified_periodic hu]

def cubicThetaRamifiedBaseRow (u : Eisenstein) (hu : u≠0) (j : ℕ)
    (h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*lambdaE^2*u),
    cubicThetaEisensteinWeight (lambdaE^j*u)
      (residueRepresentative (3*lambdaE^2*u) x)*
    residueFourierChar (3*lambdaE^2*u)
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ lambdaE_prime.ne_zero)) hu)
      (Ideal.Quotient.mk (modulus (3*lambdaE^2*u)) h*x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryResidueNine
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nine primary residue classes modulo nine, parametrized without
choices of integer coordinates by the residue ring modulo three. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryNineLift (y : Residues (3:Eisenstein)) : CubicThetaPrimaryNine where
  val := Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y)
  property := by
    apply primary_of_nine_congr (a:=1+3*residueRepresentative 3 y)
      ⟨residueRepresentative 3 y,by ring⟩
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr (residueRepresentative_spec 9
      (Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y))).symm

lemma cubicThetaPrimaryNineLift_injective : Function.Injective cubicThetaPrimaryNineLift := by
  intro x y h
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 x)=
    Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y) at he
  have hd : (9:Eisenstein) ∣ 3*(residueRepresentative 3 x-residueRepresentative 3 y) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul,map_sub]
    change Ideal.Quotient.mk (modulus (9:Eisenstein)) 3 *
      (Ideal.Quotient.mk (modulus 9) (residueRepresentative 3 x)-
        Ideal.Quotient.mk (modulus 9) (residueRepresentative 3 y))=0
    have hz := congrArg (fun z : Residues (9:Eisenstein) =>
      z-Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y)) he
    simp only [map_add,map_mul,map_one] at hz
    linear_combination hz
  have h3 : (3:Eisenstein) ∣ residueRepresentative 3 x-residueRepresentative 3 y := by
    have h9 : (9:Eisenstein)=3*3 := by norm_num
    rw [h9,mul_dvd_mul_iff_left (by norm_num : (3:Eisenstein)≠0)] at hd
    exact hd
  have hr := residue_eq_of_dvd_sub h3
  simpa only [residueRepresentative_spec] using hr

lemma cubicThetaPrimaryNineLift_surjective : Function.Surjective cubicThetaPrimaryNineLift := by
  intro x
  obtain ⟨t,ht⟩ := x.property
  refine ⟨Ideal.Quotient.mk (modulus 3) t,?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (modulus 9)
    (1+3*residueRepresentative 3 (Ideal.Quotient.mk (modulus 3) t))=x.val
  rw [← residueRepresentative_spec 9 x.val]
  apply residue_eq_of_dvd_sub
  have hd : (3:Eisenstein) ∣
      residueRepresentative 3 (Ideal.Quotient.mk (modulus 3) t)-t := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr (residueRepresentative_spec 3 (Ideal.Quotient.mk (modulus 3) t))
  obtain ⟨v,hv⟩ := hd
  exact ⟨v,by linear_combination 3*hv-ht⟩

def cubicThetaPrimaryNineEquiv : Residues (3:Eisenstein) ≃ CubicThetaPrimaryNine :=
  Equiv.ofBijective cubicThetaPrimaryNineLift
    ⟨cubicThetaPrimaryNineLift_injective,cubicThetaPrimaryNineLift_surjective⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryNineSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite summation on the primary coset modulo nine. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaPrimaryNine_sum (f : Residues (9:Eisenstein) → ℂ) :
    (∑' x : Residues (9:Eisenstein),
      if primary (residueRepresentative 9 x) then f x else 0)=
    ∑' y : Residues (3:Eisenstein), f (cubicThetaPrimaryNineLift y).val := by
  classical
  let : Finite (Residues (9:Eisenstein)) := finite_residues (by norm_num)
  let : Finite (Residues (3:Eisenstein)) := finite_residues (by norm_num)
  let : Fintype (Residues (9:Eisenstein)) := Fintype.ofFinite _
  let : Fintype (Residues (3:Eisenstein)) := Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_subtype (p:=fun x : Residues (9:Eisenstein) =>
      primary (residueRepresentative 9 x)) _ (by simp) f]
  exact (Equiv.sum_comp cubicThetaPrimaryNineEquiv (fun x => f x.val)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryNineFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality on the primary coset in the exact codifferent pairing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryNineLift_fourier (h : Eisenstein) (y : Residues (3:Eisenstein)) :
    residueFourierChar 9 (by norm_num)
      (Ideal.Quotient.mk (modulus 9) h*(cubicThetaPrimaryNineLift y).val)=
    residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)*
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h*y) := by
  change residueFourierChar 9 _
    (Ideal.Quotient.mk (modulus 9) h*
      Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y))=_
  rw [← map_mul,show h*(1+3*residueRepresentative 3 y)=
    h+3*h*residueRepresentative 3 y by ring,map_add,AddChar.map_add_eq_mul,
    cubicThetaFourier_nine_triple,map_mul,residueRepresentative_spec]

theorem cubicThetaPrimaryNine_fourier (h : Eisenstein) :
    (∑' x : Residues (9:Eisenstein),
      if primary (residueRepresentative 9 x) then
        residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h*x) else 0)=
    if (3:Eisenstein) ∣ h then
      9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h) else 0 := by
  classical
  rw [cubicThetaPrimaryNine_sum]
  simp_rw [cubicThetaPrimaryNineLift_fourier]
  rw [tsum_mul_left]
  let : Finite (Residues (3:Eisenstein)) := finite_residues (by norm_num)
  let : Fintype (Residues (3:Eisenstein)) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hs := AddChar.sum_mulShift (Ideal.Quotient.mk (modulus (3:Eisenstein)) h)
    (residueFourierChar_isPrimitive 3 (by norm_num))
  have hs' : (∑ x : Residues (3:Eisenstein),
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h*x))=
      if Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0 then
        (Fintype.card (Residues (3:Eisenstein)):ℂ) else 0 := by
    by_cases hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0
    · simpa only [hz,ite_true, if_true,mul_comm] using hs
    · simpa only [hz,ite_false, if_false,Nat.cast_zero,mul_comm] using hs
  rw [hs']
  have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0 ↔ (3:Eisenstein) ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hc : (Fintype.card (Residues (3:Eisenstein)):ℂ)=9 := by
    rw [← Nat.card_eq_fintype_card,residues_card (by norm_num)]
    have hn : normNat (3:Eisenstein)=9 := by
      apply Nat.cast_injective (R:=ℝ)
      rw [normNat_cast]
      change Complex.normSq (3:ℂ)=(9:ℝ)
      norm_num
    rw [hn]
    norm_num
  rw [hz,hc]
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedNineGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact evaluation of the finite ramified Gauss sum. The three
ramified character exponents select three distinct additive congruence
classes; this calculation is independent of residue identification. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaRamifiedCharacter_power {a : Eisenstein} (ha : primary a) (j : ℕ) :
    (cubicSymbol a lambdaE)^j=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) (2*(j:Eisenstein)*(a-1))) := by
  obtain ⟨t,ht⟩ := ha
  have he : a=1+3*t := by linear_combination ht
  have hc : cubicSymbol a lambdaE=cubicThetaRamifiedCharacter t := by rw [he]; rfl
  rw [hc,cubicThetaRamifiedCharacter_fourier]
  have hp : (residueFourierChar 3 (by norm_num)
      (Ideal.Quotient.mk (modulus 3) (2*t)))^j=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (2*(j:Eisenstein)*t)) := by
    rw [show 2*(j:Eisenstein)*t=j • (2*t) by simp; ring,map_nsmul,
      AddChar.map_nsmul_eq_pow]
  rw [hp,show 2*(j:Eisenstein)*(a-1)=3*((2*(j:Eisenstein))*t) by rw [ht]; ring]
  simpa only [mul_assoc] using (cubicThetaFourier_nine_triple (2*(j:Eisenstein)) t).symm

def cubicThetaRamifiedNineGauss (j : ℕ) (h : Eisenstein) : ℂ :=
  ∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h*x)

theorem cubicThetaRamifiedNineGauss_eq (j : ℕ) (h : Eisenstein) :
    cubicThetaRamifiedNineGauss j h=
      if (3:Eisenstein) ∣ h+2*(j:Eisenstein) then
        9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)
      else 0 := by
  classical
  let ψ := residueFourierChar (9:Eisenstein) (by norm_num)
  have hx (x : Residues (9:Eisenstein)) :
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
        ψ (Ideal.Quotient.mk (modulus 9) h*x)=
      ψ (Ideal.Quotient.mk (modulus 9) (-2*(j:Eisenstein)))*
        (if primary (residueRepresentative 9 x) then
          ψ (Ideal.Quotient.mk (modulus 9) (h+2*(j:Eisenstein))*x) else 0) := by
    rw [cubicThetaEisensteinWeight_lambda_pow]
    by_cases hp : primary (residueRepresentative 9 x)
    · rw [ite_eq_left hp,ite_eq_left hp,cubicThetaRamifiedCharacter_power hp,
        ← ψ.map_add_eq_mul,← ψ.map_add_eq_mul]
      congr 1
      have he : 2*(j:Eisenstein)*(residueRepresentative 9 x-1)+
          h*residueRepresentative 9 x=
          -2*(j:Eisenstein)+(h+2*(j:Eisenstein))*residueRepresentative 9 x := by ring
      have hz := congrArg (Ideal.Quotient.mk (modulus (9:Eisenstein))) he
      simpa only [map_add,map_mul,map_sub,map_one,map_neg,residueRepresentative_spec] using hz
    · rw [ite_eq_right hp,ite_eq_right hp,zero_mul,mul_zero]
  unfold cubicThetaRamifiedNineGauss
  change (∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      ψ (Ideal.Quotient.mk (modulus 9) h*x))=_
  simp_rw [hx]
  rw [tsum_mul_left,cubicThetaPrimaryNine_fourier]
  split_ifs
  · change ψ (Ideal.Quotient.mk (modulus 9) (-2*(j:Eisenstein)))*
      (9*ψ (Ideal.Quotient.mk (modulus 9) (h+2*(j:Eisenstein))))=
      9*ψ (Ideal.Quotient.mk (modulus 9) h)
    calc
      _ = 9*(ψ (Ideal.Quotient.mk (modulus 9) (-2*(j:Eisenstein)))*
        ψ (Ideal.Quotient.mk (modulus 9) (h+2*(j:Eisenstein)))) := by ring
      _ = _ := by
        rw [← ψ.map_add_eq_mul,← map_add]
        rw [show -2*(j:Eisenstein)+(h+2*(j:Eisenstein))=h by ring]
  · ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite ramified sum with its unit character retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaRamifiedUnitNineGauss (j r : ℕ) (h : Eisenstein) : ℂ :=
  ∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      (cubicSymbol (residueRepresentative 9 x) omegaE)^r*
        residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h*x)

theorem cubicThetaRamifiedUnitNineGauss_eq (j r : ℕ) (h : Eisenstein) :
    cubicThetaRamifiedUnitNineGauss j r h=
      if (3:Eisenstein) ∣ h+2*(j:Eisenstein)+lambdaE*(r:Eisenstein) then
        9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)
      else 0 := by
  classical
  let ψ := residueFourierChar (9:Eisenstein) (by norm_num)
  let b : Eisenstein := 2*(j:Eisenstein)+lambdaE*(r:Eisenstein)
  have hx (x : Residues (9:Eisenstein)) :
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
        (cubicSymbol (residueRepresentative 9 x) omegaE)^r*
          ψ (Ideal.Quotient.mk (modulus 9) h*x)=
      ψ (Ideal.Quotient.mk (modulus 9) (-b))*
        (if primary (residueRepresentative 9 x) then
          ψ (Ideal.Quotient.mk (modulus 9) (h+b)*x) else 0) := by
    rw [cubicThetaEisensteinWeight_lambda_pow]
    by_cases hp : primary (residueRepresentative 9 x)
    · rw [ite_eq_left hp,ite_eq_left hp,cubicThetaRamifiedCharacter_power hp,
        cubicThetaUnitCharacter_power hp,← ψ.map_add_eq_mul,
        ← ψ.map_add_eq_mul,← ψ.map_add_eq_mul]
      congr 1
      have he : 2*(j:Eisenstein)*(residueRepresentative 9 x-1)+
          lambdaE*(r:Eisenstein)*(residueRepresentative 9 x-1)+h*residueRepresentative 9 x=
          -b+(h+b)*residueRepresentative 9 x := by dsimp only [b]; ring
      have hz := congrArg (Ideal.Quotient.mk (modulus (9:Eisenstein))) he
      simpa only [map_add,map_mul,map_sub,map_one,map_neg,residueRepresentative_spec] using hz
    · rw [ite_eq_right hp,ite_eq_right hp,zero_mul,zero_mul,mul_zero]
  unfold cubicThetaRamifiedUnitNineGauss
  change (∑' x : Residues (9:Eisenstein),
    cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 x)*
      (cubicSymbol (residueRepresentative 9 x) omegaE)^r*
        ψ (Ideal.Quotient.mk (modulus 9) h*x))=_
  simp_rw [hx]
  rw [tsum_mul_left,cubicThetaPrimaryNine_fourier]
  change ψ (Ideal.Quotient.mk (modulus 9) (-b))*
    (if (3:Eisenstein) ∣ h+b then 9*ψ (Ideal.Quotient.mk (modulus 9) (h+b)) else 0)=_
  have hb : h+b=h+2*(j:Eisenstein)+lambdaE*(r:Eisenstein) := by dsimp only [b]; ring
  rw [← hb]
  split_ifs
  · calc
      _ = 9*(ψ (Ideal.Quotient.mk (modulus 9) (-b))*
        ψ (Ideal.Quotient.mk (modulus 9) (h+b))) := by ring
      _ = _ := by
        rw [← ψ.map_add_eq_mul,← map_add]
        rw [show -b+(h+b)=h by ring]
  · ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedRowValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed modulus-nine sum in the normalization of the actual
Eisenstein rows. The sign comes from lambda squared being minus three. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaRamifiedBaseRow_one (j : ℕ) (h : Eisenstein) :
    cubicThetaRamifiedBaseRow 1 one_ne_zero j h=cubicThetaRamifiedNineGauss j (-h) := by
  let d : Eisenstein := 3*lambdaE^2*1
  have hd : d=(-9:Eisenstein) := by dsimp only [d]; rw [lambdaE_sq]; ring
  have hd0 : d≠0 := by rw [hd]; norm_num
  have hmod : modulus d=modulus (9:Eisenstein) := by
    rw [hd]
    exact Ideal.span_singleton_neg (x:=(9:Eisenstein))
  let e : Residues d ≃+* Residues (9:Eisenstein) := Ideal.quotEquivOfEq hmod
  have hr (x : Residues d) : Ideal.Quotient.mk (modulus (9:Eisenstein))
      (residueRepresentative d x)=e x := by
    rw [← Ideal.quotEquivOfEq_mk hmod,residueRepresentative_spec]
  have hw (x : Residues d) :
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative d x)=
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 (e x)) := by
    have he : (9:Eisenstein) ∣ residueRepresentative d x-residueRepresentative 9 (e x) := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr ((hr x).trans (residueRepresentative_spec 9 (e x)).symm)
    have he' : (9:Eisenstein)*1 ∣ residueRepresentative d x-residueRepresentative 9 (e x) := by
      simpa only [mul_one] using he
    simpa only [mul_one] using cubicThetaEisensteinWeight_ramified_congr primary_one j he' 
  have ht (a : Eisenstein) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) (h*a))=
      residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) ((-h)*a)) := by
    rw [residueFourierChar_mk,residueFourierChar_mk]
    congr 2
    unfold tracePair
    congr 2
    have hc : (d:ℂ)=(-9:ℂ) := by
      calc
        (d:ℂ)=((-9:Eisenstein):ℂ) := congrArg (fun z : Eisenstein => (z:ℂ)) hd
        _ = (-9:ℂ) := rfl
    rw [hc]
    push_cast
    change (h:ℂ)*(a:ℂ)*(1/((-9)*traceLambda))=
      (-(h:ℂ)*(a:ℂ))*(1/(9*traceLambda))
    field_simp [traceLambda_ne_zero]
  have hp (x : Residues d) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) h*x)=
      residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) (-h)*e x) := by
    calc
      _ = residueFourierChar d hd0
          (Ideal.Quotient.mk (modulus d) (h*residueRepresentative d x)) := by
        congr 1
        rw [map_mul,residueRepresentative_spec]
      _ = residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) ((-h)*residueRepresentative d x)) := ht _
      _ = _ := by rw [map_mul,hr]
  unfold cubicThetaRamifiedBaseRow cubicThetaRamifiedNineGauss
  change (∑' x : Residues d, cubicThetaEisensteinWeight (lambdaE^j*1)
    (residueRepresentative d x)*residueFourierChar d hd0
      (Ideal.Quotient.mk (modulus d) h*x))=_
  rw [← e.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  rw [mul_one,hw,hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique ramified coordinates for exactly the admissible Eisenstein
denominators. The exponent starts at two because the rows are divisible by
three. Global units are retained. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedDenominator
    (v : Eisensteinˣ × ℕ × CubicThetaPrimaryPart) : CubicThetaDenominator :=
  ⟨(v.1:Eisenstein)*lambdaE^(v.2.1+2)*v.2.2.val,by
    refine ⟨-(v.1:Eisenstein)*lambdaE^v.2.1*v.2.2.val,?_⟩
    rw [pow_add,lambdaE_sq]
    ring,
    mul_ne_zero (mul_ne_zero v.1.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))
      (primary_ne_zero v.2.2.property)⟩

theorem cubicThetaRamifiedDenominator_bijective :
    Function.Bijective cubicThetaRamifiedDenominator := by
  constructor
  · intro v w he
    have h := congrArg Subtype.val he
    change (v.1:Eisenstein)*lambdaE^(v.2.1+2)*v.2.2.val=
      (w.1:Eisenstein)*lambdaE^(w.2.1+2)*w.2.2.val at h
    obtain ⟨hu,hk,ha⟩ := unit_ramified_primary_unique v.2.2.property w.2.2.property h
    exact Prod.ext hu (Prod.ext (by omega) (Subtype.ext ha))
  · intro c
    obtain ⟨u,k,a,ha,hc⟩ := unit_ramified_primary_decomposition c.property.2
    have hpow : lambdaE^2 ∣ c.val := by
      rw [lambdaE_sq]
      exact neg_dvd.mpr c.property.1
    have hm : emultiplicity lambdaE c.val=(k:ℕ∞) := by
      rw [hc,emultiplicity_mul lambdaE_prime,emultiplicity_mul lambdaE_prime,
        unit_lambda_emultiplicity,primary_lambda_emultiplicity ha,
        emultiplicity_pow_self_of_prime lambdaE_prime,zero_add,add_zero]
    have hk : 2 ≤ k := by
      have hle := le_emultiplicity_of_pow_dvd hpow
      rw [hm] at hle
      exact_mod_cast hle
    refine ⟨(u,k-2,⟨a,ha⟩),?_⟩
    apply Subtype.ext
    change (u:Eisenstein)*lambdaE^(k-2+2)*a=c.val
    rw [Nat.sub_add_cancel hk]
    exact hc.symm

def cubicThetaRamifiedDenominatorEquiv :
    (Eisensteinˣ × ℕ × CubicThetaPrimaryPart) ≃ CubicThetaDenominator :=
  Equiv.ofBijective _ cubicThetaRamifiedDenominator_bijective

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ramified conductor cutoff for every global-unit class in the
literal denominator decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_unit_lambda (u : Eisensteinˣ) (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight ((u:Eisenstein)*lambdaE^k) a=
      if primary a then cubicSymbol a (u:Eisenstein)*(cubicSymbol a lambdaE)^k else 0 := by
  by_cases ha : primary a
  · have hunit : IsCoprime (u:Eisenstein) a := ⟨(u⁻¹:Eisensteinˣ),0,by simp⟩
    have hc := hunit.mul_left ((primary_coprime_lambda ha).symm.pow_left (m:=k))
    rw [cubicThetaEisensteinWeight,ite_eq_left ⟨ha,hc⟩,ite_eq_left ha,
      cubicSymbol_mul_upper ha,cubicSymbol_pow_upper ha]
  · rw [cubicThetaEisensteinWeight,ite_eq_right (fun h => ha h.1),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_unit_lambda_periodic (u : Eisensteinˣ)
    (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight ((u:Eisenstein)*lambdaE^k) (a+9*b)=
      cubicThetaEisensteinWeight ((u:Eisenstein)*lambdaE^k) a := by
  have hp : primary (a+9*b) ↔ primary a := by
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t-3*b,by linear_combination ht⟩
    · rintro ⟨t,ht⟩
      exact ⟨t+3*b,by linear_combination ht⟩
  rw [cubicThetaEisensteinWeight_unit_lambda,cubicThetaEisensteinWeight_unit_lambda]
  by_cases ha : primary a
  · have hn : (9:Eisenstein) ∣ a+9*b-a := ⟨b,by ring⟩
    rw [ite_eq_left (hp.mpr ha),ite_eq_left ha,
      cubicSymbol_unit_periodic (hp.mpr ha) ha u.isUnit hn,
      cubicSymbol_lambda_periodic (hp.mpr ha) ha hn]
  · rw [ite_eq_right (fun h => ha (hp.mp h)),ite_eq_right ha]

lemma cubicThetaEisensteinWeight_full_ramified_periodic (e : Eisensteinˣ)
    {u : Eisenstein} (hu : primary u) (k : ℕ) (a b : Eisenstein) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k*u) (a+9*u*b)=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k*u) a := by
  rw [mul_comm ((e:Eisenstein)*lambdaE^k) u,cubicThetaEisensteinWeight_factor hu,
    cubicThetaEisensteinWeight_factor hu]
  have hc : cubicSymbol u (a+9*u*b)=cubicSymbol u a := by
    apply cubicSymbol_congr
    exact residue_eq_of_dvd_sub ⟨9*b,by ring⟩
  rw [hc,show a+9*u*b=a+9*(u*b) by ring,
    cubicThetaEisensteinWeight_unit_lambda_periodic]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimaryFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the primary part of every actual ramified row. Reciprocity
reduces its correction to one explicit finite character squared. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPrimaryPhase (e : Eisensteinˣ) {u : Eisenstein}
    (hu : primary u) (n : ℕ) :
    cubicSymbol u (3*((e:Eisenstein)*lambdaE^(n+2)))*
        cubicSymbol u ((e:Eisenstein)*lambdaE^(n+2))=
      (cubicSymbol u (e:Eisenstein)*(cubicSymbol u lambdaE)^n)^2 := by
  rw [cubicSymbol_mul_upper hu,cubicSymbol_mul_upper hu,cubicSymbol_pow_upper hu,
    pow_add]
  have hthree := cubicSymbol_three_lambda hu
  rw [cubicSymbol_mul_upper hu] at hthree
  have hcube := cubicSymbol_cube_of_isCoprime hu lambdaE (primary_coprime_lambda hu)
  calc
    _ = (cubicSymbol u (e:Eisenstein)*(cubicSymbol u lambdaE)^n)^2*
      (cubicSymbol u 3*cubicSymbol u lambdaE)*(cubicSymbol u lambdaE)^3 := by ring
    _ = _ := by rw [hthree,hcube,mul_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimarySeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite ramified factors separated from the remaining primary
Fourier series. These are identities for the actual convergent Dirichlet
sum, with no residue formula assumed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryFourierTerm (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) : ℂ :=
  (cubicSymbol a.val (e:Eisenstein)*(cubicSymbol a.val lambdaE)^n)^2*
    cubicThetaSymbolFourier a.val (primary_ne_zero a.property) h*(norm a.val:ℂ)^(-s)

def cubicThetaPrimaryFourierSeries (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) : ℂ := ∑' a : CubicThetaPrimaryPart, cubicThetaPrimaryFourierTerm e n s h a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryFourierTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication of the frequency by any unit of the actual residue
ring. In particular, primary Fourier rows are invariant under lambda cubed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimaryFourierSeries_lambda_cube (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s (lambdaE^3*h)=
      cubicThetaPrimaryFourierSeries e n s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  unfold cubicThetaPrimaryFourierTerm
  rw [cubicThetaSymbolFourier_lambda_cube a.property]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube support and exact residue-unit count for the primary finite
character sum occurring at the inverted cusp. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaSymbol_primary_cube {c : Eisenstein} (hc : primary c)
    (hcb : ∃ j : Eisenstein, j^3=c) (x : Eisenstein) :
    cubicSymbol c x=if IsCoprime c x then 1 else 0 := by
  by_cases hx : IsCoprime c x
  · rw [ite_eq_left hx]
    obtain ⟨u,hux,hu⟩ := residue_crt_one (primary_coprime_three hc) x
    have hcu : IsCoprime c u := isCoprime_of_residue_congr hux hx
    rw [← cubicSymbol_congr (residue_eq_of_dvd_sub hux),cubic_reciprocity hc hu]
    obtain ⟨j,hj⟩ := hcb
    rw [← hj,cubicSymbol_pow_upper hu]
    apply cubicSymbol_cube_of_isCoprime hu j
    rw [← hj] at hcu
    exact hcu.symm.of_isCoprime_of_dvd_right (dvd_pow_self j (by norm_num : (3:ℕ)≠0))
  · rw [ite_eq_right hx,cubicSymbol_eq_zero_of_not_isCoprime hc hx]

theorem cubicThetaSymbolFourier_zero_cube {c : Eisenstein} (hc : primary c)
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) 0=(Nat.card (Residues c)ˣ:ℂ) := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  let e : (Residues c)ˣ ≃ {x : Residues c // IsUnit x} := {
    toFun := fun u => ⟨u,u.isUnit⟩
    invFun := fun x => x.property.unit
    left_inv := fun u => Units.ext (IsUnit.unit_spec _)
    right_inv := fun x => Subtype.ext x.property.unit_spec }
  have hu (x : Residues c) : IsCoprime c (residueRepresentative c x) ↔ IsUnit x := by
    constructor
    · intro hx
      have ht := residue_isUnit_of_isCoprime hx
      rwa [residueRepresentative_spec] at ht
    · intro hx
      apply isCoprime_of_residue_isUnit
      rwa [residueRepresentative_spec]
  unfold cubicThetaSymbolFourier
  simp_rw [cubicThetaSymbol_primary_cube hc hcb,hu]
  simp only [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one,tsum_fintype]
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimarySeriesRamification
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three primary twists are cycled by lambda in the frequency.
These are equalities of the actual primary series, before continuation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimaryFourierSeries_period (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e (n+3) s h=cubicThetaPrimaryFourierSeries e n s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  have hc := cubicSymbol_cube_of_isCoprime a.property lambdaE
    (primary_coprime_lambda a.property)
  unfold cubicThetaPrimaryFourierTerm
  rw [pow_add,hc,mul_one]

theorem cubicThetaPrimaryFourierSeries_lambda (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s (lambdaE*h)=
      cubicThetaPrimaryFourierSeries e (n+1) s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  unfold cubicThetaPrimaryFourierTerm
  rw [mul_comm lambdaE h,cubicThetaSymbolFourier_mul a.property
    (primary_coprime_lambda a.property),← cubicSymbol_sq_eq_star a.property,
    pow_succ]
  ring

theorem cubicThetaPrimaryFourierSeries_lambda_pow (e : Eisensteinˣ) (n k : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s (lambdaE^k*h)=
      cubicThetaPrimaryFourierSeries e (n+k) s h := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc,cubicThetaPrimaryFourierSeries_lambda,ih]
    congr 1
    omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitInflation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inflation of a ramified row with its global unit retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_unit_lambda_mod (e : Eisensteinˣ) (k : ℕ) (a : Eisenstein) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k) a=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^(k%3)) a := by
  rw [cubicThetaEisensteinWeight_unit_lambda,cubicThetaEisensteinWeight_unit_lambda]
  by_cases ha : primary a
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hc := cubicSymbol_cube_of_isCoprime ha lambdaE (primary_coprime_lambda ha)
    have he : (cubicSymbol a lambdaE)^k=(cubicSymbol a lambdaE)^(k%3) := by
      conv_lhs => rw [← Nat.mod_add_div k 3]
      rw [pow_add,pow_mul,hc,one_pow,mul_one]
    rw [he]
  · rw [ite_eq_right ha,ite_eq_right ha]

lemma cubicThetaEisensteinWeight_unit_lambda_congr (e : Eisensteinˣ) (k : ℕ)
    {a b : Eisenstein} (hab : (9:Eisenstein) ∣ a-b) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k) a=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^k) b := by
  obtain ⟨t,ht⟩ := hab
  rw [show a=b+9*t by linear_combination ht,
    cubicThetaEisensteinWeight_unit_lambda_periodic]

def cubicThetaUnitRamifiedBase (e : Eisensteinˣ) (j : ℕ) (h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*(e:Eisenstein)*lambdaE^2),
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j)
      (residueRepresentative (3*(e:Eisenstein)*lambdaE^2) x)*
      residueFourierChar (3*(e:Eisenstein)*lambdaE^2)
        (mul_ne_zero (mul_ne_zero (by norm_num) e.ne_zero)
          (pow_ne_zero _ lambdaE_prime.ne_zero))
        (Ideal.Quotient.mk (modulus (3*(e:Eisenstein)*lambdaE^2)) h*x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite ramified factor at every signed omega-unit. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_signed_unit (e : Eisensteinˣ) (r j : ℕ)
    (he : (e:Eisenstein)=omegaE^r ∨ (e:Eisenstein)=-(omegaE^r)) (a : Eisenstein) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j) a=
      cubicThetaEisensteinWeight (lambdaE^j) a*(cubicSymbol a omegaE)^r := by
  rw [cubicThetaEisensteinWeight_unit_lambda,cubicThetaEisensteinWeight_lambda_pow]
  by_cases ha : primary a
  · rw [ite_eq_left ha,ite_eq_left ha]
    rcases he with he | he
    · rw [he,cubicSymbol_pow_upper ha]
      ring
    · rw [he,cubicSymbol_neg ha,cubicSymbol_pow_upper ha]
      ring
  · rw [ite_eq_right ha,ite_eq_right ha,zero_mul]

theorem cubicThetaUnitRamifiedBase_value (e : Eisensteinˣ) (r j : ℕ)
    (he : (e:Eisenstein)=omegaE^r ∨ (e:Eisenstein)=-(omegaE^r)) (h : Eisenstein) :
    cubicThetaUnitRamifiedBase e j h=
      cubicThetaRamifiedUnitNineGauss j r (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h) := by
  let d : Eisenstein := 3*(e:Eisenstein)*lambdaE^2
  have hd : d= -9*(e:Eisenstein) := by dsimp only [d]; rw [lambdaE_sq]; ring
  have hd0 : d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) e.ne_zero)
    (pow_ne_zero _ lambdaE_prime.ne_zero)
  have hmod : modulus d=modulus (9:Eisenstein) := by
    apply le_antisymm
    · apply Ideal.span_singleton_le_span_singleton.mpr
      exact ⟨-(e:Eisenstein),by rw [hd]; ring⟩
    · apply Ideal.span_singleton_le_span_singleton.mpr
      refine ⟨-((e⁻¹:Eisensteinˣ):Eisenstein),?_⟩
      rw [hd]
      calc
        (9:Eisenstein) = 9*((e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)) := by
          rw [e.mul_inv,mul_one]
        _ = (-9*(e:Eisenstein))*(-((e⁻¹:Eisensteinˣ):Eisenstein)) := by ring
  let E : Residues d ≃+* Residues (9:Eisenstein) := Ideal.quotEquivOfEq hmod
  have hr (x : Residues d) : Ideal.Quotient.mk (modulus (9:Eisenstein))
      (residueRepresentative d x)=E x := by
    rw [← Ideal.quotEquivOfEq_mk hmod,residueRepresentative_spec]
  have hw (x : Residues d) :
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j) (residueRepresentative d x)=
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 (E x))*
        (cubicSymbol (residueRepresentative 9 (E x)) omegaE)^r := by
    have h9 : (9:Eisenstein) ∣ residueRepresentative d x-residueRepresentative 9 (E x) := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr ((hr x).trans (residueRepresentative_spec 9 (E x)).symm)
    rw [cubicThetaEisensteinWeight_unit_lambda_congr e j h9,
      cubicThetaEisensteinWeight_signed_unit e r j he]
  have ht (a : Eisenstein) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) (h*a))=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) ((-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)*a)) := by
    rw [residueFourierChar_mk,residueFourierChar_mk]
    congr 2
    unfold tracePair
    congr 2
    have hc : (d:ℂ)= -9*((e:Eisenstein):ℂ) := by
      calc
        (d:ℂ)=((-9*(e:Eisenstein):Eisenstein):ℂ) := congrArg (fun z : Eisenstein => (z:ℂ)) hd
        _ = _ := rfl
    have hi : (((e⁻¹:Eisensteinˣ):Eisenstein):ℂ)=(((e:Eisenstein):ℂ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have hx := congrArg (fun z : Eisenstein => (z:ℂ)) e.inv_mul
      simpa only [Subalgebra.coe_mul,Subalgebra.coe_one] using hx
    have hne : ((e:Eisenstein):ℂ)≠0 := fun hzero => e.ne_zero (Subtype.ext hzero)
    rw [hc]
    push_cast
    rw [hi]
    change (h:ℂ)*(a:ℂ)*(1/(-9*((e:Eisenstein):ℂ)*traceLambda))=
      (-(((e:Eisenstein):ℂ)⁻¹)*(h:ℂ)*(a:ℂ))*(1/(9*traceLambda))
    field_simp [hne,traceLambda_ne_zero]
  have hp (x : Residues d) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) h*x)=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)*E x) := by
    calc
      _ = residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) (h*residueRepresentative d x)) := by
        congr 1
        rw [map_mul,residueRepresentative_spec]
      _ = _ := by rw [ht,map_mul,hr]
  unfold cubicThetaUnitRamifiedBase cubicThetaRamifiedUnitNineGauss
  change (∑' x : Residues d, cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j)
    (residueRepresentative d x)*residueFourierChar d hd0
      (Ideal.Quotient.mk (modulus d) h*x))=_
  rw [← E.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  rw [hw,hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedAllRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit finite ramified factor for all six global units. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNorm_lambda_pow (n : ℕ) : norm (lambdaE^n)=(3:ℝ)^n := by
  simp only [norm,Subalgebra.coe_pow,map_pow,lambdaE_coe,traceLambda_normSq]

lemma cubicThetaNorm_unit_lambda_pow (e : Eisensteinˣ) (n : ℕ) :
    norm ((e:Eisenstein)*lambdaE^n)=(3:ℝ)^n := by
  rw [norm_mul_eq,norm_of_isUnit e.isUnit,one_mul,cubicThetaNorm_lambda_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitCube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic inflation with every unit retained, and its exact factor in the
convergent ramified/primary decomposition. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimaryFourierTerm_cube (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) :
    cubicThetaPrimaryFourierTerm e (n+3) s (lambdaE^3*h) a=
      cubicThetaPrimaryFourierTerm e n s h a := by
  have hc := cubicSymbol_cube_of_isCoprime a.property lambdaE
    (primary_coprime_lambda a.property)
  unfold cubicThetaPrimaryFourierTerm
  rw [pow_add,hc,mul_one,cubicThetaSymbolFourier_lambda_cube a.property]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedLowFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact low-row correction is one primary series times a finite
modulus-three Fourier trace. No value of its residue is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimaryFourierSeries_neg_one (n : ℕ) (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries (-1) n s h=cubicThetaPrimaryFourierSeries 1 n s h := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  unfold cubicThetaPrimaryFourierTerm
  simp only [Units.val_neg,Units.val_one,cubicSymbol_neg a.property]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTrace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier trace in the ramified correction never vanishes.
It equals two on primary frequencies and on lambda cubes. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPhase_one :
    residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (1:Eisenstein))=1 := by
  have he := cubicThetaRamifiedCharacter_fourier (-1:Eisenstein)
  have hc : cubicThetaRamifiedCharacter (-1:Eisenstein)=1 := by
    rw [show (-1:Eisenstein)=-(1:Eisenstein) by ring,AddChar.map_neg_eq_inv,
      cubicThetaRamifiedCharacter_one,inv_one]
  have hr : Ideal.Quotient.mk (modulus (3:Eisenstein)) (2*(-1:Eisenstein))=
      Ideal.Quotient.mk (modulus 3) (1:Eisenstein) :=
    residue_eq_of_dvd_sub ⟨-1,by ring⟩
  rw [hc,hr] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFiniteFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Fourier coefficient of an inverted row is the
middle primary twist already continued from the global Eisenstein series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaInvertedFrequencyDirichlet (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' c : CubicThetaPrimaryPart, cubicThetaInvertedGaussCoefficient c.val h*(norm c.val:ℂ)^(-s)

lemma cubicThetaInvertedFrequencyDirichlet_eq (h : Eisenstein) (s : ℂ) :
    cubicThetaInvertedFrequencyDirichlet h s=cubicThetaPrimaryFourierSeries 1 1 s h := by
  unfold cubicThetaInvertedFrequencyDirichlet cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro c
  rw [cubicThetaInvertedGaussCoefficient_factor c.property,cubicThetaSymbol_three c.property]
  have h1 : cubicSymbol c.val 1=1 := by
    rw [cubic_reciprocity c.property primary_one,cubicSymbol_one_lower]
  simp [cubicThetaPrimaryFourierTerm,h1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and the literal primary-row unfolding at the
inverted cusp. The second coordinate is exactly three times a lattice point. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaInvertedGridTerm_admissible
    (cd : {cd // cubicThetaInvertedAdmissible cd}) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaInvertedGridTerm cd.val p s=
      cubicThetaInvertedTerm (cubicThetaInvertedPairEquiv.symm cd) p s := by
  simp only [cubicThetaInvertedGridTerm,cd.property,ite_true, if_true,cubicThetaInvertedTerm,
    cubicThetaInvertedPairEquiv,CubicThetaInvertedRow.height]
  rfl

lemma cubicThetaInvertedTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun r : CubicThetaInvertedRow => cubicThetaInvertedTerm r p s) := by
  have ht := cubicThetaEisenstein_summable
    (cubicThetaMobius_height_pos (cubicThetaFullComplex cubicThetaFullInversion) hp) hs
  have he : (fun r : CubicThetaBottomRow => cubicThetaEisensteinTerm r
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s)=
      (fun r => cubicThetaInvertedTerm (cubicThetaInvertedRowEquiv r) p s) := by
    funext r
    exact cubicThetaEisensteinTerm_inverted r hp s
  rw [he] at ht
  exact cubicThetaInvertedRowEquiv.summable_iff.mp ht

lemma cubicThetaInvertedGrid_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun cd : Eisenstein × Eisenstein => cubicThetaInvertedGridTerm cd p s) := by
  have hsub := (cubicThetaInvertedTerm_summable hp hs).comp_injective
    cubicThetaInvertedPairEquiv.symm.injective
  have hg : Summable (fun cd : {cd // cubicThetaInvertedAdmissible cd} =>
      cubicThetaInvertedGridTerm cd.val p s) := by
    apply hsub.congr
    intro cd
    exact (cubicThetaInvertedGridTerm_admissible cd p s).symm
  apply (Subtype.val_injective.summable_iff
    (f:=fun cd => cubicThetaInvertedGridTerm cd p s) ?_).mp hg
  intro cd hcd
  by_cases hc : cubicThetaInvertedAdmissible cd
  · exact False.elim (hcd ⟨⟨cd,hc⟩,rfl⟩)
  · simp [cubicThetaInvertedGridTerm,hc]

theorem cubicThetaEisenstein_inverted_grid {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' cd : Eisenstein × Eisenstein, cubicThetaInvertedGridTerm cd p s := by
  rw [cubicThetaEisenstein_inverted hp]
  have hsup : Function.support (fun cd => cubicThetaInvertedGridTerm cd p s) ⊆
      {cd | cubicThetaInvertedAdmissible cd} := by
    intro cd hcd
    by_contra hc
    change ¬cubicThetaInvertedAdmissible cd at hc
    exact hcd (by simp [cubicThetaInvertedGridTerm,hc])
  calc
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd},
        cubicThetaInvertedTerm (cubicThetaInvertedPairEquiv.symm cd) p s :=
      (cubicThetaInvertedPairEquiv.symm.tsum_eq _).symm
    _ = ∑' cd : {cd // cubicThetaInvertedAdmissible cd}, cubicThetaInvertedGridTerm cd.val p s :=
      tsum_congr (fun cd => (cubicThetaInvertedGridTerm_admissible cd p s).symm)
    _ = _ := tsum_subtype_eq_of_support_subset hsup

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal inverted Eisenstein rows and their convergent Gaussian
Mellin representation. This connects finite arithmetic to the actual series. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_inverted_rows {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' c : Eisenstein, if primary c then cubicThetaInvertedRowSeries c p s else 0 := by
  rw [cubicThetaEisenstein_inverted_grid hp,(cubicThetaInvertedGrid_summable hp hs).tsum_prod]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · rw [ite_eq_left hc,cubicThetaInvertedGrid_row hc]
  · simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inverted row Fourier expansion, with absolute integrated
summability proved before interchanging its heat integral and lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaInvertedGaussCoefficient_norm {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) :
    ‖cubicThetaInvertedGaussCoefficient c h‖ ≤ (Nat.card (Residues c):ℝ) := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  unfold cubicThetaInvertedGaussCoefficient
  rw [tsum_fintype,Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ x : Residues c, ‖cubicSymbol c (3*residueRepresentative c x)*
        (Real.fourierChar (tracePair (residueRepresentative c x:ℂ)
          ((h:ℂ)/((c:ℂ)*traceLambda))):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residues c, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul,Circle.norm_coe,mul_one]
      exact norm_cubicSymbol_le_one hc _
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute arithmetic and heat majorants for collecting the actual
inverted Fourier coefficients on their half-plane of convergence. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaInvertedFrequencyDirichlet_tsum (h : Eisenstein) (s : ℂ) :
    cubicThetaInvertedFrequencyDirichlet h s=
      ∑' c : Eisenstein, cubicThetaInvertedFrequencyTerm s h c := by
  have hsup : Function.support (cubicThetaInvertedFrequencyTerm s h) ⊆ {c | primary c} := by
    intro c hc
    by_contra hn
    change ¬primary c at hn
    exact hc (by simp [cubicThetaInvertedFrequencyTerm,hn])
  calc
    _ = ∑' c : CubicThetaPrimaryPart, cubicThetaInvertedFrequencyTerm s h c.val := by
      apply tsum_congr
      intro c
      simp only [cubicThetaInvertedFrequencyTerm,ite_eq_left c.property]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaInvertedFrequencyDirichlet_zero (s : ℂ) :
    cubicThetaInvertedFrequencyDirichlet 0 s=cubicThetaInvertedConstantDirichlet s := by
  rw [cubicThetaInvertedFrequencyDirichlet_tsum]
  unfold cubicThetaInvertedConstantDirichlet
  apply tsum_congr
  intro c
  simp only [cubicThetaInvertedFrequencyTerm,cubicThetaInvertedConstantWeight,
    cubicThetaInvertedGaussCoefficient_zero]

lemma cubicThetaInvertedGaussCoefficient_norm_real {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) : ‖cubicThetaInvertedGaussCoefficient c h‖≤norm c := by
  have ht := cubicThetaInvertedGaussCoefficient_norm hc h
  rwa [residues_card (primary_ne_zero hc),normNat_cast] at ht

lemma cubicThetaInvertedFrequencyTerm_bound (s : ℂ) (h c : Eisenstein) :
    ‖cubicThetaInvertedFrequencyTerm s h c‖≤9*(norm c)^(-(s.re-1)) := by
  by_cases hc : primary c
  · have hc0 := primary_ne_zero hc
    rw [cubicThetaInvertedFrequencyTerm,ite_eq_left hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hc0)]
    simp only [Complex.neg_re]
    have hg : ‖cubicThetaInvertedGaussCoefficient c h‖≤9*norm c := by
      have ht := cubicThetaInvertedGaussCoefficient_norm_real hc h
      linarith [norm_nonneg c]
    calc
      _ ≤ (9*norm c)*(norm c)^(-s.re) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg (norm_nonneg c) _)
      _ = _ := by
        have he : norm c*(norm c)^(-s.re)=(norm c)^(-(s.re-1)) := by
          calc
            _ = (norm c)^(1:ℝ)*(norm c)^(-s.re) := by rw [Real.rpow_one]
            _ = _ := by
              rw [←Real.rpow_add (norm_pos_of_ne_zero hc0)]
              congr 1
              ring
        rw [mul_assoc,he]
  · simp only [cubicThetaInvertedFrequencyTerm,ite_eq_right hc,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collect the inverted Fourier coefficients by an absolutely
convergent interchange of the two actual lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInvertedNonzeroTerm (p : ℂ × ℝ) (s : ℂ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaInvertedFrequencyDirichlet h s*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous inverted-cusp Fourier series and its physical mean.
The constant term is obtained by an actual torus projection. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaInvertedNonzeroTerm_phase (v : ℝ) (s : ℂ) (h : Eisenstein) (z : ℂ) :
    cubicThetaInvertedNonzeroTerm (0,v) s h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)=
      cubicThetaInvertedNonzeroTerm (z,v) s h := by
  by_cases hh : h=0
  · simp [cubicThetaInvertedNonzeroTerm,hh]
  · simp [cubicThetaInvertedNonzeroTerm,hh,tracePair]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryUnitTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb the six primary-series unit twists into the actual frequency.
This keeps the ramified residue equations on one finite unit orbit. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimaryFourierSeries_unit (e : Eisensteinˣ) (n : ℕ)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaPrimaryFourierSeries e n s h=
      cubicThetaPrimaryFourierSeries 1 n s (h*(e:Eisenstein)) := by
  unfold cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro a
  have hcop : IsCoprime a.val (e:Eisenstein) :=
    ⟨0,(e⁻¹:Eisensteinˣ),by simp⟩
  have h1 : cubicSymbol a.val 1=1 := by
    simpa only [pow_zero] using cubicSymbol_pow_upper a.property 1 0
  unfold cubicThetaPrimaryFourierTerm
  rw [cubicThetaSymbolFourier_mul a.property hcop,mul_pow,cubicSymbol_sq_eq_star a.property,
    Units.val_one,h1,one_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedContraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal middle-row operator on the six-unit orbit has row norm
at most two thirds. The ramified residue system therefore has a unique
solution for each fixed base-frequency forcing. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaUnitOrbit_lambda_class {h : Eisenstein} (hh : lambdaE∣h-1)
    (e : Eisensteinˣ) : lambdaE∣h*(e:Eisenstein)-1 ∨ lambdaE∣h*(e:Eisenstein)+1 := by
  obtain ⟨r,hr | hr⟩ := cubicThetaUnit_signed_power e
  · left
    have he : lambdaE∣(e:Eisenstein)-1 := by
      rw [hr]
      exact cubicThetaLambda_dvd_omega_pow_sub_one r
    convert dvd_add (dvd_mul_of_dvd_left hh (e:Eisenstein)) he using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · right
    have he : lambdaE∣(e:Eisenstein)+1 := by
      rw [hr]
      convert dvd_neg.mpr (cubicThetaLambda_dvd_omega_pow_sub_one r) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    convert dvd_add (dvd_mul_of_dvd_left hh (e:Eisenstein)) he using 1
    all_goals try with_reducible_and_instances rfl
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNinePhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The modulus-nine phase needed for the remaining ramified residue.
Integer multiples of three times a primary frequency lie in its kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNinePhase_three_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaNinePhase (3*h)=1 := by
  have he := cubicThetaFourier_nine_triple h 1
  simp only [mul_one] at he
  unfold cubicThetaNinePhase
  rw [he,(primary_iff_residue_one h).mp hh]
  simpa only [map_one] using cubicThetaRamifiedPhase_one

lemma cubicThetaNinePhase_three_integer_primary {h : Eisenstein} (hh : primary h)
    (n : ℤ) : cubicThetaNinePhase ((n:Eisenstein)*3*h)=1 := by
  have he : (n:Eisenstein)*3*h=n • (3*h) := by simp [zsmul_eq_mul,mul_assoc]
  unfold cubicThetaNinePhase
  rw [he,map_zsmul,AddChar.map_zsmul_eq_zpow]
  change (cubicThetaNinePhase (3*h))^n=1
  rw [cubicThetaNinePhase_three_primary hh,one_zpow]

lemma cubicThetaNinePhase_eq_of_difference {h a b : Eisenstein} (hh : primary h)
    (n : ℤ) (he : a-b=(n:Eisenstein)*3*h) :
    cubicThetaNinePhase a=cubicThetaNinePhase b := by
  have hz : cubicThetaNinePhase (a-b)=1 := by
    rw [he,cubicThetaNinePhase_three_integer_primary hh]
  rw [show a=(a-b)+b by ring,cubicThetaNinePhase_add,hz,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPhaseTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The modulus-nine phase aligns the two surviving middle-row terms
on each of the three positive unit representatives. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNinePhase_middle_first {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    cubicThetaNinePhase (-omegaE^2*lambdaE*(h*omegaE^(j:ℕ)))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*omegaE)^2*h)=
        cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  rw [←cubicThetaNinePhase_add]
  apply cubicThetaNinePhase_eq_of_difference hh ((j:ℕ)-1:ℤ)
  fin_cases j
  · norm_num only [Fin.val_zero,Nat.cast_zero,zero_sub,pow_zero,one_mul]
    dsimp only [lambdaE]
    linear_combination (2-2*omegaE)*h*omegaE_quadratic
  · norm_num only [Fin.val_one,Nat.cast_one,sub_self,pow_one,zero_mul]
    dsimp only [lambdaE]
    linear_combination -(omegaE^2)*h*omegaE_quadratic
  · norm_num only [Fin.val_two,Nat.cast_ofNat,Int.reduceSub,one_mul]
    dsimp only [lambdaE]
    linear_combination (omegaE^4-3*omegaE^3+3*omegaE-3)*h*omegaE_quadratic

theorem cubicThetaNinePhase_middle_second {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    cubicThetaNinePhase (omegaE*lambdaE*(h*omegaE^(j:ℕ)))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*(-omegaE^2))^2*h)=
        cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  rw [←cubicThetaNinePhase_add]
  apply cubicThetaNinePhase_eq_of_difference hh (if j=0 then -1 else if j=1 then 1 else 0)
  fin_cases j
  · norm_num
    dsimp only [lambdaE]
    linear_combination (omegaE^2-omegaE+2)*h*omegaE_quadratic
  · norm_num
    dsimp only [lambdaE]
    linear_combination (omegaE^4-omegaE^3+3*omegaE-3)*h*omegaE_quadratic
  · norm_num
    dsimp only [lambdaE]
    linear_combination (omegaE^6-omegaE^5+omegaE^3)*h*omegaE_quadratic

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPhaseRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact phase of each of the two nonzero middle ramified rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaOmegaUnit_inverse_value :
    (((cubicThetaOmegaUnit)⁻¹:Eisensteinˣ):Eisenstein)=omegaE^2 := rfl

lemma cubicThetaOmegaUnit_square_inverse_value :
    (((cubicThetaOmegaUnit^2)⁻¹:Eisensteinˣ):Eisenstein)=omegaE := by
  rw [←inv_pow,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit_inverse_value,←pow_mul,
    show 2*2=3+1 by omega,pow_add,omegaE_cube,pow_one,one_mul]

lemma cubicThetaOmegaUnit_distinct : cubicThetaOmegaUnit≠-(cubicThetaOmegaUnit^2) := by
  intro he
  have hv : omegaE=-(omegaE^2) := by
    simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using
      congrArg (fun e : Eisensteinˣ => (e:Eisenstein)) he
  have hz : (1:Eisenstein)=0 := by linear_combination omegaE_quadratic-hv
  exact one_ne_zero hz

lemma cubicThetaLambda_dvd_primary_sub_one {h : Eisenstein} (hh : primary h) :
    lambdaE∣h-1 := cubicThetaLambda_dvd_three.trans hh

lemma cubicThetaLambda_dvd_primary_omega_sub_one {h : Eisenstein} (hh : primary h) (k : ℕ) :
    lambdaE∣h*omegaE^k-1 := by
  convert dvd_add (dvd_mul_of_dvd_left (cubicThetaLambda_dvd_primary_sub_one hh) (omegaE^k))
    (cubicThetaLambda_dvd_omega_pow_sub_one k) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTopPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected top-row contribution has the same explicit phase as
the middle-row eigenvector. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNegativeInverseUnit_power (j : Fin 3) :
    (((-(cubicThetaOmegaUnit^(j:ℕ))⁻¹):Eisensteinˣ):Eisenstein)=
      -omegaE^(cubicThetaInverseUnitIndex j:ℕ) := by
  fin_cases j
  · norm_num [cubicThetaInverseUnitIndex]
  · norm_num [cubicThetaInverseUnitIndex,cubicThetaOmegaUnit_inverse_value]
  · norm_num [cubicThetaInverseUnitIndex,cubicThetaOmegaUnit_inverse_value]
    change (omegaE^2)^2=omegaE
    rw [←pow_mul,show 2*2=3+1 by omega,pow_add,omegaE_cube,pow_one,one_mul]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientPrimaryReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove every ramified and nonprimary frequency from the remaining
coefficient identification problem. This is an equivalence of exact goals,
not an additional analytic input. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimaryRepresentative {h : Eisenstein} (hh : ¬lambdaE∣h) :
    ∃ (a : Eisenstein) (e : Eisensteinˣ), primary a ∧ h=a*(e:Eisenstein) := by
  have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero lambdaE)
  obtain ⟨e,k,a,ha,he⟩ := unit_ramified_primary_decomposition h0
  have hm := congrArg (emultiplicity lambdaE) he
  simp only [emultiplicity_eq_zero.mpr hh,emultiplicity_mul lambdaE_prime,
    unit_lambda_emultiplicity,emultiplicity_pow_self_of_prime lambdaE_prime,
    primary_lambda_emultiplicity ha,zero_add,add_zero] at hm
  have hk : k=0 := by exact_mod_cast hm.symm
  exact ⟨a,e,ha,by simpa only [hk,pow_zero,mul_one,mul_comm] using he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelSection
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the global cubic automorphy of the continuous arithmetic
model from its actual L2 residue and the full positive-strip identities. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaArithmeticModelSectionCountable : Countable Eisenstein :=
  coordinatesEquiv.symm.injective.countable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Dirichlet-series Mellin expression of the constructed cubic
cusp expansion, justified by absolute integration on the initial half-plane. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaDirichlet (a : Eisenstein → ℂ) (u : ℂ) : ℂ :=
  ∑' n : Eisenstein, if n = 0 then 0 else
    a n*(‖cubicThetaFrequency n‖:ℂ)^(-u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCircleActual
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-circle coefficients of the actual fixed-height theta series.
Both orientations retain their precise signed angular coefficients. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaCircleFrequency (rev : Bool) (d : ℂ) (n : Eisenstein) : ℂ :=
  if rev then star (cubicThetaFrequency n*d) else cubicThetaFrequency n*d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelAngularReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put every genuine signed angular transformation on the symmetric height scale. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaLevelAngularRoot (q : Eisenstein) (rev : Bool) (k : ℕ) : ℂ :=
  (cubicThetaCircleMultiplier (!rev) (-(norm q:ℂ)/(q:ℂ)^2))^k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDirichletBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence gives uniform bounds on each initial vertical line. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaDirichletNormMass (σ : ℝ) : ℝ :=
  ∑' n : Eisenstein, if n=0 then 0 else ‖cubicThetaFrequency n‖^(-σ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNineCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed first column with lower-right entry divisible by nine.
This makes the common-lattice additive phase a literal residue character. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicTheta_coprime_nine {r : Eisenstein} (hr : primary r) : IsCoprime r 9 := by
  convert (primary_coprime_three hr).pow_right (n:=2) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

def cubicThetaInverseNine (r : Eisenstein) (hr : primary r) : Eisenstein :=
  Classical.choose (cubicTheta_coprime_nine hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual support is indexed once by its unit, ramified order,
squarefree primary factor and primary cube factor. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaCommonNumerator (x : CubicThetaCommonIndex) : Eisenstein :=
  (x.1:Eisenstein)*lambdaE^x.2.1*(x.2.2.val.1*x.2.2.val.2^3)

def cubicThetaCommonCoordinates (x : CubicThetaCommonIndex) :
    CubicThetaCoordinates (cubicThetaCommonNumerator x) where
  unit := x.1
  order := x.2.1
  squarefreePart := x.2.2.val.1
  cubePart := x.2.2.val.2
  squarefree_primary := x.2.2.property.1
  cube_primary := x.2.2.property.2.1
  squarefree := x.2.2.property.2.2
  numerator_eq := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCancellation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary-cube scaling of the actual dual coefficient and its
local Ramanujan factor. These are the algebraic inputs to free-cube removal. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaDualCube (d : Eisenstein) (hd : primary d)
    (n : MetaplecticDualArgument) : MetaplecticDualArgument :=
  ⟨n.val*d^3,mul_ne_zero n.property (pow_ne_zero 3 (primary_ne_zero hd))⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical removal of the free primary cube. The remaining cube part
is supported on the level, and the removed factor is coprime to it. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicTheta_primarySmallPart_supported {r a : Eisenstein} (hr : r≠0)
    (_ha : primary a) : ∃ k : ℕ, primarySmallPart r a∣r^k := by
  let ν := supportedIdealPart r (idealExponentOf a)
  let k := ν.support.sup ν
  have hle : ν≤k•idealExponentOf r := by
    intro p
    change ν p≤k*idealExponentOf r p
    by_cases hp : ν p=0
    · rw [hp]
      exact Nat.zero_le _
    · have hpm : p∈ν.support := Finsupp.mem_support_iff.mpr hp
      have hpr : idealExponentOf r p≠0 := by
        intro hz
        exact hp (by simp [ν,supportedIdealPart,hz])
      exact (Finset.le_sup hpm).trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpr))
  refine ⟨k,?_⟩
  change primaryNormalize (idealExponentGenerator ν)∣r^k
  have hd := idealExponentGenerator_dvd_of_le hle
  have he : k•idealExponentOf r=idealExponentOf (r^k) := (idealExponentOf_pow hr k).symm
  rw [he] at hd
  exact (primaryNormalize_associated _).symm.dvd.trans
    (hd.trans (idealExponentOf_associated (pow_ne_zero _ hr)).dvd)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeCubeIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact bijection separating every primary cube factor into the
part supported on the level and the free part. No multiplicity is lost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaFreeCubeJoin (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) : CubicThetaCommonIndex :=
  (x.1.val.1,x.1.val.2.1,⟨(x.1.val.2.2.val.1,x.1.val.2.2.val.2*(x.2.val:Eisenstein)),
    x.1.val.2.2.property.1,
    primary_mul x.1.val.2.2.property.2.1 x.2.val.property,
    x.1.val.2.2.property.2.2⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeLocalVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete angular transform with the free cube variable separated.
Both its coefficient bound and its absolutely convergent sum are proved. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaCommonArgument (x : CubicThetaCommonIndex) : MetaplecticDualArgument :=
  ⟨cubicThetaCommonNumerator x,(cubicThetaCommonCoordinates x).ne_zero⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreArguments
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported core indices and free primary factors give exactly the
nonzero domain of the full dual sum, with all zero extensions retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaCoreArgument {r : Eisenstein} (x : CubicThetaCoreIndex r) : MetaplecticDualArgument :=
  cubicThetaCommonArgument x.val

def cubicThetaCoreFreeArgument (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    MetaplecticDualArgument × PrimaryArgument := (cubicThetaCoreArgument x.1,x.2.val)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullLevelRows
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All level-three rows before the coprimality restriction. They form
one explicit affine lattice; primary common factors preserve the lattice. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaFullRowCoordinates (a b : Eisenstein) : CubicThetaFullRow where
  c := 3*a
  d := 1+3*b
  c_three := ⟨a,rfl⟩
  d_primary := ⟨b,by ring⟩

lemma cubicThetaFullRowCoordinates_injective :
    Function.Injective (fun p : Eisenstein × Eisenstein => cubicThetaFullRowCoordinates p.1 p.2) := by
  intro p q he
  have hc := congrArg CubicThetaFullRow.c he
  have hd := congrArg CubicThetaFullRow.d he
  apply Prod.ext
  · exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) hc
  · exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) (add_left_cancel hd)

lemma cubicThetaFullRowCoordinates_surjective :
    Function.Surjective (fun p : Eisenstein × Eisenstein => cubicThetaFullRowCoordinates p.1 p.2) := by
  intro r
  obtain ⟨a,ha⟩ := r.c_three
  obtain ⟨b,hb⟩ := r.d_primary
  refine ⟨(a,b),?_⟩
  apply CubicThetaFullRow.ext
  · exact ha.symm
  · change 1+3*b=r.d
    linear_combination -hb

def cubicThetaFullRowEquiv : Eisenstein × Eisenstein ≃ CubicThetaFullRow :=
  Equiv.ofBijective (fun p => cubicThetaFullRowCoordinates p.1 p.2)
    ⟨cubicThetaFullRowCoordinates_injective,cubicThetaFullRowCoordinates_surjective⟩

def cubicThetaFullRowMultiply (g : PrimaryArgument) (r : CubicThetaBottomRow) : CubicThetaFullRow where
  c := g.val*r.c
  d := g.val*r.d
  c_three := dvd_mul_of_dvd_right r.c_three _
  d_primary := primary_mul g.property r.d_primary

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveRowFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique extraction of the primary common factor of a level-three row.
The inverse uses a Bezout identity for its actual gcd. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullRowMultiply_surjective :
    Function.Surjective (fun p : PrimaryArgument × CubicThetaBottomRow =>
      cubicThetaFullRowMultiply p.1 p.2) := by
  classical
  let := EuclideanDomain.gcdMonoid Eisenstein
  intro r
  let d := GCDMonoid.gcd r.c r.d
  let g := primaryNormalize d
  have hgd : g ∣ r.d :=
    (primaryNormalize_associated d).symm.dvd.trans (GCDMonoid.gcd_dvd_right r.c r.d)
  have hg : primary g := primaryNormalize_primary
    (unit_residue_of_dvd_primary r.d_primary (GCDMonoid.gcd_dvd_right r.c r.d))
  have hg0 : g≠0 := primary_ne_zero hg
  have hgc : g ∣ r.c :=
    (primaryNormalize_associated d).symm.dvd.trans (GCDMonoid.gcd_dvd_left r.c r.d)
  obtain ⟨x,y,hxy⟩ := exists_gcd_eq_mul_add_mul r.c r.d
  obtain ⟨u,hu⟩ := primaryNormalize_associated d
  change d=r.c*x+r.d*y at hxy
  change d*(u:Eisenstein)=g at hu
  clear_value g d
  obtain ⟨a,ha⟩ := hgc
  obtain ⟨b,hb⟩ := hgd
  have hbprim : primary b := primary_of_mul hg (by rw [←hb]; exact r.d_primary)
  have ha3 : (3:Eisenstein) ∣ a :=
    (primary_coprime_three hg).symm.dvd_of_dvd_mul_left (by rw [←ha]; exact r.c_three)
  have hab : IsCoprime a b := by
    refine ⟨x*u,y*u,?_⟩
    apply mul_left_cancel₀ hg0
    calc
      g*(x*u*a+y*u*b)=(r.c*x+r.d*y)*u := by rw [ha,hb]; ring
      _ = g := by rw [←hxy]; exact hu
      _ = g*1 := (mul_one g).symm
  let q : CubicThetaBottomRow := ⟨a,b,ha3,hbprim,hab⟩
  refine ⟨(⟨g,hg⟩,q),?_⟩
  apply CubicThetaFullRow.ext
  · exact ha.symm
  · exact hb.symm

lemma cubicThetaFullRow_factor_dvd (g h : PrimaryArgument)
    (r s : CubicThetaBottomRow)
    (hc : g.val*r.c=h.val*s.c) (hd : g.val*r.d=h.val*s.d) :
    g.val ∣ h.val := by
  obtain ⟨x,y,hxy⟩ := s.coprime
  have he : h.val=(h.val*s.c)*x+(h.val*s.d)*y := by
    linear_combination -h.val*hxy
  rw [he,←hc,←hd]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right g.val r.c) x)
    (dvd_mul_of_dvd_left (dvd_mul_right g.val r.d) y)

lemma cubicThetaFullRowMultiply_injective :
    Function.Injective (fun p : PrimaryArgument × CubicThetaBottomRow =>
      cubicThetaFullRowMultiply p.1 p.2) := by
  rintro ⟨g,r⟩ ⟨h,s⟩ he
  have hc : g.val*r.c=h.val*s.c := congrArg CubicThetaFullRow.c he
  have hd : g.val*r.d=h.val*s.d := congrArg CubicThetaFullRow.d he
  have gh : g=h := Subtype.ext (primary_associated_eq g.property h.property
    (associated_of_dvd_dvd (cubicThetaFullRow_factor_dvd g h r s hc hd)
      (cubicThetaFullRow_factor_dvd h g s r hc.symm hd.symm)))
  subst h
  have hrs : r=s := CubicThetaBottomRow.ext
    (mul_left_cancel₀ (primary_ne_zero g.property) hc)
    (mul_left_cancel₀ (primary_ne_zero g.property) hd)
  subst s
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarFactorization
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of common primary factors from the scalar height series. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaFullHeightMass (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaFullRow,r.height p^s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussian
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual affine four-dimensional Gaussian, before removal of common
primary factors. Its Mellin integral is the full height series. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaFullGaussian (p : ℂ × ℝ) (t : ℝ) : ℝ :=
  ∑' r : CubicThetaFullRow, Real.exp (-t*r.quadratic p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussianMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin interchange for the literal affine row heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_2_r72b9b7_1 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance instCountableCubicThetaFullRow_r72b9b7_1 : Countable CubicThetaFullRow := cubicThetaFullRowEquiv.symm.injective.countable
def cubicThetaFullGaussianMellinTerm (p : ℂ × ℝ) (s : ℝ)
    (r : CubicThetaFullRow) (t : ℝ) : ℝ := t^(s-1)*Real.exp (-t*r.quadratic p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNonzeroRowHeat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal two-coordinate Gaussian behind the nonzero-first-row bound. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNonzeroRowQuadratic (p : ℂ × ℝ) (r : CubicThetaNonzeroRow) : ℝ :=
  Complex.normSq ((r.1.val:ℂ)*p.1+r.2)/p.2+norm r.1.val*p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTailCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinate parametrizations for the two arithmetic remainder families. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaOrdinaryCoordinate (p : CubicThetaIntegerPoint) : Eisenstein :=
  ofCoords p.1 p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRemainderWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A summable majorant on the actual Fourier lattice, with its full mass bounded. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaHighRemainderWeight : Eisenstein → ℝ :=
  cubicThetaMassPushforward (fun p => lambdaE^3*cubicThetaOrdinaryCoordinate p)
    cubicThetaRamifiedDerivativeWeight

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarHeightCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the finitely many rows above height one preserves the scalar
Eisenstein pole. The remaining positive kernel is the one used in the
Rankin integral of the square-integrable theta section. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaScalarHeightCutoff (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaBottomRow,if r.height p≤1 then r.height p^s else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarRankinKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive truncated scalar kernel on the actual arithmetic quotient.
Its residue is known before any integration against the theta norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaScalarRankinKernel (σ : ℝ) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaScalarHeightCutoff (cubicThetaBorelSection q).val (2+2*σ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailLevel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long completion coefficient separates exactly into one fixed
factor and a coprimality restriction on the original outer coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticTailOuter (e : Eisenstein) (α : Eisenstein → ℂ) (r : Eisenstein) : ℂ :=
  if IsCoprime e r then α r else 0

end CubicFirstMoment

end

end OAI
end


