-- Prove2me | Definitions.Def_OAIQ096A015
-- name    : OAIQ096A015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:44:22.707601+00:00
-- url     : https://prove2.me/theorems/fe9d718f-2ba7-4284-9ecb-a342a004a783
-- title:
--   Definitions bundle OAIQ096A015 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 168 definitions, 1 instance and 16 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaMassPairEquiv`, `OAI.CubicFirstMoment.cubicThetaNegativeRemainderWeight`, `OAI.CubicFirstMoment.cubicThetaNonzeroFirstPrimitiveRow_map`, `OAI.CubicFirstMoment.cubicThetaPairMassTerm`, `OAI.CubicFirstMoment.cubicThetaPositiveRemainderWeight`, `OAI.CubicFirstMoment.cubicThetaPrimaryCoordinate`, `OAI.CubicFirstMoment.cubicThetaPrimaryGaussSum`, `OAI.CubicFirstMoment.cubicThetaPrimaryIndexEquiv`, `OAI.CubicFirstMoment.cubicThetaPrimaryMass`, `OAI.CubicFirstMoment.cubicThetaPrimaryPairEquiv`, `OAI.CubicFirstMoment.cubicThetaPrimitiveHeat`, `OAI.CubicFirstMoment.cubicThetaPrimitiveHeatMellinTerm`, `OAI.CubicFirstMoment.cubicThetaPrimitiveHeatTerm`, `OAI.CubicFirstMoment.cubicThetaPrimitiveKernel`, `OAI.CubicFirstMoment.cubicThetaRamifiedMass`, `OAI.CubicFirstMoment.cubicThetaRightInversionPrincipal`, `OAI.CubicFirstMoment.cubicThetaScalarHeightHigh`, `OAI.CubicFirstMoment.cubicThetaScalarHeightMass`, `OAI.CubicFirstMoment.cubicThetaShiftedBareTerm`, `OAI.CubicFirstMoment.cubicThetaShiftedFourierTerm`, `OAI.CubicFirstMoment.cubicThetaShiftedFourierWeight`, `OAI.CubicFirstMoment.cubicThetaShiftedFrequencyDirichlet`, `OAI.CubicFirstMoment.cubicThetaShiftedGridTerm`, `OAI.CubicFirstMoment.cubicThetaShiftedInvertedTerm`, `OAI.CubicFirstMoment.cubicThetaShiftedPoleRadial`, `OAI.CubicFirstMoment.cubicThetaShiftedPositiveRadialTest`, `OAI.CubicFirstMoment.cubicThetaShiftedWindowRadialTest`, `OAI.CubicFirstMoment.cubicThetaSievePhase`, `OAI.CubicFirstMoment.cubicThetaSquareIndexEquiv`, `OAI.CubicFirstMoment.cubicThetaSquareNumerator`, `OAI.CubicFirstMoment.cubicThetaSquarefreeMass`, `OAI.CubicFirstMoment.cubicThetaUnitRow`, `OAI.CubicFirstMoment.cubicThetaZeroFirstRowEquiv`, `OAI.CubicFirstMoment.cutoffBilinearTail`, `OAI.CubicFirstMoment.cutoffBilinearWindow`, `OAI.CubicFirstMoment.distinguishedShiftedSideTest`, `OAI.CubicFirstMoment.distinguishedSubsetWeight`, `OAI.CubicFirstMoment.divisorCoprimeDispersionGram`, `OAI.CubicFirstMoment.divisorCubePoissonContribution`, `OAI.CubicFirstMoment.divisorGramCoefficient` and 128 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_MellinDecay`, `CubicMoment_Angular_AngularCoordinateWeightedTuple`, `CubicMoment_Angular_AngularFullPrimeConvolution`, `CubicMoment_Angular_AngularFullSmoothFactor`, `CubicMoment_Angular_AngularLogSmallTwist`, `CubicMoment_Angular_AngularNormalizedCoordinateTuple`, `CubicMoment_Angular_AngularResidueLift`, `CubicMoment_Angular_AngularShortTupleMellin`, `CubicMoment_Angular_AngularShortTuplePartition`, `CubicMoment_Angular_AngularShortUnsplitTuple`, `CubicMoment_Angular_AngularSmallTwistSmoothMoment`, `CubicMoment_Decomposition_DistinguishedProductPairs`, `CubicMoment_Decomposition_PrimeProductHeight`, `CubicMoment_Decomposition_StoppedAbsoluteMass`, `CubicMoment_Decomposition_StoppedBinDecomposition`, `CubicMoment_Decomposition_StoppedDistinguishedIdentity`, `CubicMoment_Decomposition_StoppedDistinguishedRows`, `CubicMoment_Decomposition_StoppedDivisorPartition`, `CubicMoment_Decomposition_StoppedDivisorRows`, `CubicMoment_Decomposition_StoppedLargestRoles`, `CubicMoment_Decomposition_StoppedLongBinSaving`, `CubicMoment_Decomposition_StoppedMellinRows`, `CubicMoment_Decomposition_StoppedProductCoefficient`, `CubicMoment_Decomposition_StoppedProductModel`, `CubicMoment_Decomposition_StoppedSelectedBeta`, `CubicMoment_Decomposition_StoppedSelectedReindex`, `CubicMoment_Decomposition_StoppedSelectedRow`, `CubicMoment_Decomposition_StoppingThreshold`, `CubicMoment_Decomposition_StoppingTwoStage`, `CubicMoment_Estimates_ArithmeticTwist`, `CubicMoment_Estimates_BilinearHeightTail`, `CubicMoment_Estimates_CommonHeightCoefficient`, `CubicMoment_Estimates_CommonVarianceDecomposition`, `CubicMoment_Estimates_ConductorNeighborhoods`, `CubicMoment_Estimates_CubicMomentGram`, `CubicMoment_Estimates_DivisorCoefficient`, `CubicMoment_Estimates_DivisorCoprimePoisson`, `CubicMoment_Estimates_DivisorCubeTerm`, `CubicMoment_Estimates_DivisorNoncubeTotal`, `CubicMoment_Estimates_DivisorPoissonRadial`, `CubicMoment_Estimates_FarLogCellHeight`, `CubicMoment_Estimates_FinitePoissonRadial`, `CubicMoment_Estimates_FullPrimeConvolution`, `CubicMoment_Estimates_FullStructuredMeanValue`, `CubicMoment_Estimates_HeckeSmoothApproximation`, `CubicMoment_Estimates_HuxleyGaussianEnergy`, `CubicMoment_Estimates_HuxleyResiduePoints`, `CubicMoment_Estimates_IdealHeatTheta`, `CubicMoment_Estimates_IdealMangoldtDyadic`, `CubicMoment_Estimates_IdealMangoldtMellin`, `CubicMoment_Estimates_IdealMangoldtPrefix`, `CubicMoment_Estimates_IdealPrimePowerCount`, `CubicMoment_Estimates_IdealPrimeReplacement`, `CubicMoment_Estimates_LargeTupleFullSupport`, `CubicMoment_Estimates_LargeTupleKernelIntegral`, `CubicMoment_Estimates_LargestPrimeCanonical`, `CubicMoment_Estimates_LargestPrimeSelection`, `CubicMoment_Estimates_LogCellNearHeight`, `CubicMoment_Estimates_LowCutoffWindow`, `CubicMoment_Estimates_MellinDualTail`, `CubicMoment_Estimates_MixedModelCoprime`, `CubicMoment_Estimates_NoncubePoissonTotal`, `CubicMoment_Estimates_NormProfileOperator`, `CubicMoment_Estimates_NormalizedCoordinateTuple`, `CubicMoment_Estimates_PrimeHeightDecomposition`, `CubicMoment_Estimates_PrimeIdealBall`, `CubicMoment_Estimates_PrimeLogReplacement`, `CubicMoment_Estimates_PrimeModelTail`, `CubicMoment_Estimates_PrimeStoppingCollection`, `CubicMoment_Estimates_PrimeStoppingSplit`, `CubicMoment_Estimates_PrincipalZetaContinuation`, `CubicMoment_Estimates_RestrictedNoStopCoefficient`, `CubicMoment_Estimates_ScaleFirstStoppedTailEnvelope`, `CubicMoment_Estimates_ScaleFirstStoppedTransport`, `CubicMoment_Estimates_SemiprimeBilinear`, `CubicMoment_Estimates_SemiprimeBlockEstimate`, `CubicMoment_Estimates_SemiprimeHeightBlock`, `CubicMoment_Estimates_SmallBVarianceRemainder`, `CubicMoment_Estimates_SmoothShortFamily`, `CubicMoment_Estimates_StructuredHeightMass`, `CubicMoment_Estimates_StructuredMeanValue`, `CubicMoment_Estimates_TwistedRetainedMoment`, `CubicMoment_Estimates_TypeICutoffWindow`, `CubicMoment_Estimates_TypeIHeightIntegral`, `CubicMoment_Estimates_TypeILowHeightTwist`, `CubicMoment_Estimates_TypeILowIntegral`, `CubicMoment_Estimates_TypeIMixedDyads`, `CubicMoment_Estimates_TypeIMixedWeights`, `CubicMoment_Estimates_TypeIProductLow`, `CubicMoment_Estimates_TypeIProductSupport`, `CubicMoment_Estimates_TypeIProductWindow`, `CubicMoment_Theta_CubicThetaAdaptedMultiplier`, `CubicMoment_Theta_CubicThetaCharacterAverage`, `CubicMoment_Theta_CubicThetaInverseResidues`, `CubicMoment_Theta_CubicThetaMassFactorization`, `CubicMoment_Theta_CubicThetaPrimaryIndex`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimitiveHeat`, `CubicMoment_Theta_CubicThetaPrimitiveHeatCusp`, `CubicMoment_Theta_CubicThetaPrimitiveKernel`, `CubicMoment_Theta_CubicThetaPrimitiveZeroRows`, `CubicMoment_Theta_CubicThetaRamifiedMass`, `CubicMoment_Theta_CubicThetaRawPairs`, `CubicMoment_Theta_CubicThetaRemainderWeights`, `CubicMoment_Theta_CubicThetaScalarFactorization`, `CubicMoment_Theta_CubicThetaScalarHeightCutoff`, `CubicMoment_Theta_CubicThetaShiftedGaussExplicit`, `CubicMoment_Theta_CubicThetaShiftedHorizontalContinuity`, `CubicMoment_Theta_CubicThetaShiftedInvertedRows`, `CubicMoment_Theta_CubicThetaShiftedModelSeries`, `CubicMoment_Theta_CubicThetaShiftedRadialMellin`, `CubicMoment_Theta_CubicThetaShiftedTorus`, `CubicMoment_Theta_CubicThetaShiftedUnfold`, `CubicMoment_Theta_CubicThetaShiftedWindowFourier`, `CubicMoment_Theta_CubicThetaShiftedWindowTest`, `CubicMoment_Theta_CubicThetaSievePhase`, `CubicMoment_Theta_CubicThetaSieveSupport`, `CubicMoment_Theta_CubicThetaSquareDecomposition`, `CubicMoment_Theta_CubicThetaTailCoordinates`, `CubicMoment_Transform_MetaplecticActualInverse`, `CubicMoment_Transform_MetaplecticBlockCoefficient`, `CubicMoment_Transform_MetaplecticCodeDyads`, `CubicMoment_Transform_MetaplecticCodeMean`, `CubicMoment_Transform_MetaplecticCodePartition`, `CubicMoment_Transform_MetaplecticCoefficientMass`, `CubicMoment_Transform_MetaplecticCoefficientSeries`, `CubicMoment_Transform_MetaplecticDecompletion`, `CubicMoment_Transform_MetaplecticDualFinite`, `CubicMoment_Transform_MetaplecticDualTailWeights`, `CubicMoment_Transform_MetaplecticFreeFrequency`, `CubicMoment_Transform_MetaplecticLongCompletion`, `CubicMoment_Transform_MetaplecticLongDyads`, `CubicMoment_Transform_MetaplecticPrimaryCompletion`, `CubicMoment_Transform_MetaplecticPrimaryInverse`, `CubicMoment_Transform_MetaplecticRetainedCritical`, `CubicMoment_Transform_MetaplecticRetainedSupport`, `CubicMoment_Transform_MetaplecticShortInverse`, `CubicMoment_Transform_MetaplecticTailCoefficient`, `CubicMoment_Transform_MetaplecticTailLevel`, `CubicMoment_Transform_MetaplecticVoronoi`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A007`, `OAIQ096A008`, `OAIQ096A009` and `OAIQ096A010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A019` and `OAIQ096A020`; the statements `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve`, `OAI.CubicFirstMoment.ProfileControl.low_poisson_dyadic_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.low_variance_remainder_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power`, `OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power`, `OAI_CubicFirstMoment_UniformLogWeights_cubeModelTerm_mass_error`, `OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood`, `OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood`, `OAI_CubicFirstMoment_angular_corrected_dispersion_asymptotic_actual`, `OAI_CubicFirstMoment_angular_cube_poisson_log_saving`, `OAI_CubicFirstMoment_angular_divisor_full_model_asymptotic`, `OAI.CubicFirstMoment.angular_divisor_noncube_total_saving`, `OAI.CubicFirstMoment.angular_exceptional_residual_moment`, `OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood`, `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving`, `OAI.CubicFirstMoment.angular_height_signed_mellin_saving`, `OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual`, `OAI.CubicFirstMoment.angular_noncube_poisson_total_saving`, `OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all`, `OAI_CubicFirstMoment_angular_stopped_cube_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_angular_stopped_divisor_full_model_log_saving`, `OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total`, `OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual`, `OAI.CubicFirstMoment.balanced_common_normalized_exponents`, `OAI.CubicFirstMoment.bounded_poisson_dyadic`, `OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving`, `OAI_CubicFirstMoment_cube_poisson_log_saving`, `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO`, `OAI.CubicFirstMoment.divisor_noncube_total_saving`, `OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer`, `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.low_far_logCell_integrated_bound`, `OAI.CubicFirstMoment.noncube_poisson_total_saving`, `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved`, `OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate`, `OAI.CubicFirstMoment.stoppedBeta_selected_log_saving`, `OAI_CubicFirstMoment_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_stopped_divisor_coprime_model_log_saving`, `OAI.CubicFirstMoment.stopped_divisor_noncube_total`, `OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass`, `OAI.CubicFirstMoment.stopped_low_core_mass`, `OAI.CubicFirstMoment.stopped_typeI_mixed_actual` and `OAI.CubicFirstMoment.uniform_core_block_polynomial_height`; the proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve`, `OAI_CubicFirstMoment_UniformLogWeights_cubeModelTerm_mass_error`, `OAI_CubicFirstMoment_angular_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_angular_cube_poisson_log_saving`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO`, `OAI_CubicFirstMoment_angular_sieved_squarefree_model_asymptotic`, `OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all`, `OAI.CubicFirstMoment.angular_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_angular_stopped_cube_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_cube_uniform_error`, `OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total`, `OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual`, `OAI_CubicFirstMoment_angular_stopped_squarefree_model_log_saving`, `OAI_CubicFirstMoment_balanced_common_squarefree_exponents`, `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_cube_poisson_log_saving`, `OAI.CubicFirstMoment.first_angular_primeCoordinateError_moment`, `OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay`, `OAI_CubicFirstMoment_kummer_unweighted_from_primitive`, `OAI.CubicFirstMoment.localized_integral_power_saving`, `OAI_CubicFirstMoment_logCell_bilinear_height_square`, `OAI.CubicFirstMoment.low_far_logCell_integrated_bound`, `OAI.CubicFirstMoment.low_localized_height_integral_bound`, `OAI_CubicFirstMoment_low_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_low_shrinking_variance_remainder`, `OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving`, `OAI_CubicFirstMoment_sieved_squarefree_model_asymptotic`, `OAI.CubicFirstMoment.stoppedBeta_selected_log_saving`, `OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual`, `OAI_CubicFirstMoment_stopped_cube_uniform_error`, `OAI.CubicFirstMoment.stopped_divisor_noncube_total`, `OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass`, `OAI.CubicFirstMoment.stopped_low_core_mass` and `OAI_CubicFirstMoment_stopped_squarefree_model_log_saving`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A009
import Definitions.Def_OAIQ096A010

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def gramMellinCoefficient (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ t : ℝ) : ℂ :=
  𝓕 (gramLogSchwartz W hW hW' ρ) t

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreePrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (squarefreeConvolution S w) ℓ u t

def errorPrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (squarefreeConvolutionError S w) ℓ u t

def twistedErrorPrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (fun b => squarefreeConvolutionError S w b * χ b) ℓ u t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinDualTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual far-left dual-series tails. The integer-line Gamma estimate
and smooth Mellin decay provide the analytic bounds. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- The integrand of the omitted part of the functional-equation series
on the line `Re s = 1/2-m`. -/
def heckeDualTailIntegrand (W : ℝ → ℂ) (χ : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A Z J : ℝ) (m : ℕ) (t τ : ℝ) : ℂ :=
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
  let u : ℂ := s-(t:ℂ)*Complex.I
  mellin W s*(Z:ℂ)^s*ε*(A:ℂ)^(1-2*u)*
    (Complex.Gamma (1-u)/Complex.Gamma u)*idealDirichletTail χ J (1-u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothApproximation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth Hecke sums are approximated by their retained dual
integrals, with an error smaller than any prescribed power. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def retainedHeckeIntegral (W : ℝ → ℂ) (χdual : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A Z J t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A
        ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedRetainedMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained functional-equation integrals of the actual primitive
characters have the cubic second moment, with explicit logarithmic losses. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def smallTwistMomentLoss (r : Eisenstein) (J : ℝ) : ℝ :=
  (((supportedParts (3*r) (fullIdealBall (2*J))).card:ℝ))^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmallTwistSmoothMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original primary mixed smooth sum has the cubic second moment.
Its primitive characters, conductors, and Euler corrections are constructed. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryAngularSmallTwistSmoothSum (ℓ : ℤ) (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x)*W (norm x/Z) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLogSmallTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dominant logarithmic full factor retains a positive power saving. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryAngularSmallTwistLogSmoothSum (ℓ : ℤ) (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    (Real.log (norm x):ℂ)*(mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*
      mellinPhase t (norm x))*W (norm x/Z) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact classification of the full smooth factors from the short inverse.
The short Möbius alternative vanishes once the dyad lies above its support. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryAngularShortSmoothSum (ℓ : ℤ) (A : EisensteinArithmeticFunction) (a b q : Eisenstein)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    ((MvPowerSeries.coeff (idealExponentOf x) A:ℝ):ℂ)*
      (mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x))*W (norm x/Z)
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicMomentGram
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Gram estimate for a finite cubic-character moment

This supplies the near-orthogonality inequality in the exceptional-character-moment argument
for the actual character polynomials. The only analytic estimate used
here is the cubic Gram theorem.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def primarySieveWeight (Z : ℝ) (n : Eisenstein) : ℝ :=
  if primary n then gramLogBump (norm n / Z) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructing the actual smooth short-factor family used in the exceptional
moments. Finite characters, norm phases and smooth dyads are explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def shortFamilyOfSmoothWeights {ι : Type*} (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1) : ShortFactorFamily ι where
  cutoff := fun _ => F
  length := fun _ => X
  coefficient := fun _ => A
  twist := fun _ i => smoothShortTwist (η i) (W i) (X i) (t i)
  factor_spec := fun _ => hA
  length_ge_one := fun _ => hX
  twist_bound := fun _ i n _ => smoothShortTwist_norm (hq i) (η i) (W i) (hW i) (X i) (t i) n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortTupleMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin separation for the actual smooth short-inverse factors. The
integrand is a product of the original primary sums, with a common shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularShortTupleSum (ℓ : ℤ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ n : (i : ι) → primaryElementBall (X i),
    (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
        mellinPhase (t i) (norm (n i)))*W i (norm (n i)/(X i/2)))*
      V ((∏ i, norm (n i))/Z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularTupleCore (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) (n : ι → Eisenstein) : ℂ :=
  (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ)*
    (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*theta ℓ (n i)*
      mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularShortUnsplitTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def primaryAngularUnsplitTuple (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    primaryAngularTupleCore ℓ A a b q η t V Y n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoordinateWeightedTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent smooth weights on the original arithmetic factors, with the
exact Mellin representation by the unweighted convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularCoordinateWeightedTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    primaryAngularTupleCore ℓ A a b q η t V Y n * ∏ i, W i (norm (n i)/X i)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Twisting actual ideal arithmetic functions by a residue character and
norm phase commutes with convolution. Different original factors may
therefore retain different Mellin heights throughout short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residueNormTwist (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ℂ :=
  residueIdealChar q η ν*mellinPhase t (idealExponentNorm ν)

def twistArithmetic (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) : MvPowerSeries EisensteinIdealPrime ℂ :=
  fun ν => ((MvPowerSeries.coeff ν A:ℝ):ℂ)*residueNormTwist q η t ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact replacement of a prime indicator by von Mangoldt divided by log norm.
The discrepancy is bounded and is supported on actual higher primary prime powers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeLogCorrection (a : Eisenstein) : ℝ :=
  normalizedVonMangoldt a-primeIndicator a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormalizedCoordinateTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact restoration of Λ/log(N) on each original factor. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryNormalizedVonMangoldtTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    (∏ i, (normalizedVonMangoldt (n i):ℂ)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exceptional moments hold throughout a fixed open neighborhood
of each exceptional conductor exponent. The neighborhoods are constructed by
contradiction from actual short-factor sequences, not assumed as analytic inputs. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedNeighborhoodAdmissible (δ H D C κ : ℝ)
    (x : ConductorMomentInstance ι (Eisenstein × Eisenstein)) : Prop :=
  (∀ i, x.family.length 0 i ≤ x.scale^(1-δ)) ∧
  (x.scale/C ≤ ∏ i, x.family.length 0 i) ∧
  (∏ i, x.family.length 0 i) ≤ C*x.scale ∧
  1 ≤ x.conductorScale ∧
  (x.scale^(1/3-κ) ≤ x.conductorScale ∧ x.conductorScale ≤ x.scale^(1/3+κ)) ∧
  (∀ p ∈ x.rows, PrimarySquarefreePair p ∧
    norm p.1 ≤ x.conductorScale ∧ norm p.2 ≤ x.conductorScale) ∧
  (x.rows.card:ℝ) ≤ x.scale^D ∧
  (∀ p ∈ x.rows, ∀ i, ‖x.family.mixedValue 0 i p‖ ≤ x.scale^H)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularResidueLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor above three compensates the fixed infinity type.
It is one on every primary element, so it does not change the original sums. -/
noncomputable section
namespace CubicFirstMoment

def structuredAngularTwistModulus (v e : Eisenstein) : Eisenstein :=
  structuredTwistModulus v e*3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite realization of the literal prime convolution: each coordinate
contains every primary prime on which its independent weight is nonzero. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullStructuredPrimeSum (R : ℝ) (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun z => IsCoprime z e),
    fullPrimeCoefficient R W X z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullStructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary published mean-value theorem applied to the literal
prime convolution, with every numerator and excluded-prime factor retained. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullStructuredAngularSum (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun z => IsCoprime z e),
    fullPrimeCoefficient R W X z*cubicSymbol z (v*h)*theta ℓ z*mellinPhase u (norm z)

def fullStructuredCoefficient (R : ℝ) (h v e : Eisenstein)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (z : Eisenstein) : ℂ :=
  if IsCoprime z e then fullPrimeCoefficient R W X z*cubicSymbol z (v*h) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularFullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def fullStructuredAngularPrimeSum (R : ℝ) (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun z => IsCoprime z e),
    fullPrimeCoefficient R W X z*theta ℓ z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNormalizedCoordinateTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact restoration of Λ/log(N) on each original factor. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularNormalizedVonMangoldtTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  primaryAngularCoefficientTuple ℓ (fun n => (normalizedVonMangoldt n:ℂ)) a b q η t W X V Y

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-bin identity with the actual selected divisor and its
complement. The crossing test only sees the selected divisor, while
inverse-binomial weighting restores every original squarefree term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppingSelected (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (j : ℕ) (t : Finset Eisenstein) : Finset Eisenstein :=
  primeBinPrefix s b j ∪ t

def stoppingRemainder (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (j : ℕ) (t : Finset Eisenstein) : Finset Eisenstein :=
  s \ stoppingSelected s b j t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeSelection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact selection of a largest prime, with a fixed injective tie code.
This is an unordered selection: inserting it into a finite sum introduces
no factor depending on the number of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma exists_largestPrime (code : Eisenstein → ℕ) (s : Finset Eisenstein)
    (hs : s.Nonempty) : ∃ p ∈ s, largestPrimePredicate code s p := by
  obtain ⟨q,hq,hnq⟩ := Finset.exists_mem_eq_sup s hs normNat
  let T := s.filter (fun p => normNat p = s.sup normNat)
  have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hq,hnq.symm⟩
  obtain ⟨p,hp,hcp⟩ := Finset.exists_mem_eq_sup T ⟨q,hqT⟩ code
  have hpn := (Finset.mem_filter.mp hp).2
  refine ⟨p,(Finset.mem_filter.mp hp).1,?_⟩
  intro r hr
  have hrn : normNat r ≤ normNat p := (Finset.le_sup (f := normNat) hr).trans_eq hpn.symm
  by_cases hlt : normNat r < normNat p
  · exact Or.inl hlt
  · have he : normNat r = normNat p := le_antisymm hrn (le_of_not_gt hlt)
    have hrT : r ∈ T := Finset.mem_filter.mpr ⟨hr,he.trans hpn⟩
    exact Or.inr ⟨he,hcp ▸ Finset.le_sup (f := code) hrT⟩

def selectedLargestPrime (s : Finset Eisenstein) (hs : s.Nonempty) : Eisenstein :=
  Classical.choose (exists_largestPrime primeTieCode s hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeCanonical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical functions for the exact largest-prime change of variables.
They allow predicates on the original product to be rewritten after the
finite reindexing, without a choice-dependent coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largestPrimeChoice (n : Eisenstein) : Eisenstein :=
  if h : (primaryPrimeFactors n).Nonempty then selectedLargestPrime (primaryPrimeFactors n) h else 1

def largestPrimeRemainder (n : Eisenstein) : Eisenstein :=
  ∏ q ∈ (primaryPrimeFactors n).erase (largestPrimeChoice n), q

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeStoppingCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite reindexing from choices in the stopping bin to the
independent selected and complementary divisor subsets. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppingDivisorSubsets (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (j k : ℕ) : Finset (Finset Eisenstein) :=
  s.powerset.filter (fun d =>
    (∀ p ∈ d, bin p ≤ j) ∧ (primeBin d bin j).card = k ∧
      (∀ p ∈ s \ d, j ≤ bin p))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingThreshold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact no-stop/stopped split. The original product kernel may
contain a sharp norm cutoff; no continuity is required. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def geometricStoppedElement (ρ X R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) : ℂ :=
  ∑ q ∈ stoppingLabelBox ρ X,
    ∑ t ∈ (primeBin (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t)
            (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
          (R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
              geometricBinLower ρ X q.1 < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t, p) *
            cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t, p)) *
          K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p)*
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p))
      else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedProductPairs
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the distinguished subset expansion by its
primary product. The original finite support remains inside each row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedSubsetWeight (ψ : ℝ → ℝ) (w z : ℝ) (r : Eisenstein) : ℂ :=
  ∏ p ∈ primaryPrimeFactors r, distinguishedPrimeWeight ψ w z p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullStructuredHeightMass (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ h ∈ H, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticDualTerm (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (σ X : ℝ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if IsCoprime (nd.2:Eisenstein) r then
    a r nd.1*metaplecticLocalCoefficient r nd.1/
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)*
      complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)*
      metaplecticTransform ℓ W σ
        ((2*Real.pi)^4*Complex.normSq ((nd.2:Eisenstein)^3*
          metaplecticFrequency nd.1)*X/(norm r)^2)
  else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FinitePoissonRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of a finite Poisson frequency block with the
radial form used in the Mellin estimates, including its scalar. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def finitePoissonContribution (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a W A h else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the separated arithmetic majorant from the actual Voronoi
support. The two free norm series and the ramified geometric series
converge, while the squarefree supported factor is a divisor of the level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCodeWeight (r : Eisenstein) (σ : ℝ) (z : MetaplecticCoefficientCode r) : ℝ :=
  metaplecticRamifiedRatio σ^z.1 *
    (1*(norm z.2.2.1.val^(-σ)*
      (norm z.2.2.2.1^(-3/2-3*σ)*norm z.2.2.2.2^(-1-σ))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective coding of the actual published theta coefficients gives
the absolute dual coefficient mass with a subpower level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticDecode (r : Eisenstein) (z : MetaplecticCoefficientCode r) : Eisenstein :=
  lambdaE^z.1*z.2.1.val*z.2.2.1.val*z.2.2.2.2.val*z.2.2.2.1.val^3

def metaplecticCoefficientMassTerm
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (σ : ℝ)
    (n : MetaplecticDualArgument) : ℝ :=
  ‖a r n*metaplecticLocalCoefficient r n‖/(Complex.normSq (metaplecticFrequency n))^(1+σ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticBlockCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual critical-line coefficients of a retained Voronoi block.
The free-variable inverse-square-root bound follows from the published
coefficient support and the two proved common-divisor bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticNormalizedDualCoefficient
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if IsCoprime (nd.2:Eisenstein) r then
    a r nd.1*metaplecticLocalCoefficient r nd.1 /
      ((Real.sqrt (Complex.normSq (metaplecticFrequency nd.1))*norm nd.2:ℝ):ℂ)*
      complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)
  else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualTailWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact exponent bookkeeping for truncating the metaplectic dual
series. The cutoff is in the actual norm N(d³ν). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def metaplecticDualNorm (nd : MetaplecticDualArgument × PrimaryArgument) : ℝ :=
  norm nd.2^3*Complex.normSq (metaplecticFrequency nd.1)

def metaplecticFarTailTerm (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if J < metaplecticDualNorm nd then metaplecticDualTerm a r ℓ W A X nd else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDualFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained Voronoi sum is an actual finite frequency polynomial.
Its cutoff is independent of the height parameter. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticDualBall (J : ℝ) : Finset (MetaplecticDualArgument × PrimaryArgument) :=
  (((nonzeroNormBall (3*J)).subtype (fun n => n ≠ 0)).product
    ((primaryElementBall (3*J)).subtype primary)).filter (fun nd => metaplecticDualNorm nd ≤ J)

def metaplecticRetainedTerm (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if metaplecticDualNorm nd ≤ J then metaplecticDualTerm a r ℓ W A X nd else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedCritical
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite retained Voronoi sum on the critical line, with
its coefficients normalized for ordinary free-variable mean value. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticRawDualCoefficient
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if IsCoprime (nd.2:Eisenstein) r then
    a r nd.1*metaplecticLocalCoefficient r nd.1 /
      ((Complex.normSq (metaplecticFrequency nd.1)*norm nd.2^(5/2:ℝ):ℝ):ℂ)*
      complexAngular (-ℓ) ((nd.2:Eisenstein)^3*metaplecticFrequency nd.1)
  else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticFreeFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal free-variable parametrization of each supported Voronoi
block, including the ramified exponent k=0 (j=-1). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_lambda_ne_zero : lambdaE ≠ 0 := by
  intro h
  apply traceLambda_ne_zero
  rw [←lambdaE_coe,h]
  rfl

def metaplecticFreeArgument (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) (w : Eisenstein) : MetaplecticDualArgument :=
  if hw : w ≠ 0 then
    ⟨lambdaE^k*ζ.val*h.val*w*h'.val^3,
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (pow_ne_zero k metaplectic_lambda_ne_zero) ζ.ne_zero)
        (primary_ne_zero h.property)) hw) (pow_ne_zero 3 (primary_ne_zero h'.property))⟩
  else ⟨1,one_ne_zero⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the literal published support representation once for each
nonzero retained coefficient. The resulting finite code set decodes
injectively to the original frequency set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrefixArgument (r : Eisenstein) (p : MetaplecticSupportPrefix r)
    (w : Eisenstein) : MetaplecticDualArgument :=
  metaplecticFreeArgument p.1 p.2.1 (metaplecticDivisorPrimary r p.2.2.1) p.2.2.2 w

def metaplecticRetainedDecode (r : Eisenstein) (z : MetaplecticRetainedCode r) :
    MetaplecticDualArgument × PrimaryArgument :=
  (metaplecticPrefixArgument r z.2.1 z.2.2.val,z.1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodeDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact norm dyad of each free variable after fixing the supported
parameters in the retained Voronoi sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCodePrefix {r : Eisenstein} (z : MetaplecticRetainedCode r) :
    MetaplecticDyadPrefix r := (z.1,z.2.1)

def metaplecticFreeScale {r : Eisenstein} (p : MetaplecticDyadPrefix r) : ℝ :=
  norm p.1^3*((3:ℝ)^((p.2.1:ℝ)-1)*norm p.2.2.2.1.val*norm p.2.2.2.2^3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite partition of the chosen retained frequencies by their
supported prefix. The remaining index is the literal primary free variable. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCodeFreeSet {r : Eisenstein} (T : Finset (MetaplecticRetainedCode r))
    (p : MetaplecticDyadPrefix r) : Finset Eisenstein :=
  (T.filter (fun z => metaplecticCodePrefix z = p)).image (fun z => z.2.2.val)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary mean values for the exact finite prefix partition. The
coefficient hypotheses here are precisely the support data supplied by
`metaplectic_retained_support_partition`. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrefixAmplitude (r : Eisenstein) (C : ℝ)
    (p : MetaplecticDyadPrefix r) : ℝ :=
  C*3^((max ((p.2.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm p.2.2.2.2)*
    min (norm r) (norm p.2.2.2.1.val*norm p.2.2.2.2) /
    (Real.sqrt ((3:ℝ)^((p.2.1:ℝ)-1)*norm p.2.2.2.1.val*norm p.2.2.2.2^3)*norm p.1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubePoissonTotal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full noncube Poisson contribution: the bounded-conductor proof and
the actual infinite high-frequency tail give the full contribution. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def noncubePoissonContribution (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' j : ℕ, finitePoissonContribution S
    ((frequencyDyad j).filter (fun h => ¬∃ z : Eisenstein, z^3 = h)) β u V A

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCubeTerm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal part of a square-divisor Poisson block, with
the square-divisor density kept explicitly. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCubePoissonContribution (d : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*
      ∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then
        mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h else 0
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorPoissonRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing by the effective frequency d*h for a square-divisor
Poisson block. The additive phase uses the actual inverse on the image. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def finiteDivisorPoissonContribution (d : Eisenstein) (S H : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*
      (mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor character can be absorbed into the original
coefficient. Its norm never increases, including at noncoprime inputs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorTwistedCoefficient (d : Eisenstein) (β : Eisenstein → ℂ)
    (a : Eisenstein) : ℂ := β a*star (cubicSymbol a (d^2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorNoncubeTotal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All effective noncube frequencies of each small square divisor.
The finite annuli and the infinite Fourier tail are both retained. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def divisorNoncubePoissonContribution (d : Eisenstein) (hd : d ≠ 0)
    (S : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' j : ℕ, finiteDivisorPoissonContribution d S
    ((divisorFrequencyDyad d hd j).filter (fun h => ¬∃ z : Eisenstein, z^3 = d*h)) β u V A

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCoprimePoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coprime component of the square-divisor variance, with its
literal lattice Poisson formula and its vanishing zero frequency. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCoprimeDispersionGram (d : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  coprimeDispersionGram S (divisorTwistedCoefficient d β) u W (A/(norm d)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonVarianceDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor variance as actual character mass, followed by
its canonical common-factor decomposition. This is the bridge to the
wide dual recurrence on shortened rows. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorGramCoefficient (d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ)
    (a : Eisenstein) : ℂ := star (dispersionAmplitude (divisorTwistedCoefficient d β) u a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeModelTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire large-height part of the undecomposed prime model is
negligible at the first-moment scale, with the actual finite windows. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def primeModelWindowSum (P : Finset Eisenstein) (c : Eisenstein → ℂ) (ℓ : ℤ)
    (H T₀ X₀ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (heightWindowCount H T₀),
    ∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
      heightFourierIntegral
        (fun t => cutoffHeightMultiplier H t*heightWindow (T₀*(3/2:ℝ)^j) t)
        (Real.log (norm p)-Real.log X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeHeightDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact low-height and dyadic-window decomposition of the sharp prime
comparison. The large-height model is controlled before any factorization
of the Gauss sum is used. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

def finiteHeightLow (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ p ∈ P, c p*heightFourierIntegral
    (fun t => cutoffHeightMultiplier H t*(heightPartitionBump (t/T):ℂ))
      (Real.log (norm p)-Real.log X₀)

def finiteHeightTail (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (heightWindowCount H T),
    ∑ p ∈ P, c p*heightFourierIntegral
      (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
        (Real.log (norm p)-Real.log X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin inversion of the actual character-twisted ideal von
Mangoldt sum, on its half-plane of absolute convergence. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def idealMangoldtSmooth (χ : EisensteinIdealExponent → ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' ν, (((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*W (idealExponentNorm ν/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormProfileOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed radial lift and trace Fourier transform form a continuous
linear operator. Thus the finite profile cost is controlled by finitely
many seminorms of the original one-dimensional cutoff. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap FourierTransform
namespace CubicFirstMoment
open CubicPoisson

def normProfileFourierCLM : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  (2/Real.sqrt 3:ℝ) •
    (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (Complex.conjCLE.trans (complexMulEquiv 2 (by norm_num)))).comp
      (SchwartzMap.fourierTransformCLM ℂ (V := ℂ) (E := ℂ))).comp
        normProfileLiftCLM).restrictScalars ℝ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtDyadic
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sharp dyadic ideal sums and the two endpoint errors of the
logarithmic smooth cutoff. All ideals, including those above three, remain. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealMangoldtDyadic (χ : EisensteinIdealExponent → ℂ) (X : ℝ) : ℂ :=
  ∑ ν ∈ fullIdealBall (2*X) with X ≤ idealExponentNorm ν,
    ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMangoldtPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete ideal von Mangoldt prefixes, exact half-open dyadic
increments, and the cost of their closed lower endpoints. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealMangoldtSum (χ : EisensteinIdealExponent → ℂ) (X : ℝ) : ℂ :=
  ∑ ν ∈ fullIdealBall X, ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealPrimePowerCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct count of higher prime-ideal powers in the complete norm ball.
The map from a prime base and its exponent is used only for an upper bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def higherIdealPrimePowers (X : ℝ) : Finset EisensteinIdealExponent :=
  (fullIdealBall X).filter (fun ν => ∃ p : EisensteinIdealPrime, ∃ j : ℕ,
    2 ≤ j ∧ ν = Finsupp.single p j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealPrimeReplacement
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of prime ideals from higher prime powers in the
actual von Mangoldt prefix. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealPrimeChebyshev (χ : EisensteinIdealExponent → ℂ) (X : ℝ) : ℂ :=
  ∑ ν ∈ fullIdealBall X with ∃ p : EisensteinIdealPrime, ν=Finsupp.single p 1,
    (Real.log (idealExponentNorm ν):ℂ)*χ ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealBall
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite norm ball of prime ideals and the exact reindexing of its
logarithmically weighted sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeIdealBall (X : ℝ) : Finset EisensteinIdealPrime :=
  (fullIdealBall X).biUnion Finsupp.support

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation of the principal ideal series from the actual principal
theta function, retaining its simple pole at one. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma principalThetaConstant_ne_zero : principalThetaConstant ≠ 0 :=
  inv_ne_zero residueTheta_unit_multiplicity_ne_zero

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticDecompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of the actual completion factor, including its contribution
to the residue. This is an internal analytic bridge: the completed
continuation must still be constructed from the Voronoi identity. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

def metaplecticCompletedResidue (r : Eisenstein) : ℂ :=
  (metaplecticA0*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimaryCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The expanded ideal kernel is exactly a primary cube-divisor sum.
This reindexing retains the finite norm cutoff and arbitrary complex
coefficients; no analytic summability assumption enters the inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryCubeFiber (F : ℝ) (b : Eisenstein) : Finset (Fin 2 → Eisenstein) :=
  (Fintype.piFinset (fun _ : Fin 2 => primaryElementBall F)).filter
    (fun n => n 0^3*n 1 = b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimaryInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact inverse completion at primary elements. The formal Euler
inverse is reindexed onto the literal primary cube-divisor fibers, with
its actual Möbius, angular and height weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrimeCompletionWeights (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    (p : EisensteinIdealPrime) : ℂ :=
  metaplecticCompletionWeight r ℓ t (primaryNormalize (idealPrimeRepresentative p))

def metaplecticGaussIdealSeries (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    ComplexIdealSeries := fun ν =>
      gauss (r*idealPrimaryGenerator ν)*theta ℓ (r*idealPrimaryGenerator ν)*
        mellinPhase t (idealExponentNorm ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticActualInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse completion for the original angular, norm-twisted
smooth Gauss sum. All cube-divisor sums are finite by the actual support
of the weight, and the rescaled completed length is retained literally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticAngularSmoothSum (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U t : ℝ) : ℂ :=
  ∑' u : PrimaryArgument,
    (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticTailCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal grouped coefficient in the long inverse-completion tail.
Its angular and coprimality phases are retained, while the remaining
Möbius divisor sum is bounded by a proved small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticTailPairs (F : ℝ) (e : Eisenstein) : Finset (Eisenstein × Eisenstein) :=
  ((primaryElementBall F).product (primaryElementBall F)).filter (fun cd => cd.1*cd.2 = e)

def metaplecticTailMoebius (C F : ℝ) (e : Eisenstein) : ℂ :=
  ∑ cd ∈ metaplecticTailPairs F e, if C < norm cd.1 then (idealMoebius cd.1:ℂ) else 0

def metaplecticTailCoefficient (r : Eisenstein) (ℓ : ℤ) (C F : ℝ) (e : Eisenstein) : ℂ :=
  ∑ cd ∈ metaplecticTailPairs F e, if C < norm cd.1 then
    (idealMoebius cd.1:ℂ)*metaplecticCompletionWeight r ℓ 0 cd.1*
      metaplecticCompletionWeight r ℓ 0 cd.2 else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse-completion sum, collected by e=cd.
The resulting weight is the proved tail coefficient, not an arbitrary
divisor-bounded replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticLongCompletion (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U C F : ℝ) : ℂ :=
  ∑ c ∈ primaryElementBall F, if C < norm c then
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
      metaplecticCompleted r ℓ W (U/norm c^3) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticShortInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short part of inverse completion. The same actual error sum
serves the radial and every fixed angular Type-I argument. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticShortCompletionError (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U C : ℝ) : ℂ :=
  ∑ c ∈ primaryElementBall C,
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
      (metaplecticCompleted r ℓ W (U/norm c^3)-metaplecticMain r ℓ W (U/norm c^3))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticLongDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual long inverse sum has a finite, canonical norm-dyad
partition. Each nonempty block lies above half the inverse cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticLongSupport (C F : ℝ) : Finset Eisenstein :=
  (((primaryElementBall F).product (primaryElementBall F)).image
    (fun cd => cd.1*cd.2)).filter (fun e => C < norm e)

def metaplecticLongDyad (C F : ℝ) (j : ℕ) : Finset Eisenstein :=
  (metaplecticLongSupport C F).filter (fun e => Nat.log 2 (normNat e) = j)

def metaplecticLongDyads (C F : ℝ) : Finset ℕ :=
  (metaplecticLongSupport C F).image (fun e => Nat.log 2 (normNat e))

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

def metaplecticTailScalar (ℓ : ℤ) (C F : ℝ) (e : Eisenstein) : ℂ :=
  (Real.sqrt (norm e):ℂ)*theta (3*ℓ) e*metaplecticTailMoebius C F e

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeILowHeightTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height Type-I estimate with its actual Mellin phase.
The original height-dependent squarefree model is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def lowTwistedTypeIRow (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (U t : ℝ) : ℂ :=
  metaplecticAngularSmoothSum r ℓ W U t-
    mellinPhase t U*angularSmoothModel r ℓ (fun x => W x*mellinPhase t x) U

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeILowIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the proved low Type-I estimate against the actual central
height weight. Outer-level and interval phases have modulus one. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def lowTypeIIntegral {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U H T X₀ : ℝ) : ℂ :=
  ∫ t : ℝ, lowHeightWeight H T t*
    (Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
      ∑ r ∈ S, (α r*normTwist t r)*lowTwistedTypeIRow r ℓ (W (w r)) U t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed-term weight from the corrected square. The factor
`(Na)^(-1/6)` is transferred to a fixed smooth test function and the
squarefree model is retained without removing mutual coprimality. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def typeIMixedGauss (r : Eisenstein) (W : ℝ → ℂ) (U : ℝ) : ℂ :=
  ∑' u : PrimaryArgument, gauss (r*u)*((norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U)

def typeIMixedModel (r : Eisenstein) (W : ℝ → ℂ) (U : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u then (idealMoebius (r*u):ℂ)^2*
    ((cStar*norm (r*u)^(-1/6:ℝ)*norm u^(-1/6:ℝ):ℝ):ℂ)*W (norm u/U) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductLow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low Type I for the actual product-norm envelope. Bounded dilation
supplies the selected inner weights; it is not an additional hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def productTypeILowIntegral {γ : Type*} (w : Eisenstein → γ)
    (P : Finset Eisenstein) (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ)
    (ℓ : ℤ) (B X U H T X₀ : ℝ) : ℂ :=
  ∫ t : ℝ, lowHeightWeight H T t*
    (Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
      ∑ r ∈ P, α r*∑ u ∈ primaryElementBall (B*U),
        theta ℓ (r*u)*centeredGauss (r*u)*normTwist t (r*u)*W (w r) (norm (r*u)/X))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove only the proved zero terms when the detector's finite
squarefree envelope is put into a Type-I row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def productCenteredKernel (ℓ : ℤ) (W : ℝ → ℂ) (X t : ℝ) (n : Eisenstein) : ℂ :=
  theta ℓ n*centeredGauss n*normTwist t n*W (norm n/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact sharp comparison through a smooth total-product weight.
The model tail and the endpoint error remain negligible uniformly in this
fixed weight, so the remaining integrals are precisely the detector kernels. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def primeProductGaussTail (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  finiteHeightTail (primeCutoff (4*X))
    (fun p => primeProductEnvelope (norm p/X)*theta ℓ p*gaussAtPrime p) H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute, uncollected complementary factorization mass used
after a free prime is cancelled. No cancellation inside beta is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairAbsolute (R D : Finset Eisenstein) (v f : Eisenstein → ℂ)
    (b : Eisenstein) : ℝ :=
  ∑ p ∈ primaryPairFiber R D b, ‖v p.1‖*‖f p.2‖


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected-bin free-prime row with its actual full product,
complementary exclusion and both stopping tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedSelectedPrimeRow (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c v e : Eisenstein) : ℂ :=
  ∑ p ∈ stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e,
    cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (r*(p*c))*cubicSymbol (r*(p*c)) v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedReindex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selected-divisor sum is exactly the finite collection
of free-prime rows. Its squarefree support, global largest-prime choice,
output interval, exclusion and stopping predicates are all retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def selectedStoppedDivisorSet (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r e : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall B).filter (fun d =>
    Squarefree (r*d) ∧ (primaryPrimeFactors d).Nonempty ∧ IsCoprime (r*d) e ∧
      (a < norm (r*d) ∧ norm (r*d) ≤ b) ∧ largestPrimeChoice (r*d) ∣ d ∧
      geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d)

def selectedStoppedRowPairs (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r e : Eisenstein) : Finset (Eisenstein × Eisenstein) :=
  ((primaryElementBall B) ×ˢ (primeCutoff B)).filter (fun t =>
    Squarefree (r*t.1) ∧ IsCoprime (r*t.1) e ∧
      t.2 ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*t.1)) (b/norm (r*t.1))
        j j₀ k h Z Q early r t.1 e)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished largest-prime role of literal stopped beta,
with the ordered-tuple factorial and original full-product twist. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDistinguishedTest (B ρ : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    largestPrimeChoice (r*d) ∣ r ∧ geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedBeta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selected-side prime cancellation applies to the literal
stoppedBeta coefficient, with its global-largest role selected exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedSelectedTest (B ρ : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    largestPrimeChoice (r*d) ∣ d ∧ geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargestRoles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact splitting of a valid largest-prime bin into its distinguished
and selected-divisor roles. The source stopping test is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedLargestBinTest (B ρ : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact long-bin decomposition of a stopped coefficient. The
complementary short-bin part is supported on genuinely smooth integers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedShortBinTest (B ρ y : ℝ) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice (r*d))) < y/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the literal distinguished stopped coefficient into
the prime rows whose cancellation has already been proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDistinguishedRows (B ρ a b w z u : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (W : ι → ℝ → ℂ) (D : Finset Eisenstein)
    (v e : Eisenstein) (i : ι) : ℂ :=
  ∑ t ∈ (coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D).filter
      (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ IsCoprime ((∏ l, t.1 l)*t.2) e),
    (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l)))*
    (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
        (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
      cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
        normTwist u (((∏ l, t.1 l)*p)*t.2)*cubicSymbol (((∏ l, t.1 l)*p)*t.2) v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLongBinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All long bins of the literal stopped coefficient have arbitrary
logarithmic saving. The number of bins is accounted for explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedCharacterSum (B w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) : ℂ :=
  ∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
      (primaryElementBall B),
    stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
        (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected n*
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMellinRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual coprime Poisson rows are the literal stopped rows at
the shifted norm heights. Divisibility filters and the original interval
support remain in the statement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDivisorMass (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H U : Finset Eisenstein) : ℝ :=
  ∑ d ∈ U.powerset, ∑ h ∈ H,
    ‖∑ n ∈ (stoppedIntervalSupport ι X a b e).filter (fun n => (∏ p ∈ d,p) ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n h‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact shortening for a divisor-restricted stopped row. The shortened
coefficient remains the original coefficient evaluated at d*n; no new
prime-factor independence is asserted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDivisorSlice (ι : Type*) [Fintype ι] [DecidableEq ι]
    (X l b : ℝ) (e d : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall (b/norm d)).filter
    (fun n => d*n ∈ stoppedIntervalSupport ι X l b e)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact divisor partition for a rough stopped coefficient. Every
nonempty row below the roughness cutoff and every row above the original
support length vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedDivisorRowMass (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H s : Finset Eisenstein) : ℝ :=
  ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
    (fun n => (∏ p ∈ s,p) ∣ n),
    stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree product coefficient of the literal stopped sides.
Its divisor bound is proved before collecting equal norms. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The true squarefree product support, without a coprimality replacement. -/
def squarefreePairSupport (P B : Finset Eisenstein) : Finset Eisenstein :=
  (primaryPairSupport P B).filter Squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the product squarefree model and its ordinary
height mean for the actual stopped outer coefficient. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeProductModel (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ B, if Squarefree (a*b) then
    α a*β b*normTwist u (a*b)*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingTwoStage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-stage stopping, first above a bin boundary and then after
failure of that high-prime stage. The original kernel and inverse
binomial coefficients remain unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def geometricStoppingLabel (ρ X R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) (q : ℕ × ℕ × ℕ) : ℂ :=
    ∑ t ∈ (primeBin (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t)
            (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
          (R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
              geometricBinLower ρ X q.1 < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t, p) *
            cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t, p)) *
          K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p)*
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p))
      else 0


def geometricHighStoppedElement (ρ X R Z : ℝ) (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) : ℂ :=
  ∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
    geometricStoppingLabel ρ X R Z ψ w K n q

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonHeightCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the normalized Gauss factor without changing coefficient energy.
This permits the proved dispersion estimate to act on the literal
common-factor rows, with their original height dependence. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def gramUntwist (v : Eisenstein → ℂ) (a : Eisenstein) : ℂ :=
  star (v a)*star (gauss a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBVarianceRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pure power saving for the original variance after subtraction
of its exact, height-independent zero-frequency model. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def varianceZeroMode (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ k ∈ commonRowFactors S, commonGramZeroMode S (fun b => star (β b)) V A k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogCellNearHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the actual near-boundary cell polynomials, preserving the
thin diagonal and the proved derivative cost in the dispersion remainder. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def logCellPolynomial (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B : ℝ) (e : ℤ × ℤ) (u : ℝ) : ℂ :=
  ∑ a ∈ logNormCellSupport P J A e.1, ∑ b ∈ logNormCellSupport S J B e.2,
    α a*β b*gauss (a*b)*normTwist u (a*b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarLogCellHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual far cells after height integration by parts. The
only loss in their diagonal mass is the proved number of populated cells. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

def logCellHeightSum (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (J A B X₀ : ℝ) (e : ℤ × ℤ) (h : ℝ → ℂ) : ℂ :=
  ∑ a ∈ logNormCellSupport P J A e.1, ∑ b ∈ logNormCellSupport S J B e.2,
    (α a*β b*gauss (a*b))*heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCutoffWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the low-height logarithmic estimate to the actual smooth
Fourier windows in the sharp prime interval decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def cutoffBilinearWindow (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
      (Real.log (norm (a*b))-Real.log X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BilinearHeightTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing all actual stopped bilinear height windows. One extra
logarithmic saving pays for the explicit finite window count. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cutoffBilinearTail (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (heightWindowCount H T),
    cutoffBilinearWindow P B α β H (T*(3/2:ℝ)^i) X₀

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianEnergy
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expansion and Schur bound for the actual Gaussian-weighted dual polynomial. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def huxleyDualPolynomial (P : Finset HuxleyLift) (v : HuxleyLift → ℂ) (n : ℤ × ℤ) : ℂ :=
  ∑ p ∈ P, v p*huxleyFrequencyPhase p.frequency (ofCoords n.1 n.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyResiduePoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal residue sums as a finite set of reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev huxleyResidueIndexFintype (Q : ℝ) : Fintype (HuxleyResidueIndex Q) := by
  let _ (q : {q : Eisenstein // q ∈ nonzeroNormBall Q}) : Fintype (Residues q.val) := huxleyResidueFintype q
  exact inferInstance

def huxleyIndexLift {Q : ℝ} (p : HuxleyResidueIndex Q) : HuxleyLift :=
  ⟨p.1.val,residueRepresentative p.1.val p.2,0⟩

def huxleyResiduePointSet (Q : ℝ) : Finset HuxleyLift := by
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  exact (Finset.univ.filter (fun p : HuxleyResidueIndex Q => IsUnit p.2)).image huxleyIndexLift

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealHeatTheta
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized theta series whose Mellin transform has the angular
Gamma shift. Its defining sum runs over all nonzero ideals. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

lemma idealHeatTheta_term_bound {A κ C t : ℝ} (hA : 0 < A) (ht : 0 < t)
    (hkernel : ∀ x : ℝ, 0 ≤ x → x^κ*Real.exp (-x) ≤ C*Real.exp (-x/2))
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (ν : EisensteinIdealExponent) :
    ‖χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)‖ ≤
      C*Real.exp (-idealExponentNorm ν*t/(2*A)) := by
  have hn := idealExponentNorm_pos ν
  have hx : 0 ≤ idealExponentNorm ν*t/A := by positivity
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx κ) (Real.exp_pos _).le)]
  calc
    _ ≤ (idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A) :=
      mul_le_of_le_one_left (by positivity) (hχ ν)
    _ = (idealExponentNorm ν*t/A)^κ*Real.exp (-(idealExponentNorm ν*t/A)) := by congr 2; ring
    _ ≤ C*Real.exp (-(idealExponentNorm ν*t/A)/2) := hkernel _ hx
    _ = _ := by congr 2; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIMixedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed number of relative norm dyads covers the full product support.
The number is independent of the product length. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def typeIMixedDyadIndex (L : ℝ) (r : Eisenstein) : ℕ :=
  if h : 1 ≤ norm r/L then Classical.choose (exists_nat_pow_near h (by norm_num : (1:ℝ) < 2)) else 0

def typeIMixedDyad (S : Finset Eisenstein) (L : ℝ) (j : ℕ) : Finset Eisenstein :=
  S.filter (fun r => typeIMixedDyadIndex L r = j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeBilinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual detector semiprime kernel has independent prime variables.
Its roughness factors can therefore be absorbed into the two coefficients
before applying the centered bilinear estimates. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def semiprimeRoughWeight (X : ℝ) (p : Eisenstein) : ℂ :=
  1-(primeDetectorCutoff (norm p/(X^(2/5:ℝ))):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleFullSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High boxes are literal full independent prime sums. The original
finite prime cutoff is removed only after the coordinate support bounds
show that all nonzero weights fit inside it. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleVector {i j : ℕ} (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    (Fin i ⊕ Fin j) → Eisenstein := Sum.elim q.1 q.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleKernelIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual regrouped kernel on the full Mellin line. No product
cutoff or Mellin-frequency remainder is discarded by these identities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev largeTupleSelectedCoefficient {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullPrimeCoefficient 2
    (fun a : s => largeTupleCoordinateWeight ξ X k a)
    (fun a : s => largeTupleNormScale k a)

abbrev largeTupleOtherCoefficient {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullPrimeCoefficient 2
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedModelCoprime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal Type-I product model becomes the factored squarefree
model after a proved rough-prime coprimality error. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def mixedMassModel (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  (cStar:ℂ)*∑ b ∈ S, β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)*
    coprimeSquarefreeModelMass b W A

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedNoStopCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Type-I collection for a no-stop branch with an additional
predicate on the distinguished and selected factors. In particular the
failed first-stage prefix is preserved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def restrictedNoStopCoefficient (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ X Z : ℝ) (P : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein) : ℂ :=
  stoppedBeta R D v ψ w (fun r m =>
    norm r*primeSurrogate (primaryPrimeFactors m)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z ∧ P r m) b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-line Mellin separation of the total-product envelope in a
finite height tail. No Mellin frequency is discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def envelopeCutoffBilinearTail (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (W : ℝ → ℂ) (H T X : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (heightWindowCount H T),
    ∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*W (norm (a*b)/X)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow (T*(3/2:ℝ)^j) t)
        (Real.log (norm (a*b))-Real.log X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite dyad is the analytic interval row, with the exact
selected-bin shift and failed-prefix predicate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedShiftedSideTest (ρ X : ℝ) (h : ℕ) (early : Bool)
    (q : ℕ × ℕ × ℕ) : Eisenstein → Eisenstein → Prop :=
  let Δ := geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X
  stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    (q.1-Δ) q.2.1 (h-Δ)
    (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeBlockEstimate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero semiprime piece has a logarithmically small centered
prime polynomial throughout the required fixed logarithmic height range.
The two coordinate orders are treated by their exact symmetry. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeBlockPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  let A := semiprimePartitionScale i
  let B := semiprimePartitionScale j
  let r := A/(X^(2/5:ℝ))
  let s := B/(X^(2/5:ℝ))
  ∑ p ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) (),
    ∑ q ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) (),
      semiprimeSmoothWeight r (norm p/A)*semiprimeSmoothWeight s (norm q/B)*
        centeredGauss (p*q)*normTwist u (p*q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeHeightBlock
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine semiprime Gauss polynomial has a uniform dyadic height
mean throughout the range used to truncate its Mellin transform. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeGaussPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  let A := semiprimePartitionScale i
  let B := semiprimePartitionScale j
  ∑ p ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight (A/X^(2/5:ℝ))) (fun _ => A) (),
    ∑ q ∈ fullPrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight (B/X^(2/5:ℝ))) (fun _ => B) (),
      semiprimeSmoothWeight (A/X^(2/5:ℝ)) (norm p/A)*
        semiprimeSmoothWeight (B/X^(2/5:ℝ)) (norm q/B)*gauss (p*q)*normTwist u (p*q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIHeightIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal Type-I height integral is bounded by the published-input
mean estimates, with the outer norm phase and interval endpoint retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def typeIHeightIntegral {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U H T X₀ : ℝ) : ℂ :=
  (T:ℂ)⁻¹*∫ t : ℝ,
    (localizedEndpointWeight H T t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      ∑ r ∈ S, (α r*normTwist t r)*metaplecticAngularSmoothSum r ℓ (W (w r)) U t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeICutoffWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cutoff window of the Type-I polynomial is the difference
of its two normalized endpoint integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def typeIHeightPolynomial {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U t : ℝ) : ℂ :=
  ∑ r ∈ S, (α r*normTwist t r)*metaplecticAngularSmoothSum r ℓ (W (w r)) U t

def typeICutoffWindow {γ : Type*} (w : Eisenstein → γ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ) (ℓ : ℤ) (U H T X₀ : ℝ) : ℂ :=
  ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
      Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*typeIHeightPolynomial w S α W ℓ U t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Type I for the actual Gauss product envelope at a height window.
The inner smooth weight is the bounded dilation forced by the outer norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def productTypeICutoffWindow {γ : Type*} (w : Eisenstein → γ)
    (P : Finset Eisenstein) (α : Eisenstein → ℂ) (W : γ → ℝ → ℂ)
    (ℓ : ℤ) (B X U H T X₀ : ℝ) : ℂ :=
  ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
      ∑ r ∈ P, α r*∑ u ∈ primaryElementBall (B*U),
        theta ℓ (r*u)*gauss (r*u)*normTwist t (r*u)*W (w r) (norm (r*u)/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSievePhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additive character that detects the primary cubic theta support.
It is computed from the actual lambda^-4 frequency lattice. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSievePhase (n : Eisenstein) : ℂ :=
  (Real.fourierChar (tracePair (cubicThetaFrequency n) omega):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSieveSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary coefficient selector of DR v3 (5.17)--(5.18). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- This is the source set S, written on the common numerator lattice. -/
lemma cubicThetaPrimarySupport_iff (n : Eisenstein) :
    cubicThetaPrimarySupport n ↔ ∃ c d : Eisenstein,
      primary c ∧ primary d ∧ Squarefree c ∧ n = lambdaE*c*d^3 := by
  constructor
  · rintro ⟨R,hk,hu⟩
    refine ⟨R.squarefreePart,R.cubePart,R.squarefree_primary,R.cube_primary,R.squarefree,?_⟩
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hk,hu,pow_one,one_mul]; ring
  · rintro ⟨c,d,hc,hd,hs,hn⟩
    let R : CubicThetaCoordinates n := {
      unit := 1
      order := 1
      squarefreePart := c
      cubePart := d
      squarefree_primary := hc
      cube_primary := hd
      squarefree := hs
      numerator_eq := by simpa [mul_assoc] using hn }
    exact ⟨R,rfl,rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable fundamental domain for the cubic-scale fractional-root cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeCubeRootCoverGroup_continuous {p : Eisenstein} (hp : primaryPrime p) :
    ContinuousConstSMul (cubicThetaPrimeCubeRootCoverGroup hp) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows at the translated inverted cusps used by the primary
coefficient projector. The phase is kept as the actual cubic symbol; its
ramified evaluation is a subsequent arithmetic step. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaShiftedInvertedTerm (b : Eisenstein) (r : CubicThetaInvertedRow)
    (p : ℂ×ℝ) (s : ℂ) : ℂ :=
  cubicSymbol (r.c+b*r.d) r.d*(r.height p:ℂ)^s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal primary-row unfolding at every translated inverted cusp.
Absolute convergence follows from equality of the actual row norms. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedGridTerm (b : Eisenstein) (cd : Eisenstein × Eisenstein)
    (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if cubicThetaInvertedAdmissible cd then
    cubicSymbol (cd.1+b*cd.2) cd.2*
      ((p.2/(Complex.normSq ((cd.1:ℂ)*p.1+cd.2)+norm cd.1*p.2^2):ℝ):ℂ)^s
  else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedGaussExplicit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit translated-cusp Gauss coefficients. The only new support
condition is the ramified congruence; the unramified factor is the same
primary Fourier coefficient already identified from the actual residue. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedFrequencyDirichlet (b : Eisenstein) (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' c : CubicThetaPrimaryPart, cubicThetaShiftedGaussCoefficient b c.val h*(norm c.val:ℂ)^(-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual continuous Fourier expansion at a translated cusp,
parametrized by its period-nine torus. All frequencies, including zero,
are retained until the explicit arithmetic support is applied. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaShiftedFourierTerm (b : Eisenstein) (v : ℝ) (s : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaShiftedFrequencyDirichlet b h s*
    ∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindowTest
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded Fourier tests on finite translated-cusp windows. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedFourierWeight (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (p : CubicThetaPoint) : ℂ :=
  W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaShiftedRowFrequency h)):ℂ)

lemma cubicThetaShiftedFourierWeight_continuous (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    Continuous (cubicThetaShiftedFourierWeight h W) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      Real.fourierChar (tracePair p.val.1 (cubicThetaShiftedRowFrequency h))) :=
    Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
  exact (W.continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
    (continuous_subtype_val.comp hc)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact initial Fourier observation on a finite translated-cusp window. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedWindowRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Icc a d,star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRadialMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire radial factors for the actual shifted frequency, including a
finite closed height window. The endpoint changes are null sets. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedPositiveRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (ε : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Ioi ε,star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t)/(v:ℂ)^3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedHorizontalContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual translated theta coefficient and its radial kernel. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

def cubicThetaShiftedPoleRadial (h : Eisenstein) (v : ℝ) : ℂ :=
  (v:ℂ)^(4/3:ℂ)*
    (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v (4/3) (cubicThetaShiftedRowHeatScale h) t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedModelSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolutely convergent arithmetic series determined by the proved
other-cusp coefficients. Its constant coefficient is explicitly zero. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaShiftedBareTerm (v : ℝ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAdaptedMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A principal-level decomposition evaluates the common multiplier for
cusp lifts with both diagonal entries zero modulo three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaRightInversion_matrix (g : SL(2,Eisenstein)) :
    (g*cubicThetaFullInversion⁻¹).val=!![-g 0 1,g 0 0;-g 1 1,g 1 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  change g.val*Matrix.adjugate !![(0:Eisenstein),-1;1,0]=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaRightInversion_mem (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    g*cubicThetaFullInversion⁻¹∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hb : primary (-g 0 1) := by
    change (3:Eisenstein)∣-g 0 1-1
    rw [show -g 0 1-1= -g 0 0*g 1 1+g 0 1*(g 1 0-1) by linear_combination hdet]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr ha) _)
      (dvd_mul_of_dvd_right hc _)
  rw [show (g*cubicThetaFullInversion⁻¹).val= _ from cubicThetaRightInversion_matrix g]
  exact ⟨hb,ha,dvd_neg.mpr hd,hc⟩

def cubicThetaRightInversionPrincipal (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) : cubicThetaPrincipalGroup :=
  ⟨g*cubicThetaFullInversion⁻¹,cubicThetaRightInversion_mem g hc ha hd⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique indexing of the primary theta frequencies by the original
squarefree and cube variables. There is no multiplicity factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryNumerator_support (cd : CubicThetaPrimaryPair) :
    cubicThetaPrimarySupport (cubicThetaPrimaryNumerator cd) := by
  rw [cubicThetaPrimarySupport_iff]
  exact ⟨cd.val.1,cd.val.2,cd.property.1,cd.property.2.1,cd.property.2.2,rfl⟩

lemma cubicThetaPrimaryNumerator_injective : Function.Injective cubicThetaPrimaryNumerator := by
  intro cd ef he
  have hp : cd.val.1*cd.val.2^3 = ef.val.1*ef.val.2^3 := by
    apply mul_left_cancel₀ lambdaE_prime.ne_zero
    simpa only [cubicThetaPrimaryNumerator,mul_assoc] using he
  have hu := primary_squarefree_cube_unique cd.property.1 cd.property.2.1 ef.property.1
    ef.property.2.1 cd.property.2.2 ef.property.2.2 hp
  exact Subtype.ext (Prod.ext hu.1 hu.2)

def cubicThetaPrimaryIndexEquiv : CubicThetaPrimaryPair ≃ {n // cubicThetaPrimarySupport n} :=
  Equiv.ofBijective (fun cd => ⟨cubicThetaPrimaryNumerator cd,cubicThetaPrimaryNumerator_support cd⟩)
    ⟨fun _ _ h => cubicThetaPrimaryNumerator_injective (congrArg Subtype.val h),by
      rintro ⟨n,hn⟩
      obtain ⟨c,d,hc,hd,hs,he⟩ := (cubicThetaPrimarySupport_iff n).mp hn
      exact ⟨⟨(c,d),hc,hd,hs⟩,Subtype.ext he.symm⟩⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCharacterAverage
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cubic-character average of the actual selected Gauss sum.
The zero extension removes every cube factor sharing a prime with the level. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimaryGaussSum (r u : Eisenstein) (ℓ : ℤ) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  ∑' cd : CubicThetaPrimaryPair,
    (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
      additivePhase r (cd.val.1*cd.val.2^3*u)*W (norm cd.val.1*norm cd.val.2^3/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInverseResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse residues arising from determinant-one cusp lifts permute
the actual unit group. No distribution or cancellation estimate is assumed. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaUnitRepresentative_coprime (r : Eisenstein) (u : (Residues r)ˣ) :
    IsCoprime r (residueRepresentative r u) := by
  apply isCoprime_of_residue_isUnit
  rw [residueRepresentative_spec]
  exact u.isUnit

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMass
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaRamifiedMass (σ : ℝ) (u : Eisensteinˣ) (k : ℕ) : ℝ :=
  (if k%3=0 ∧ 3 ≤ k then 1
   else if k%3=1 ∧ ((u:Eisenstein)=1 ∨ (u:Eisenstein)=-1) then 1 else 0) *
    3^(8-2*((k/3:ℕ):ℝ)-(k:ℝ)*σ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and factorization of the literal coefficient mass.
The unramified factors retain the primary and squarefree restrictions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimaryMass (t : ℝ) : ℝ :=
  ∑' d : PrimaryArgument, (norm d.val)^(-t)

def cubicThetaSquarefreeMass (t : ℝ) : ℝ :=
  ∑' c : CubicThetaSquarefreePrimary, (norm c.val)^(-t)

def cubicThetaMassPairEquiv : CubicThetaPrimaryPair ≃
    CubicThetaSquarefreePrimary × PrimaryArgument where
  toFun cd := (⟨cd.val.1,cd.property.1,cd.property.2.2⟩,⟨cd.val.2,cd.property.2.1⟩)
  invFun cd := ⟨(cd.1.val,cd.2.val),cd.1.property.1,cd.2.property,cd.1.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cubicThetaPairMassTerm (σ : ℝ) (cd : CubicThetaPrimaryPair) : ℝ :=
  (norm cd.val.1)^(-(1+σ)) * (norm cd.val.2)^(-(2+3*σ))

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

def cubicThetaScalarHeightMass (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaBottomRow,r.height p^s

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

def cubicThetaScalarHeightHigh (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaBottomRow,if 1 < r.height p then r.height p^s else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive full-group kernel majorizing the principal scalar kernel.
Its right action allows the estimate to be proved in one Siegel set. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimitiveKernel (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaPrimitiveRow,if r.height p ≤ 1 then r.height p^s else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveHeat
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive heat representation of the truncated primitive kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_4_rca7788_1 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance instCountableCubicThetaPrimitiveRow_rca7788_1 : Countable CubicThetaPrimitiveRow := by
  have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
    intro r s h
    exact CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  exact hi.countable
def cubicThetaPrimitiveHeatTerm (p : ℂ × ℝ) (t : ℝ) (r : CubicThetaPrimitiveRow) : ℝ :=
  if r.height p≤1 then Real.exp (-t/r.height p) else 0

def cubicThetaPrimitiveHeat (p : ℂ × ℝ) (t : ℝ) : ℝ :=
  ∑' r : CubicThetaPrimitiveRow,cubicThetaPrimitiveHeatTerm p t r

def cubicThetaPrimitiveHeatMellinTerm (p : ℂ × ℝ) (s : ℝ)
    (r : CubicThetaPrimitiveRow) (t : ℝ) : ℝ :=
  t^(s-1)*cubicThetaPrimitiveHeatTerm p t r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveZeroRows
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-first-coordinate rows are exactly the finitely many units.
Their cutoff heat contribution has uniform exponential decay. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaUnitRow (u : Eisensteinˣ) : CubicThetaZeroFirstRow :=
  ⟨⟨0,u,⟨0,(u⁻¹:Eisensteinˣ),by simp⟩⟩,rfl⟩

lemma cubicThetaUnitRow_injective : Function.Injective cubicThetaUnitRow := by
  intro u v h
  apply Units.ext
  exact congrArg (fun r : CubicThetaZeroFirstRow => r.val.d) h

lemma cubicThetaUnitRow_surjective : Function.Surjective cubicThetaUnitRow := by
  intro r
  have hu : IsUnit r.val.d := isCoprime_zero_left.mp (by simpa only [r.property] using r.val.coprime)
  obtain ⟨u,hu⟩ := hu
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply CubicThetaPrimitiveRow.ext
  · exact r.property.symm
  · exact hu

def cubicThetaZeroFirstRowEquiv : Eisensteinˣ ≃ CubicThetaZeroFirstRow :=
  Equiv.ofBijective cubicThetaUnitRow ⟨cubicThetaUnitRow_injective,cubicThetaUnitRow_surjective⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveHeatCusp
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform control of the actual truncated primitive heat kernel in a cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaNonzeroFirstPrimitiveRow_map (r : CubicThetaNonzeroFirstPrimitiveRow) :
    CubicThetaNonzeroRow := (⟨r.val.c,r.property⟩,r.val.d)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRawPairs
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Gauss average equals the manuscript's actual raw completed
sum. Nonsquarefree terms vanish by the proved finite Gauss-sum identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimaryPairEquiv : CubicThetaPrimaryPair ≃
    {du : PrimaryArgument × PrimaryArgument // Squarefree (du.2:Eisenstein)} where
  toFun cd := ⟨(⟨cd.val.2,cd.property.2.1⟩,⟨cd.val.1,cd.property.1⟩),cd.property.2.2⟩
  invFun du := ⟨(du.val.2.val,du.val.1.val),du.val.2.property,du.val.1.property,du.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

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

def cubicThetaPrimaryCoordinate (p : CubicThetaIntegerPoint) : Eisenstein :=
  ofCoords (1+3*p.1) (3*p.2)

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

def cubicThetaPositiveRemainderWeight : Eisenstein → ℝ :=
  cubicThetaMassPushforward (fun p => lambdaE*cubicThetaPrimaryCoordinate p)
    cubicThetaPrimaryDerivativeWeight

def cubicThetaNegativeRemainderWeight : Eisenstein → ℝ :=
  cubicThetaMassPushforward (fun p => -lambdaE*cubicThetaPrimaryCoordinate p)
    cubicThetaPrimaryDerivativeWeight

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSquareDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unique primary squarefree-times-square decomposition, used only
for the coefficient-energy Euler quotient. -/
noncomputable section
namespace CubicFirstMoment


def cubicThetaSquareNumerator (cd : CubicThetaPrimaryPair) : Eisenstein :=
  cd.val.1*cd.val.2^2

lemma cubicThetaSquareNumerator_primary (cd : CubicThetaPrimaryPair) :
    primary (cubicThetaSquareNumerator cd) := by
  exact primary_mul cd.property.1 (by
    simpa only [pow_two] using primary_mul cd.property.2.1 cd.property.2.1)

lemma cubicThetaSquareNumerator_injective : Function.Injective cubicThetaSquareNumerator := by
  intro cd ef he
  have hce := (idealExponentOf_squarefree_iff (primary_ne_zero cd.property.1)).mpr cd.property.2.2
  have hef := (idealExponentOf_squarefree_iff (primary_ne_zero ef.property.1)).mpr ef.property.2.2
  have hexp := congrArg idealExponentOf he
  change idealExponentOf (cd.val.1*cd.val.2^2)=idealExponentOf (ef.val.1*ef.val.2^2) at hexp
  rw [idealExponentOf_mul (primary_ne_zero cd.property.1) (pow_ne_zero 2 (primary_ne_zero cd.property.2.1)),
    idealExponentOf_mul (primary_ne_zero ef.property.1) (pow_ne_zero 2 (primary_ne_zero ef.property.2.1)),
    idealExponentOf_pow (primary_ne_zero cd.property.2.1),
    idealExponentOf_pow (primary_ne_zero ef.property.2.1)] at hexp
  have hp (p : EisensteinIdealPrime) :
      idealExponentOf cd.val.1 p=idealExponentOf ef.val.1 p ∧
      idealExponentOf cd.val.2 p=idealExponentOf ef.val.2 p := by
    have h := congrArg (fun ν : EisensteinIdealExponent => ν p) hexp
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at h
    have hc := hce p
    have hd := hef p
    omega
  apply Subtype.ext
  apply Prod.ext
  · apply primary_eq_of_idealExponentOf_eq cd.property.1 ef.property.1
    ext p
    exact (hp p).1
  · apply primary_eq_of_idealExponentOf_eq cd.property.2.1 ef.property.2.1
    ext p
    exact (hp p).2

lemma cubicThetaSquareNumerator_surjective (n : PrimaryArgument) :
    ∃ cd : CubicThetaPrimaryPair, cubicThetaSquareNumerator cd=n.val := by
  obtain ⟨d,c,he,hc⟩ := exists_sq_mul_squarefree n.val
  have hdc : d ∣ n.val := by rw [←he,pow_two,mul_assoc]; exact dvd_mul_right _ _
  have hcc : c ∣ n.val := by rw [←he]; exact dvd_mul_left _ _
  have hcp := primaryNormalize_primary (unit_residue_of_dvd_primary n.property hcc)
  have hdp := primaryNormalize_primary (unit_residue_of_dvd_primary n.property hdc)
  refine ⟨⟨(primaryNormalize c,primaryNormalize d),hcp,hdp,
    (primaryNormalize_associated c).squarefree_iff.mp hc⟩,?_⟩
  apply primary_associated_eq (primary_mul hcp (by simpa only [pow_two] using primary_mul hdp hdp))
    n.property
  change Associated (primaryNormalize c*primaryNormalize d^2) n.val
  rw [←he,mul_comm (d^2) c]
  exact ((primaryNormalize_associated c).mul_mul ((primaryNormalize_associated d).pow_pow)).symm

def cubicThetaSquareIndexEquiv : CubicThetaPrimaryPair ≃ PrimaryArgument :=
  Equiv.ofBijective (fun cd => ⟨cubicThetaSquareNumerator cd,cubicThetaSquareNumerator_primary cd⟩)
    ⟨fun _ _ h => cubicThetaSquareNumerator_injective (congrArg Subtype.val h),by
      intro n
      obtain ⟨cd,he⟩ := cubicThetaSquareNumerator_surjective n
      exact ⟨cd,Subtype.ext he⟩⟩

end CubicFirstMoment

end

end OAI
end


