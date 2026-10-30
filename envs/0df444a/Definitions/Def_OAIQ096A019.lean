-- Prove2me | Definitions.Def_OAIQ096A019
-- name    : OAIQ096A019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:52:01.309061+00:00
-- url     : https://prove2.me/theorems/98fbac8c-8139-4833-b9e3-368d8a5a60c0
-- title:
--   Definitions bundle OAIQ096A019 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 334 declarations of OpenAI's Lean: 132 definitions, 5 instances and 197 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaArithmeticModel`, `OAI.CubicFirstMoment.cubicThetaArithmeticModelRemainder`, `OAI.CubicFirstMoment.cubicThetaArithmeticModelTorus`, `OAI.CubicFirstMoment.cubicThetaBorelInversionFunction`, `OAI.CubicFirstMoment.cubicThetaBorelLift`, `OAI.CubicFirstMoment.cubicThetaBorelPhase`, `OAI.CubicFirstMoment.cubicThetaCoefficientMass`, `OAI.CubicFirstMoment.cubicThetaCoefficientMassTerm`, `OAI.CubicFirstMoment.cubicThetaCommonCuspCoefficient`, `OAI.CubicFirstMoment.cubicThetaCommonTau`, `OAI.CubicFirstMoment.cubicThetaCoreCoefficient`, `OAI.CubicFirstMoment.cubicThetaDenominatorTerm`, `OAI.CubicFirstMoment.cubicThetaDerivativeRemainder`, `OAI.CubicFirstMoment.cubicThetaDualMellinKernel`, `OAI.CubicFirstMoment.cubicThetaDualPrefactor`, `OAI.CubicFirstMoment.cubicThetaDualScale`, `OAI.CubicFirstMoment.cubicThetaEnergyMellinTerm`, `OAI.CubicFirstMoment.cubicThetaFourierEnergyHighMass`, `OAI.CubicFirstMoment.cubicThetaFourierEnergyLowMass`, `OAI.CubicFirstMoment.cubicThetaFourierStripSeed`, `OAI.CubicFirstMoment.cubicThetaFreeCubeEquiv`, `OAI.CubicFirstMoment.cubicThetaFreeLocalDualTerm`, `OAI.CubicFirstMoment.cubicThetaFullTorus`, `OAI.CubicFirstMoment.cubicThetaHighWindowL2`, `OAI.CubicFirstMoment.cubicThetaHighWindowTest`, `OAI.CubicFirstMoment.cubicThetaIncomingWindowTest`, `OAI.CubicFirstMoment.cubicThetaInvertedTorus`, `OAI.CubicFirstMoment.cubicThetaInvertedTorusRemainder`, `OAI.CubicFirstMoment.cubicThetaLocalDualTerm`, `OAI.CubicFirstMoment.cubicThetaNineConductorUnit`, `OAI.CubicFirstMoment.cubicThetaNineGaussMatrix`, `OAI.CubicFirstMoment.cubicThetaNineUnitInverse`, `OAI.CubicFirstMoment.cubicThetaNonzeroRowHeatTerm`, `OAI.CubicFirstMoment.cubicThetaPositiveFourierProfileL2`, `OAI.CubicFirstMoment.cubicThetaPositiveFourierProfileTest`, `OAI.CubicFirstMoment.cubicThetaPositiveStripFourierTest`, `OAI.CubicFirstMoment.cubicThetaPositiveStripHorizontalDensity`, `OAI.CubicFirstMoment.cubicThetaPrimeFreeDirichlet`, `OAI.CubicFirstMoment.cubicThetaPrimePowerTerm`, `OAI.CubicFirstMoment.cubicThetaPrimitiveRowEquiv` and 92 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Angular_AngularPrimeCoordinateCollection`, `CubicMoment_Angular_AngularPrimeProductCentered`, `CubicMoment_Angular_AngularPrimeProductPolynomialBounds`, `CubicMoment_Decomposition_DistinguishedScaleRows`, `CubicMoment_Decomposition_PrimeProductHeight`, `CubicMoment_Decomposition_PrimeProductPolynomialBounds`, `CubicMoment_Estimates_FullPrimeSlice`, `CubicMoment_Estimates_FullPrimeSliceMoments`, `CubicMoment_Estimates_IdealHeatCompletion`, `CubicMoment_Estimates_IdealHeatTheta`, `CubicMoment_Estimates_IdealThetaCompletion`, `CubicMoment_Estimates_LargeTupleExceptionalHigh`, `CubicMoment_Estimates_LargeTupleFullSupport`, `CubicMoment_Estimates_LargeTupleHighSum`, `CubicMoment_Estimates_LargeTupleKernelIntegral`, `CubicMoment_Estimates_LargeTupleKernelRegroup`, `CubicMoment_Estimates_LargeTupleOrdinarySum`, `CubicMoment_Estimates_LargeTupleResidualPartition`, `CubicMoment_Estimates_LargeTupleSelectedFlat`, `CubicMoment_Estimates_PrimeCoordinateErrors`, `CubicMoment_Estimates_PrimeCoprimeMass`, `CubicMoment_Estimates_PrimeIndicatorCollection`, `CubicMoment_Estimates_PrimeMomentCoefficient`, `CubicMoment_Estimates_PrimeTailWindow`, `CubicMoment_Estimates_RestrictedNoStopParameters`, `CubicMoment_Estimates_ScaleFirstArity`, `CubicMoment_Estimates_ScaleFirstHighSum`, `CubicMoment_Estimates_ScaleFirstMiddleSum`, `CubicMoment_Estimates_ScaleFirstNoStopTailNegligible`, `CubicMoment_Estimates_ScaleFirstOrdinaryStoppedTail`, `CubicMoment_Estimates_ScaleFirstOrdinaryTail`, `CubicMoment_Estimates_ScaleFirstReduction`, `CubicMoment_Estimates_ScaleFirstStoppedDyads`, `CubicMoment_Estimates_ScaleFirstStoppedReduction`, `CubicMoment_Estimates_ScaleFirstStoppedTailCoefficient`, `CubicMoment_Estimates_ScaleFirstStopping`, `CubicMoment_Estimates_ScaleFirstTailAggregation`, `CubicMoment_Estimates_ScaleFirstTailDecomposition`, `CubicMoment_Estimates_ScaleFirstTailDecompositionRows`, `CubicMoment_Estimates_SemiprimeGaussTail`, `CubicMoment_Estimates_SemiprimeGaussTailAngularAlgebra`, `CubicMoment_Estimates_SemiprimeGaussTailAngularHecke`, `CubicMoment_Estimates_SemiprimeGaussTailAngularMiddle`, `CubicMoment_Estimates_SemiprimeGaussTailAngularSplit`, `CubicMoment_Estimates_SemiprimeGaussTailPartition`, `CubicMoment_Estimates_SemiprimeGaussTailWeights`, `CubicMoment_Estimates_SemiprimePartition`, `CubicMoment_Estimates_SemiprimePolynomialBounds`, `CubicMoment_Estimates_SemiprimeSmoothed`, `CubicMoment_Estimates_ShortMoebiusFinite`, `CubicMoment_Estimates_SmallPrimeParts`, `CubicMoment_Estimates_StructuredFrequencyPolynomial`, `CubicMoment_Theta_CubicThetaArithmetic`, `CubicMoment_Theta_CubicThetaArithmeticModelL2`, `CubicMoment_Theta_CubicThetaArithmeticModelSection`, `CubicMoment_Theta_CubicThetaArithmeticModelTorus`, `CubicMoment_Theta_CubicThetaArithmeticRowSeries`, `CubicMoment_Theta_CubicThetaArithmeticTorus`, `CubicMoment_Theta_CubicThetaAveragedVoronoi`, `CubicMoment_Theta_CubicThetaBorelInversion`, `CubicMoment_Theta_CubicThetaBorelTransport`, `CubicMoment_Theta_CubicThetaCoefficientMass`, `CubicMoment_Theta_CubicThetaCommonCuspCoefficient`, `CubicMoment_Theta_CubicThetaConstantModeResidue`, `CubicMoment_Theta_CubicThetaCoreCoefficient`, `CubicMoment_Theta_CubicThetaCubeCancellation`, `CubicMoment_Theta_CubicThetaCuspCoefficients`, `CubicMoment_Theta_CubicThetaCuspWindowCore`, `CubicMoment_Theta_CubicThetaDerivativeRemainder`, `CubicMoment_Theta_CubicThetaDualMellinIntegral`, `CubicMoment_Theta_CubicThetaEnergyMellin`, `CubicMoment_Theta_CubicThetaFourierEnergyLowPole`, `CubicMoment_Theta_CubicThetaFourierStripSeed`, `CubicMoment_Theta_CubicThetaFourierStripSupport`, `CubicMoment_Theta_CubicThetaFreeCubeIndex`, `CubicMoment_Theta_CubicThetaFreeCubeParts`, `CubicMoment_Theta_CubicThetaFreeLocalVoronoi`, `CubicMoment_Theta_CubicThetaFrequencyTwist`, `CubicMoment_Theta_CubicThetaFullEisensteinFourier`, `CubicMoment_Theta_CubicThetaGaussFactor`, `CubicMoment_Theta_CubicThetaGaussParity`, `CubicMoment_Theta_CubicThetaHighWindowPairing`, `CubicMoment_Theta_CubicThetaHighWindowSeries`, `CubicMoment_Theta_CubicThetaHighWindowSmooth`, `CubicMoment_Theta_CubicThetaIncomingWindow`, `CubicMoment_Theta_CubicThetaInverseResidues`, `CubicMoment_Theta_CubicThetaInversionRestriction`, `CubicMoment_Theta_CubicThetaInvertedCoefficients`, `CubicMoment_Theta_CubicThetaInvertedDirichlet`, `CubicMoment_Theta_CubicThetaInvertedFourierObservable`, `CubicMoment_Theta_CubicThetaInvertedFrequencyBounds`, `CubicMoment_Theta_CubicThetaInvertedIncoming`, `CubicMoment_Theta_CubicThetaInvertedRowFourier`, `CubicMoment_Theta_CubicThetaInvertedRowMellin`, `CubicMoment_Theta_CubicThetaInvertedTorus`, `CubicMoment_Theta_CubicThetaLocalVoronoi`, `CubicMoment_Theta_CubicThetaMellinPowers`, `CubicMoment_Theta_CubicThetaNineCusp`, `CubicMoment_Theta_CubicThetaNonzeroRowHeat`, `CubicMoment_Theta_CubicThetaPoincareUnfolding`, `CubicMoment_Theta_CubicThetaPositiveCuspRestriction`, `CubicMoment_Theta_CubicThetaPositiveFourierProfile`, `CubicMoment_Theta_CubicThetaPositiveFourierSmooth`, `CubicMoment_Theta_CubicThetaPositiveHeightBand`, `CubicMoment_Theta_CubicThetaPositiveModelL2`, `CubicMoment_Theta_CubicThetaPositiveStripBound`, `CubicMoment_Theta_CubicThetaPositiveStripFourierSeparation`, `CubicMoment_Theta_CubicThetaPositiveStripFubini`, `CubicMoment_Theta_CubicThetaPositiveStripHorizontalDensity`, `CubicMoment_Theta_CubicThetaPositiveStripRepresentative`, `CubicMoment_Theta_CubicThetaPositiveZeroWindow`, `CubicMoment_Theta_CubicThetaPrimaryCoefficients`, `CubicMoment_Theta_CubicThetaPrimaryConstant`, `CubicMoment_Theta_CubicThetaPrimeCubeDirichlet`, `CubicMoment_Theta_CubicThetaPrimeCubeRootHorizontal`, `CubicMoment_Theta_CubicThetaPrimeCubeRows`, `CubicMoment_Theta_CubicThetaPrimeDirichlet`, `CubicMoment_Theta_CubicThetaPrimeEulerStep`, `CubicMoment_Theta_CubicThetaPrimeHeckeRelation`, `CubicMoment_Theta_CubicThetaPrimeLocalCases`, `CubicMoment_Theta_CubicThetaPrimePowerFourier`, `CubicMoment_Theta_CubicThetaPrimeRowRecurrence`, `CubicMoment_Theta_CubicThetaPrimeShiftRows`, `CubicMoment_Theta_CubicThetaPrimitiveRowFactorization`, `CubicMoment_Theta_CubicThetaProjectedAngularMellin`, `CubicMoment_Theta_CubicThetaProjectedDirichlet`, `CubicMoment_Theta_CubicThetaProjectedSmoothMellin`, `CubicMoment_Theta_CubicThetaRamifiedAllRows`, `CubicMoment_Theta_CubicThetaRamifiedContraction`, `CubicMoment_Theta_CubicThetaRamifiedDirichlet`, `CubicMoment_Theta_CubicThetaRamifiedDirichletCube`, `CubicMoment_Theta_CubicThetaRamifiedFinite`, `CubicMoment_Theta_CubicThetaRamifiedLowFactor`, `CubicMoment_Theta_CubicThetaRamifiedLowRow`, `CubicMoment_Theta_CubicThetaRamifiedMiddleSupport`, `CubicMoment_Theta_CubicThetaRamifiedMiddleValue`, `CubicMoment_Theta_CubicThetaRamifiedMissingClass`, `CubicMoment_Theta_CubicThetaRamifiedPhaseEigen`, `CubicMoment_Theta_CubicThetaRamifiedPhaseRows`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryFactor`, `CubicMoment_Theta_CubicThetaRamifiedPrimarySeries`, `CubicMoment_Theta_CubicThetaRamifiedPrimarySupport`, `CubicMoment_Theta_CubicThetaRamifiedResidueFormula`, `CubicMoment_Theta_CubicThetaRamifiedResidueSystem`, `CubicMoment_Theta_CubicThetaRamifiedRowInflation`, `CubicMoment_Theta_CubicThetaRamifiedRowValue`, `CubicMoment_Theta_CubicThetaRamifiedTopPhase`, `CubicMoment_Theta_CubicThetaRamifiedTopRow`, `CubicMoment_Theta_CubicThetaRamifiedUnitConductor`, `CubicMoment_Theta_CubicThetaRamifiedUnitCube`, `CubicMoment_Theta_CubicThetaRamifiedUnitInflation`, `CubicMoment_Theta_CubicThetaRamifiedUnitOperator`, `CubicMoment_Theta_CubicThetaRegularHeatLow`, `CubicMoment_Theta_CubicThetaRegularHeatPole`, `CubicMoment_Theta_CubicThetaRemainderWeights`, `CubicMoment_Theta_CubicThetaResidueCusps`, `CubicMoment_Theta_CubicThetaResidueVanishing`, `CubicMoment_Theta_CubicThetaRowFiniteFourier`, `CubicMoment_Theta_CubicThetaScalarHeightSeed`, `CubicMoment_Theta_CubicThetaScalarSeedPairing`, `CubicMoment_Theta_CubicThetaSelectedAngularMellin`, `CubicMoment_Theta_CubicThetaSelectedGaussSum`, `CubicMoment_Theta_CubicThetaShiftedFullObservation`, `CubicMoment_Theta_CubicThetaShiftedPeriodMeasure`, `CubicMoment_Theta_CubicThetaShiftedTorus`, `CubicMoment_Theta_CubicThetaShiftedWindow`, `CubicMoment_Theta_CubicThetaTorusCellTransport`, `CubicMoment_Theta_CubicThetaTorusModes`, `CubicMoment_Theta_CubicThetaWeightFactor`, `CubicMoment_Theta_CubicThetaWindowWeak`, `CubicMoment_Transform_MetaplecticSupportedSum`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A011`, `OAIQ096A012`, `OAIQ096A013`, `OAIQ096A014` and `OAIQ096A015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A022` and `OAIQ096A023`; the statements `OAI.CubicFirstMoment.angular_balanced_common_squarefree_exponents`, `OAI.CubicFirstMoment.angular_distinguishedStoppedEnvelopeTail_bound`, `OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual`, `OAI.CubicFirstMoment.angular_large_tuple_triple_transition_smoothed`, `OAI.CubicFirstMoment.angular_primeProductLowHeight_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.angular_tailPrime_hecke_group`, `OAI.CubicFirstMoment.angular_tailPrime_hecke_window`, `OAI.CubicFirstMoment.angular_tailPrime_middle_group`, `OAI.CubicFirstMoment.angular_tailPrime_ordinary_group_prefix`, `OAI.CubicFirstMoment.angular_tailPrime_upper_group_bound_uniform`, `OAI.CubicFirstMoment.centralRoughProduct_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi`, `OAI.CubicFirstMoment.cubicThetaResidue_voronoi`, `OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean`, `OAI.CubicFirstMoment.cubicTheta_completed_tail_mean`, `OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO`, `OAI.CubicFirstMoment.distinguishedStoppedEnvelopeTail_bound`, `OAI.CubicFirstMoment.first_primeCoordinateError_moment`, `OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleSelectedFlatHighSum_isLittleO`, `OAI.CubicFirstMoment.primeProductLowHeight_angular_isLittleO_actual`, `OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual`, `OAI.CubicFirstMoment.primeProductLowHeight_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO`, `OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO`, `OAI.CubicFirstMoment.semiprimeGaussTail_angular_hecke_window`, `OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving`, `OAI.CubicFirstMoment.semiprime_block_log_saving_actual`, `OAI.CubicFirstMoment.semiprime_gauss_height_log_saving`, `OAI.CubicFirstMoment.tailPrime_low_group`, `OAI.CubicFirstMoment.tailPrime_middle_group`, `OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform` and `OAI.CubicFirstMoment.two_prime_transition_height`; the proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power`, `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_angular_mean`, `OAI.CubicFirstMoment.angular_balanced_common_squarefree_exponents`, `OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood`, `OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_distinguishedStoppedEnvelopeTail_bound`, `OAI.CubicFirstMoment.angular_divisor_noncube_total_saving`, `OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood`, `OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual`, `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving`, `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual`, `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual`, `OAI.CubicFirstMoment.angular_noncube_poisson_total_saving`, `OAI.CubicFirstMoment.angular_primeProductLowHeight_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail_isLittleO_proved`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryNoStopTail_isLittleO_proved`, `OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual`, `OAI.CubicFirstMoment.angular_tailPrime_middle_group`, `OAI.CubicFirstMoment.angular_tailPrime_ordinary_group_prefix`, `OAI.CubicFirstMoment.angular_tailPrime_upper_group_bound_uniform`, `OAI.CubicFirstMoment.angular_upperNoStopTail_isLittleO_proved`, `OAI.CubicFirstMoment.balanced_common_normalized_exponents`, `OAI.CubicFirstMoment.centralRoughProduct_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.coprime_noncube_mellin_integral_saving`, `OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg`, `OAI.CubicFirstMoment.cubicTheta_completed_negative_tail_mean`, `OAI.CubicFirstMoment.cubicTheta_completed_tail_mean`, `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_radial_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryLowTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_radial_upperNoStopTail_isLittleO`, `OAI.CubicFirstMoment.distinguishedStoppedEnvelopeTail_bound`, `OAI.CubicFirstMoment.divisor_noncube_total_saving`, `OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood`, `OAI.CubicFirstMoment.first_common_prime_exponents`, `OAI.CubicFirstMoment.first_primeCoordinateError_moment`, `OAI.CubicFirstMoment.first_weighted_tuple_neighborhood`, `OAI.CubicFirstMoment.full_prime_centered_product_bilinear_actual`, `OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound`, `OAI.CubicFirstMoment.full_smooth_twisted_primitive_cubic_bound`, `OAI.CubicFirstMoment.height_radial_form_saving`, `OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleSelectedFlatHighSum_isLittleO`, `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.noncube_poisson_total_saving`, `OAI.CubicFirstMoment.patterson_angularCancellation`, `OAI.CubicFirstMoment.patterson_angularComparison`, `OAI.CubicFirstMoment.primeProductLowHeight_angular_isLittleO_actual`, `OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual`, `OAI.CubicFirstMoment.primeProductLowHeight_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO`, `OAI.CubicFirstMoment.semiprimeGaussTailAngular_isLittleO`, `OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving`, `OAI.CubicFirstMoment.semiprime_block_log_saving_actual`, `OAI.CubicFirstMoment.short_outer_low_bound_actual`, `OAI.CubicFirstMoment.stopped_typeI_mixed_actual`, `OAI.CubicFirstMoment.tailPrime_low_group`, `OAI.CubicFirstMoment.tailPrime_middle_group` and `OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A012
import Definitions.Def_OAIQ096A013
import Definitions.Def_OAIQ096A014
import Definitions.Def_OAIQ096A015

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentOf_primaryGenerator (ν : EisensteinIdealExponent) :
    idealExponentOf (idealPrimaryGenerator ν) = ν := by
  have h := primaryNormalize_associated (idealExponentGenerator ν)
  have hne := h.ne_zero_iff.mp (idealExponentGenerator_ne_zero ν)
  exact (idealExponentOf_eq_of_associated hne (idealExponentGenerator_ne_zero ν) h.symm).trans
    (idealExponentOf_generator ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPrimeParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primaryOutsidePart_coprime {a v : Eisenstein} (ha : primary a) (hv : v ≠ 0) :
    IsCoprime (primaryOutsidePart v a) v := by
  rw [isCoprime_iff_idealExponent_disjoint
    (primary_ne_zero (primaryOutsidePart_primary v ha)) hv]
  change ∀ p, idealExponentOf (idealPrimaryGenerator (outsideIdealPart v (idealExponentOf a))) p = 0 ∨
    idealExponentOf v p = 0
  rw [idealExponentOf_primaryGenerator]
  intro p
  by_cases hp : p ∈ (idealExponentOf v).support
  · left
    have hne := Finsupp.mem_support_iff.mp hp
    simp [outsideIdealPart,hne]
  · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the indicator convolution to genuine primary primes,
followed by the exact squarefree discrepancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primarySquarefreePrimeTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
    squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*V (norm z/Y))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of angular coordinate tuples. The same fixed theta
factor occurs on each original coordinate and hence on their product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularSquarefreePrimeTuple (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
    squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*theta ℓ z*V (norm z/Y))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMomentCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the structured moment with the original
squarefree ordered-prime coefficient, including numerator and exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeMomentCoefficient (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) (z : Eisenstein) : ℂ :=
  squarefreeConvolution (coordinatePrimeSupport W X Y) (fun i n => W i (norm n/X i)) z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quotient support for divisor-restricted prime coefficients.
No independent-prime condition is asserted for the shortened coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeSliceSupport (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall (R^Fintype.card ι*(∏ i, X i)/norm f)).filter
    (fun n => f*n ∈ fullSquarefreePrimeSupport R W X e)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height-independent bounds for the actual two full prime convolutions.
These are used only beyond the power range of the published height mean. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def fullPrimeProductGauss (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
    ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
      fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
        gauss (a*b)*normTwist u (a*b)

def fullPrimeProductModel (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
    ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
      fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
        ((cStar:ℂ)*(idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ))*
          normTwist u (a*b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeProductPolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular Gauss product and its coefficient-mass bound. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def fullAngularPrimeProductGauss (ℓ : ℤ) (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) : ℂ :=
  productGaussPolynomial (fullSquarefreePrimeSupport R WA XA 1)
    (fullSquarefreePrimeSupport R WB XB 1)
    (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) ℓ u


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeProductCentered
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def fullAngularPrimeProductModel (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
    ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
      fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
        theta ℓ (a*b)*((cStar:ℂ)*(idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ))*
          normTwist u (a*b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSupportedSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported primary factors in the retained metaplectic sum have
convergent weighted Euler products with arbitrarily small level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponent_support_of_dvd_power {b r : Eisenstein}
    (hb : b ≠ 0) (hr : r ≠ 0) (hd : ∃ k : ℕ, b ∣ r^k) :
    (idealExponentOf b).support ⊆ (idealExponentOf r).support := by
  obtain ⟨k,hk⟩ := hd
  have hle := idealExponentOf_le_of_dvd hb (pow_ne_zero k hr) hk
  rw [idealExponentOf_pow hr k] at hle
  intro p hp
  by_contra hpr
  have hz := Finsupp.notMem_support_iff.mp hpr
  have he := hle p
  simp only [Finsupp.coe_smul,Pi.smul_apply,hz,smul_zero] at he
  exact (Finsupp.mem_support_iff.mp hp) (Nat.eq_zero_of_le_zero he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredFrequencyPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def structuredFrequencyCoefficient (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (z : Eisenstein) : ℂ :=
  if IsCoprime z e then
    primeMomentCoefficient W X Z z*mellinPhase u (norm z)*cubicSymbol z v else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-indicator replacement errors in the two exceptional regions. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeCoordinateError (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinateProductCutoff W X Y,
    primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*V (norm z/Y))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeSliceMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shortened energies and all three sieve orientations for the literal
quotient coefficients β(fn). These are used for common-factor tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeSliceSum (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e h v : Eisenstein) (ℓ : ℤ) (u : ℝ) : ℂ :=
  ∑ n ∈ fullPrimeSliceSupport R W X f e,
    fullPrimeCoefficient R W X (f*n)*theta ℓ n*mellinPhase u (norm n)*cubicSymbol n (v*h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoprimeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact common-divisor mass for full prime rows. Roughness leaves
only the empty divisor below a chosen threshold; every remaining term
has a genuinely large common divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeDivisorMellinMass (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u N : ℝ) (f : Eisenstein) (t : ℝ) : ℝ :=
  ((∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖^2)+
   (∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖^2))/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
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

def primeProductLowHeight (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), centeredHeightKernel ℓ primeProductEnvelope H T X X p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite smooth partition of the original semiprime kernel. Every
prime coordinate retains both its roughness weight and the total-product
cutoff; the displayed number of pieces is the actual finite partition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def semiprimePartitionPiece (ℓ : ℤ) (H T X : ℝ) (i j : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
    semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
      centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedScaleRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale-first decomposition of the central rough product. The
threshold applies to independent distinguished-prime scales, before
expanding the rough remainder. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleRow (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ) *
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

def distinguishedLowScaleRows (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      distinguishedScaleRow i ℓ ξ Ct H X k else 0

def distinguishedHighScaleRows (i : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ distinguishedScaleLength k then
      distinguishedScaleRow i ℓ ξ Ct H X k else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealHeatTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealHeatTheta_summable {A κ t : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (ht : 0 < t)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    Summable (fun ν => χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)) := by
  obtain ⟨C,hC,hkernel⟩ := rpow_exp_half_bound hκ
  have hs := (summable_ideal_exponential (show 0 < t/(2*A) by positivity)).mul_left C
  apply hs.of_norm_bounded
  intro ν
  convert idealHeatTheta_term_bound hA ht hkernel χ hχ ν using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

lemma idealHeatTheta_continuousOn_ray {A κ δ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealHeatTheta A κ χ) (Set.Ici δ) := by
  obtain ⟨C,hC,hkernel⟩ := rpow_exp_half_bound hκ
  have hc (ν : EisensteinIdealExponent) : Continuous (fun t : ℝ =>
      (idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A)) :=
    (((continuous_const.mul continuous_id).div_const A).rpow_const (fun _ => Or.inr hκ)).mul
      (by fun_prop)
  apply continuousOn_tsum (fun ν =>
    (continuous_const.mul (Complex.continuous_ofReal.comp (hc ν))).continuousOn)
    ((summable_ideal_exponential (show 0 < δ/(2*A) by positivity)).mul_left C)
  intro ν t ht
  have ht0 : 0 < t := lt_of_lt_of_le hδ ht
  apply (idealHeatTheta_term_bound hA ht0 hkernel χ hχ ν).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply Real.exp_le_exp.mpr
  have hn := idealExponentNorm_pos ν
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ idealExponentNorm ν/(2*A) by positivity)
  first | (convert neg_le_neg hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((neg_le_neg hm).trans (le_of_eq (by ring)))

lemma idealHeatTheta_continuousOn {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealHeatTheta A κ χ) (Set.Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hr := idealHeatTheta_continuousOn_ray hA hκ (show 0 < t/2 by exact half_pos ht) χ hχ
  exact (hr.continuousAt (Ici_mem_nhds (show t/2 < t by linarith))).continuousWithinAt

lemma idealHeatTheta_norm_bound {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖idealHeatTheta A κ χ t‖ ≤ C*Real.exp (-t/(4*A)) := by
  obtain ⟨C,hC,hkernel⟩ := rpow_exp_half_bound hκ
  let D := ∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(4*A))
  have hD : 0 ≤ D := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨C*D,by positivity,?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hs := idealHeatTheta_summable hA hκ ht0 χ hχ
  have he := (summable_ideal_exponential (show 0 < 1/(4*A) by positivity)).mul_left C
  have hg : Summable (fun ν : EisensteinIdealExponent =>
      C*Real.exp (-idealExponentNorm ν/(4*A))*Real.exp (-t/(4*A))) := by
    convert he.mul_right (Real.exp (-t/(4*A))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    congr 3
    ring
  calc
    _ ≤ ∑' ν, ‖χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ν : EisensteinIdealExponent,
        C*Real.exp (-idealExponentNorm ν/(4*A))*Real.exp (-t/(4*A)) := by
      apply hs.norm.tsum_le_tsum _ hg
      intro ν
      apply (idealHeatTheta_term_bound hA ht0 hkernel χ hχ ν).trans
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn := idealExponentNorm_ge_one ν
      have hp := mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr ht)
      have hh : -2*(idealExponentNorm ν*t) ≤ -idealExponentNorm ν-t := by nlinarith
      convert div_le_div_of_nonneg_right hh (show 0 ≤ 4*A by positivity) using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp <;> ring)
    _ = _ := by rw [tsum_mul_right,tsum_mul_left]

lemma idealHeatTheta_isBigO_rpow {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (r : ℝ) :
    idealHeatTheta A κ χ =O[atTop] (fun t : ℝ => t^r) := by
  obtain ⟨C,hC,hbound⟩ := idealHeatTheta_norm_bound hA hκ χ hχ
  have he : idealHeatTheta A κ χ =O[atTop] (fun t : ℝ => Real.exp (-(1/(4*A))*t)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have hx : -(1/(4*A))*t = -t/(4*A) := by ring
    simpa only [hx,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hbound t ht
  exact he.trans (isLittleO_exp_neg_mul_rpow_atTop (show 0 < 1/(4*A) by positivity) r).isBigO

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic continuation from the exact ideal theta transformation. The
hypotheses concern the theta series itself and follow from the
finite-character Poisson formula. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

def idealThetaFEPair {A : ℝ} (hA : 0 < A)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta A χ (1/t) = ε*(t:ℂ)*idealTheta A χdual t) : WeakFEPair ℂ where
  f := idealTheta A χ
  g := idealTheta A χdual
  k := 1
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (idealTheta_continuousOn hA χ hχ).locallyIntegrableOn measurableSet_Ioi
  hg_int := (idealTheta_continuousOn hA χdual hχdual).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  hf_top r := by simpa only [sub_zero] using idealTheta_isBigO_rpow hA χ hχ r
  hg_top r := by simpa only [sub_zero] using idealTheta_isBigO_rpow hA χdual hχdual r
  h_feq t ht := by simpa only [Real.rpow_one,smul_eq_mul] using hFE t ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealHeatCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire angular Hecke completion from the actual normalized heat
transformation. No continuation or finite-order assumption is used here. -/
noncomputable section
open Filter Asymptotics MeasureTheory
namespace CubicFirstMoment

def idealHeatFEPair {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {ε : ℂ} (hε : ε ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealHeatTheta A κ χ (1/t) = ε*(t:ℂ)*idealHeatTheta A κ χdual t) : WeakFEPair ℂ where
  f := idealHeatTheta A κ χ
  g := idealHeatTheta A κ χdual
  k := 1
  ε := ε
  f₀ := 0
  g₀ := 0
  hf_int := (idealHeatTheta_continuousOn hA hκ χ hχ).locallyIntegrableOn measurableSet_Ioi
  hg_int := (idealHeatTheta_continuousOn hA hκ χdual hχdual).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  hf_top r := by simpa only [sub_zero] using idealHeatTheta_isBigO_rpow hA hκ χ hχ r
  hg_top r := by simpa only [sub_zero] using idealHeatTheta_isBigO_rpow hA hκ χdual hχdual r
  h_feq t ht := by simpa only [Real.rpow_one,smul_eq_mul] using hFE t ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleFullSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
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

def largeTupleIndependentSum (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) : ℂ :=
  ∑ f ∈ Fintype.piFinset (fullPrimeSupport 2 (largeTupleCoordinateWeight ξ X k)
      (largeTupleNormScale k)),
    (∏ a, largeTupleCoordinateWeight ξ X k a (norm (f a)/largeTupleNormScale k a))*
      centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (∏ a, f a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleKernelRegroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of the actual high-box kernel. Squarefreeness is
retained through the centered kernel and full prime convolutions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleRegroupedKernel (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) : ℂ :=
  ∑ b ∈ fullSquarefreePrimeSupport 2
      (fun a : s => largeTupleCoordinateWeight ξ X k a)
      (fun a : s => largeTupleNormScale k a) 1,
    ∑ a ∈ fullSquarefreePrimeSupport 2
        (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
        (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a) 1,
      fullPrimeCoefficient 2 (fun a : s => largeTupleCoordinateWeight ξ X k a)
          (fun a : s => largeTupleNormScale k a) b*
        fullPrimeCoefficient 2
          (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
          (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a) a*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (b*a)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleKernelIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
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

abbrev largeTupleSelectedSupport {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullSquarefreePrimeSupport 2
    (fun a : s => largeTupleCoordinateWeight ξ X k a)
    (fun a : s => largeTupleNormScale k a) 1

abbrev largeTupleOtherSupport {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :=
  fullSquarefreePrimeSupport 2
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleCoordinateWeight ξ X k a)
    (fun a : {a : Fin i ⊕ Fin j // a ∉ s} => largeTupleNormScale k a) 1

def largeTupleSmoothedPolynomial {i j : ℕ} (ℓ : ℤ) (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) (u : ℝ) : ℂ :=
  centeredProductSmoothed (largeTupleSelectedSupport ξ X k s)
    (largeTupleOtherSupport ξ X k s) (largeTupleSelectedCoefficient ξ X k s)
    (largeTupleOtherCoefficient ξ X k s) ℓ primeProductEnvelope X u


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleOrdinarySum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual high ordinary norm boxes, summed over the finite smooth
partition. The exceptional and cutoff boundary boxes remain separate. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleOrdinaryHighSum (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      (∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleResidualPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An exact partition of the remaining large tuples. A boundary box
retains its sharp distinguished-product cutoff; an exceptional high box
has no surviving ordinary tuple. No contribution is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleExceptionalHighSum (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      ¬(∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleSelectedFlat
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any selected subfamily of actual high flat boxes has the same
negligible bound. This will select the exceptional contribution exactly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleSelectedFlatHighSum (i j : ℕ) (ξ : ℝ) (Ct G : ℕ) (H X : ℝ)
    (select : ((Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) → Prop) : ℂ :=
  ∑ d ∈ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X,
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧ select d then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleExceptionalHigh
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining high exceptional boxes split exactly into the flat
subfamily and its complement. Both are negligible on the stated scale. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleExceptionalSelector (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : Prop :=
  ¬∃ q ∈ largePrimeTupleBox i j X,
    largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
      ¬largePrimeTupleExceptional δ q

def largePrimeTupleExceptionalNonflatSum (i j : ℕ) (ξ δ : ℝ) (Ct G : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if (X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleExceptionalSelector i j ξ δ Ct H X d) ∧
      d ∉ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleHighSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All high boxes of each actual large-row arity are negligible. The
separate sharp-cutoff boundary contribution is retained explicitly. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Fourier height window is bounded by its two-sided mean,
including the reciprocal height normalization and both endpoint phases. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def productGaussWindow (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (H U X : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ S, α a*β b*productGaussHeightWindowKernel ℓ W H U X X (a*b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedNoStopParameters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power saving for the literal no-stop term with the
first-stage predicate retained, including a growing finite norm partition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleNoStop (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (P : Eisenstein → Eisenstein → Prop) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      restrictedNoStopCenteredValue (centralPrimaryFactors X)
        (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
        (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) 0 primeProductEnvelope
        H ((1+Real.log X)^Ct) X X P else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstArity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expand the rough remainder only after fixing the distinguished
smooth scales. All tuple and product supports remain exact. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleDoubleRow (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X k r *
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      roughTupleCoefficient j (Real.exp primeProductWeights.radius*X)
        primeDetectorCutoff (X^ξ) u *
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstMiddleSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scale-first middle boxes, summed with their original independent
prime weights and complete product kernels. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstMiddleSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleDistinguishedScale (fun a => (d a).val) < X^(38/100:ℝ) then
      scaleFirstPrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstHighSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete manuscript high-scale branch is negligible. The new
middle interval is treated by its distinguished group; the higher
interval is exactly the already proved large-row high sum. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      scaleFirstPrimeTuplePiece i j 0 ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStopping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual low scale-first rows satisfy the two-stage stopping
identity. The no-stop prefix test and both independent stopped matrices
are retained exactly. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleStoppedRow (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  let F := Real.exp primeProductWeights.radius*X
  let I := if early then (stoppingLabelBox ρ F).filter (fun q => q.1 < h)
    else stoppingLabelBox ρ F
  ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
    ∑ a ∈ primaryPairSupport (primaryElementBall F) (primaryElementBall F),
      ∑ b ∈ primaryPairSupport (centralPrimaryFactors X) (primaryElementBall F),
        stoppedAlpha (primaryElementBall F) (primaryElementBall F) primeDetectorCutoff (X^ξ)
            (stoppingRemainingTest (geometricPrimeBin ρ F) q.1 q.2.2) a *
          stoppedBeta (centralPrimaryFactors X) (primaryElementBall F)
            (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ)
            (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
              q.1 q.2.1 h (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early) b *
          (if a*b ∈ centralProductEnvelope X then
            centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

def distinguishedScaleStopped (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      distinguishedScaleStoppedRow i ρ ξ Ct H X h early k else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact dyadic form of each original stopped row. The inverse
binomial scalar and both stopping predicates are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedStoppedDyad (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
        (if a*b ∈ centralProductEnvelope X then
          centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimePolynomialBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse bounds for the genuine semiprime polynomials. These bounds are
uniform in all heights and are used only beyond the power cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def semiprimeModelPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  ∑ p ∈ semiprimeFullSupport X i, ∑ q ∈ semiprimeFullSupport X j,
    semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
      ((cStar:ℂ)*(idealMoebius (p*q):ℂ)^2*((norm (p*q)^(-1/6:ℝ):ℝ):ℂ)*normTwist u (p*q))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothed
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full Mellin transfer for the actual semiprime pieces. Every Mellin
frequency is included before the low-height kernel is estimated. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeSmoothedPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  centeredProductSmoothed (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
    0 primeProductEnvelope X u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstReduction
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial central comparison after the complete high-scale branch
has been discharged. Only the faithful low-scale stopping problem remains. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def scaleFirstLowAritySum (m : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, distinguishedLowScaleRows i ℓ ξ Ct H X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedReduction
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial central kernel reduced to the two actual stopped branches.
The no-stop term is removed using one arbitrarily small fixed mesh for
all arities and all first-stage boundary choices. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def scaleFirstStoppedSum (m : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (h : ℕ) (early : Bool) : ℂ :=
  ∑ i ∈ Finset.range m, distinguishedScaleStopped i ρ ξ Ct H X h early

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime detection on each original high-height window. The smooth
total-product envelope and the finite squarefree support are retained. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstTailRoughWindow (ℓ : ℤ) (H U X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*scaleFirstTailKernel ℓ H U X n

def scaleFirstTailSemiprimeWindow (ℓ : ℤ) (H U X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X with (primeFactors n).card = 2,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*scaleFirstTailKernel ℓ H U X n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecompositionRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale-first and two-stage stopping identities for the original
Gauss height windows. Every matrix retains its total-product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstTailStoppedDyad (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
        (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstNoStopTailNegligible
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire ordinary-height no-stop contribution is negligible,
including every norm partition and every actual height window. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstOrdinaryNoStopArity (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(69/200:ℝ) then
          scaleFirstTailNoStopRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h d else 0
    else 0

def scaleFirstOrdinaryNoStopTail (m : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) : ℂ :=
  ∑ i ∈ Finset.range m, scaleFirstOrdinaryNoStopArity i ρ ξ H T X h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedTailCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of zero distinguished coefficients before the height-tail
estimate. This proves roughness of the actual remaining support and keeps
the original stopped coefficient unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedStoppedRoughSupport (i : ℕ) (ξ X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    Finset Eisenstein :=
  (centralPrimaryFactors X).filter (fun r => distinguishedScaleCoefficient i ξ X d r ≠ 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailAggregation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact summation of retained-envelope height tails over the original
labels, sharp side dyads and low distinguished-scale pieces. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstStoppedEnvelopeTail (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstOrdinaryStoppedTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-height stopped contribution is an exact prefix of the
retained-envelope tail, bounded as a difference of two complete tails. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstStoppedWindow (i : ℕ) (ρ ξ H U X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      scaleFirstTailStoppedRow i 0 ρ ξ H U X h early d else 0

def scaleFirstOrdinaryStoppedArity (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      scaleFirstStoppedWindow i ρ ξ H (T*(3/2:ℝ)^s) X h early else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstOrdinaryTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordinary-height low distinguished-scale contribution is
negligible, by the exact no-stop and two-stage stopped decomposition. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstOrdinaryLowArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(69/200:ℝ) then
          scaleFirstTailScaleRow i 0 ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def scaleFirstOrdinaryLowTail (m : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, scaleFirstOrdinaryLowArity i ξ H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact smooth coordinate partition of each literal semiprime Gauss window.
The finite prime cutoff and the original product envelope are retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def semiprimeGaussTailPiece (ℓ : ℤ) (H T X : ℝ) (i j : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
    semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
      scaleFirstTailKernel ℓ H T X (p*q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both analytic height ranges on the original smooth rough-prime weights.
The parameter families retain their actual transition ratios. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeGaussUnitWindow (r s A B H U X : ℝ) : ℂ :=
  productGaussWindow
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B))
    0 primeProductEnvelope H U X

def semiprimeGaussUnitTail (r s A B H U X : ℝ) : ℂ :=
  envelopeCutoffBilinearTail
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B))
    primeProductEnvelope H U X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic cancellation for the literal semiprime Gauss tail in the
prime-detector decomposition, retaining every height window and norm piece. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def semiprimeGaussTail (H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    scaleFirstTailSemiprimeWindow 0 H (T*(3/2:ℝ)^s) X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailAngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular coefficient transfer for the original semiprime Gauss
window. The twist preserves the actual prime support and coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def semiprimeAngularCoefficient (ℓ : ℤ) (X : ℝ) (i : ℕ) (p : Eisenstein) : ℂ :=
  theta ℓ p*semiprimePartitionCoefficient X i p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailAngularHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed-angular semiprime window from the derived angular
Hecke height mean, preserving its full product Mellin envelope. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

def semiprimeGaussAngularUnitWindow (r s A B H U X : ℝ) : ℂ :=
  productGaussWindow
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A) 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B) 1)
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight r) (fun _ => A))
    (fullPrimeCoefficient 2 (fun _ : Unit => semiprimeSmoothWeight s) (fun _ => B))
    ℓ primeProductEnvelope H U X


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailAngularMiddle
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The all-height middle-range semiprime tail remains valid with every
fixed angular twist. Its constants are independent of the angular index. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeAngularEnvelopeTail (ℓ : ℤ) (H U X : ℝ) (i j : ℕ) : ℂ :=
  envelopeCutoffBilinearTail (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimeAngularCoefficient ℓ X i) (semiprimeAngularCoefficient ℓ X j)
    primeProductEnvelope H U X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailAngularSplit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local-height separation of the angular semiprime tail. The high
part is negligible using all-height dispersion; the low part is left as the
literal finite sum to which the angular Hecke mean must be applied. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def semiprimeGaussTailAngular (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    scaleFirstTailSemiprimeWindow ℓ H (T*(3/2:ℝ)^s) X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmetic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized arithmetic coefficient of DR v3 (5.7), indexed on the
common cusp lattice lambda^-4 Z[omega]. The coefficient used in the
Whittaker series is tau(mu)/|mu|. No modular transformation is asserted. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Absolute convergence for the literal normalized arithmetic coefficients. -/
theorem cubicThetaArithmetic_summable {v : ℝ} (hv : 0 < v) (z : ℂ) :
    Summable (cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v) :=
  cubicThetaSeries_summable (by norm_num : (0:ℝ) ≤ 81) cubicThetaArithmeticCoefficient_bound hv z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaCuspCoefficient_zero : cubicThetaCuspCoefficient 0 = cubicThetaArithmeticCoefficient := by
  funext n
  unfold cubicThetaCuspCoefficient cubicThetaArithmeticCoefficient
  split_ifs <;> simp [CubicThetaCoordinates.cuspCoefficient]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusModes
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual trace frequencies are the full Fourier basis of the
three-Eisenstein period cell. This fixes the lattice index and Parseval
normalization for the cusp Hilbert space. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions
theorem cubicThetaTorus_parseval (F : CubicThetaTorusL2) :
    (∑' h : Eisenstein, ‖cubicThetaTorusCoefficient F h‖^2)=‖F‖^2 := by
  calc
    _ = ∑' n : Fin 2 → ℤ, ‖UnitAddTorus.mFourierCoeff F n‖^2 :=
      cubicThetaFourierIndex.tsum_eq _
    _ = ∫ t, ‖F t‖^2 := (UnitAddTorus.hasSum_sq_mFourierCoeff F).tsum_eq
    _ = _ := (cubicTheta_l2_norm_sq_measure F).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic remainder on each high-cusp torus, with its
nonzero coefficient computed from the initial arithmetic series. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticTorusMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticTorusProbability
lemma cubicThetaArithmeticTorus_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticTorus v s)) h=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaNonzeroFrequencyTerm (0,v) s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [← cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaArithmeticTorus v s)=_
  rw [cubicThetaArithmeticTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
    ite_eq_right hh,cubicThetaTorusRemainder_coefficient hv hs,smul_eq_mul,mul_zero,zero_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantModeResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residue of the zero Fourier mode of the principal
level-three Eisenstein series. Nonzero Fourier modes remain separate. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_principalZeta_residue_value :
    principalThetaConstant/(residueHeckeScale 1:ℂ)=(Real.pi:ℂ)/(3*Real.sqrt 3) := by
  unfold principalThetaConstant residueHeckeScale
  rw [eisenstein_units_card]
  have hnorm : norm (1:Eisenstein)=1 := by norm_num [norm]
  rw [hnorm,mul_one,Complex.ofReal_div,Complex.ofReal_mul]
  push_cast
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticRowSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindex the literal theta expansion on the actual three-Eisenstein
period lattice. Coefficients off this lattice vanish by their ramified
support, so this change of variables introduces no multiplicity. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaSeriesTerm_row_support (z : ℂ) (v : ℝ) :
    Function.support (cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v) ⊆
      Set.range (fun h : Eisenstein => -lambdaE*h) := by
  intro n hn
  have ha : cubicThetaArithmeticCoefficient n≠0 := by
    intro hz
    exact hn (by simp [cubicThetaSeriesTerm,hz])
  obtain ⟨h,hh⟩ := cubicThetaArithmeticCoefficient_lambda_dvd ha
  exact ⟨-h,by simpa using hh.symm⟩

lemma cubicThetaArithmeticRowTerm_eq (z : ℂ) (v : ℝ) (h : Eisenstein) :
    cubicThetaArithmeticRowTerm z v h=
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v (-lambdaE*h) := by
  by_cases hh : h=0
  · simp [cubicThetaArithmeticRowTerm,cubicThetaSeriesTerm,hh]
  · have hn : -lambdaE*h≠0 := mul_ne_zero (neg_ne_zero.mpr lambdaE_prime.ne_zero) hh
    simp only [cubicThetaArithmeticRowTerm,cubicThetaSeriesTerm,hh,hn,ite_false, if_false,
      cubicThetaRowFrequency_index]
    congr 3
    unfold tracePair
    rw [mul_comm z (cubicThetaRowFrequency h)]

theorem cubicThetaArithmeticRowSeries (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v)=
      ∑' h : Eisenstein,cubicThetaArithmeticRowTerm z v h := by
  simp_rw [cubicThetaArithmeticRowTerm_eq]
  exact (cubicThetaRowIndex_injective.tsum_eq
    (cubicThetaSeriesTerm_row_support z v)).symm

lemma cubicThetaArithmeticRowTerm_summable (z : ℂ) {v : ℝ} (hv : 0<v) :
    Summable (cubicThetaArithmeticRowTerm z v) := by
  simpa only [Function.comp_def,←cubicThetaArithmeticRowTerm_eq] using
    (cubicThetaArithmetic_summable hv z).comp_injective cubicThetaRowIndex_injective

lemma cubicThetaArithmeticRowTerm_phase (z : ℂ) (v : ℝ) (h : Eisenstein) :
    cubicThetaArithmeticRowTerm z v h=cubicThetaArithmeticRowTerm 0 v h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ) := by
  by_cases hh : h=0
  · simp [cubicThetaArithmeticRowTerm,hh]
  · simp [cubicThetaArithmeticRowTerm,hh,tracePair]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous torus realization of the explicit arithmetic theta series.
The nonconstant scalar is retained while its normalization is established. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticModelRemainder (v : ℝ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein,cubicThetaArithmeticRowTerm 0 v h • cubicThetaTorusFourier h

lemma cubicThetaArithmeticModelRemainder_summable {v : ℝ} (hv : 0<v) :
    Summable (fun h : Eisenstein =>
      cubicThetaArithmeticRowTerm 0 v h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using
    (cubicThetaArithmeticRowTerm_summable 0 hv).norm

lemma cubicThetaArithmeticModelRemainder_real {v : ℝ} (hv : 0<v) (x : Fin 2 → ℝ) :
    cubicThetaArithmeticModelRemainder v (fun i => (x i:UnitAddCircle))=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (cubicThetaPeriodCell x,v) := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaArithmeticModelRemainder_summable hv)
  change cubicThetaArithmeticModelRemainder v (fun i => (x i:UnitAddCircle))=_ at he
  rw [he,cubicThetaArithmeticRowSeries]
  apply tsum_congr
  intro h
  change cubicThetaArithmeticRowTerm 0 v h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,←cubicThetaArithmeticRowTerm_phase]

attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticModelTorusMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticModelTorusProbability
lemma cubicThetaArithmeticModelRemainder_coefficient {v : ℝ} (hv : 0<v) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaArithmeticModelRemainder v)) k=cubicThetaArithmeticRowTerm 0 v k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaArithmeticModelRemainder v)=_
  rw [cubicThetaArithmeticModelRemainder,L.map_tsum
    (cubicThetaArithmeticModelRemainder_summable hv),tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,
      smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

def cubicThetaArithmeticModel (A : ℂ) (p : ℂ × ℝ) : ℂ :=
  (cubicThetaConstant*p.2^(2/3:ℝ):ℝ)+
    A*cubicThetaNonconstant cubicThetaArithmeticCoefficient p

def cubicThetaArithmeticModelTorus (A : ℂ) (v : ℝ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ) • cubicThetaTorusFourier 0+
    A • cubicThetaArithmeticModelRemainder v

lemma cubicThetaArithmeticModelTorus_real (A : ℂ) {v : ℝ} (hv : 0<v) (x : Fin 2 → ℝ) :
    cubicThetaArithmeticModelTorus A v (fun i => (x i:UnitAddCircle))=
      cubicThetaArithmeticModel A (cubicThetaPeriodCell x,v) := by
  simp only [cubicThetaArithmeticModelTorus,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    cubicThetaTorusFourier_zero,ContinuousMap.one_apply,smul_eq_mul,mul_one,
    cubicThetaArithmeticModelRemainder_real hv,cubicThetaArithmeticModel]

theorem cubicThetaArithmeticModelTorus_coefficient (A : ℂ) {v : ℝ} (hv : 0<v)
    (h : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaArithmeticModelTorus A v)) h=
      if h=0 then ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)
      else A*cubicThetaArithmeticCoefficient (-lambdaE*h)*
        cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v) := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaArithmeticModelTorus A v)=_
  rw [cubicThetaArithmeticModelTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
    cubicThetaArithmeticModelRemainder_coefficient hv,smul_eq_mul]
  by_cases hh : h=0
  · simp [hh,cubicThetaArithmeticRowTerm]
  · simp [hh,cubicThetaArithmeticRowTerm,tracePair,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit arithmetic model is an actual L2 function on the
high cusp, including its nonzero constant term. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticModel_remainder_memLp :
    MemLp (fun p : CubicThetaPoint => cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val)
      2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaNonconstant_continuousAt (by norm_num : (0:ℝ)≤81)
      cubicThetaArithmeticCoefficient_bound p.property).comp continuous_subtype_val.continuousAt
  apply MemLp.of_bound hc.aestronglyMeasurable (cubicThetaExpConstant 81)
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp
  have hv : 1≤p.val.2 := by have h : (2:ℝ)<p.val.2 := hp.1; linarith
  have he := cubicThetaAuxiliarySeries_exponential_bound 0 p.val.1 hv
  rw [cubicThetaAuxiliarySeries,cubicThetaCuspCoefficient_zero] at he
  apply he.trans
  apply mul_le_of_le_one_right
  · have hb := cubicThetaAuxiliarySeries_exponential_bound 0 0 (v:=1) (by norm_num)
    exact nonneg_of_mul_nonneg_left ((_root_.norm_nonneg _).trans hb)
      (Real.exp_pos _)
  · apply Real.exp_le_one_iff.mpr
    have := Real.pi_pos
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded multiplicity of a positive-height period strip over the
actual arithmetic quotient. Only a finite compact chart cover is used. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPositiveStrip_compact_cover {ε : ℝ} (hε : 0<ε) :
    ∃ K : Set CubicThetaPoint,IsCompact K ∧
      cubicThetaCuspStrip ε⊆K ∪ cubicThetaCuspStrip 2 := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaHorizontalCell_compact_container
  let B : Set (ℂ × ℝ) := L ×ˢ Icc ε 2
  have hpos : B⊆{y : ℂ × ℝ | 0<y.2} := fun y hy => hε.trans_le hy.2.1
  have hc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  refine ⟨cubicThetaPointInclusion.symm '' B,
    (hL.prod isCompact_Icc).image_of_continuousOn (hc.mono hpos),?_⟩
  intro p hp
  by_cases hv : 2<p.val.2
  · exact Or.inr ⟨hv,hp.2⟩
  · apply Or.inl
    refine ⟨p.val,⟨hcell hp.2,hp.1.le,le_of_not_gt hv⟩,?_⟩
    exact cubicThetaPointInclusion.left_inv
      (by rw [cubicThetaPointInclusion_source]; trivial)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaBorelSheet_measurable (g : cubicThetaPrincipalGroup) :
    MeasurableSet (cubicThetaBorelSheet g) :=
  measurableSet_eq_fun ((measurable_const_smul g).comp
    (cubicThetaBorelSection_measurable.comp cubicThetaQuotientMap_open.continuous.measurable))
    measurable_id

lemma cubicThetaBorelSheet_cover (p : CubicThetaPoint) :
    ∃ g : cubicThetaPrincipalGroup,p∈cubicThetaBorelSheet g := by
  have hq : cubicThetaQuotientMap p=
      cubicThetaQuotientMap (cubicThetaBorelSection (cubicThetaQuotientMap p)) := by
    rw [cubicThetaBorelSection_rightInverse]
  exact cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp hq

lemma cubicThetaBorelPhase_exists :
    ∃ b : CubicThetaPoint → ℂ,Measurable b ∧
      ∀ g,EqOn b (fun _ => cubicThetaKubotaValue g) (cubicThetaBorelSheet g) := by
  apply exists_measurable_piecewise cubicThetaBorelSheet cubicThetaBorelSheet_measurable
    (fun g _ => cubicThetaKubotaValue g) (fun _ => measurable_const)
  intro g h hne p hp
  exact False.elim (Set.disjoint_left.mp (cubicThetaBorelSheet_disjoint hne) hp.1 hp.2)

def cubicThetaBorelPhase : CubicThetaPoint → ℂ :=
  Classical.choose cubicThetaBorelPhase_exists

lemma cubicThetaBorelPhase_measurable : Measurable cubicThetaBorelPhase :=
  (Classical.choose_spec cubicThetaBorelPhase_exists).1

lemma cubicThetaBorelPhase_sheet (g : cubicThetaPrincipalGroup) {p : CubicThetaPoint}
    (hp : p∈cubicThetaBorelSheet g) : cubicThetaBorelPhase p=cubicThetaKubotaValue g :=
  (Classical.choose_spec cubicThetaBorelPhase_exists).2 g hp

lemma cubicThetaBorelPhase_norm (p : CubicThetaPoint) : ‖cubicThetaBorelPhase p‖=1 := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelPhase_sheet g hg,cubicThetaKubotaValue_norm]

lemma cubicThetaBorelPhase_smul (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaBorelPhase (g • p)=cubicThetaKubotaValue g*cubicThetaBorelPhase p := by
  obtain ⟨h,hh⟩ := cubicThetaBorelSheet_cover p
  have hgh : g • p∈cubicThetaBorelSheet (g*h) := by
    change (g*h) • cubicThetaBorelSection (cubicThetaQuotientMap (g • p))=g • p
    rw [cubicThetaQuotient_covering.map_smul,mul_smul,hh]
  rw [cubicThetaBorelPhase_sheet (g*h) hgh,cubicThetaBorelPhase_sheet h hh,
    cubicThetaKubotaValue_mul]

def cubicThetaBorelLift (f : CubicThetaQuotient → ℂ) (p : CubicThetaPoint) : ℂ :=
  cubicThetaBorelPhase p*f (cubicThetaQuotientMap p)

lemma cubicThetaBorelLift_measurable {f : CubicThetaQuotient → ℂ} (hf : Measurable f) :
    Measurable (cubicThetaBorelLift f) :=
  cubicThetaBorelPhase_measurable.mul (hf.comp cubicThetaQuotientMap_open.continuous.measurable)

lemma cubicThetaBorelLift_norm (f : CubicThetaQuotient → ℂ) (p : CubicThetaPoint) :
    ‖cubicThetaBorelLift f p‖=‖f (cubicThetaQuotientMap p)‖ := by
  rw [cubicThetaBorelLift,norm_mul,cubicThetaBorelPhase_norm,one_mul]

theorem cubicThetaBorelLift_automorphy (f : CubicThetaQuotient → ℂ)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaBorelLift f (g • p)=cubicThetaKubotaValue g*cubicThetaBorelLift f p := by
  rw [cubicThetaBorelLift,cubicThetaBorelLift,cubicThetaBorelPhase_smul,
    cubicThetaQuotient_covering.map_smul,mul_assoc]

lemma cubicThetaBorelLift_section (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaBorelLift (cubicThetaSectionRepresentative F) p=F.val p := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelLift,cubicThetaBorelPhase_sheet g hg,cubicThetaSectionRepresentative,
    ←F.property g]
  exact congrArg F.val hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaTorusCellPoint_embedding : MeasurableEmbedding cubicThetaTorusCellPoint := by
  have hS : MeasurableSet {x : Fin 2 → ℝ | ∀ i,
      x i∈Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i+1)} :=
    MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  exact cubicThetaPeriodEquiv.toHomeomorph.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe hS).comp
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)).measurableEmbedding)

lemma cubicThetaTorusCellPoint_character (h : Eisenstein) (u : UnitAddTorus (Fin 2)) :
    cubicThetaTorusFourier h u=
      (Real.fourierChar (tracePair (cubicThetaTorusCellPoint u) (cubicThetaRowFrequency h)):ℂ) := by
  let e := UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)
  have hu : (fun i => ((e u).val i:UnitAddCircle))=u := e.symm_apply_apply u
  calc
    _ = cubicThetaTorusFourier h (fun i => ((e u).val i:UnitAddCircle)) :=
      congrArg (cubicThetaTorusFourier h) hu.symm
    _ = _ := cubicThetaTorusFourier_actual h (e u).val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded restriction to any positive-height period strip.
Injectivity is replaced by the proved finite multiplicity below height two. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPositiveStrip_finite {ε : ℝ} (hε : 0<ε) :
    IsFiniteMeasure (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨K,hK,hcover⟩ := cubicThetaPositiveStrip_compact_cover hε
  constructor
  rw [Measure.restrict_apply_univ]
  exact (measure_mono hcover).trans_lt
    ((measure_union_le K (cubicThetaCuspStrip 2)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨cubicThetaPointMeasure_compact hK,
        by simpa only [Measure.restrict_apply_univ] using
          (measure_lt_top (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) univ)⟩))

local instance positiveCuspRestriction_finiteEnergyAdd : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveModelL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic series in the L2 space of every positive
height strip, with its scalar still retained. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticModel_point_continuous (A : ℂ) :
    Continuous (fun p : CubicThetaPoint => cubicThetaArithmeticModel A p.val) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hc : ContinuousAt (cubicThetaArithmeticModel A) p.val := by
    unfold cubicThetaArithmeticModel
    apply ContinuousAt.add
    · apply Complex.continuous_ofReal.continuousAt.comp
      exact (continuousAt_snd.rpow_const (Or.inl p.property.ne')).const_mul _
    · exact (cubicThetaNonconstant_continuousAt (by norm_num : (0:ℝ)≤81)
        cubicThetaArithmeticCoefficient_bound p.property).const_mul A
  exact hc.comp continuous_subtype_val.continuousAt

lemma cubicThetaPositiveFourierWeight_memLp {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    MemLp (cubicThetaCuspFourierWeight h W) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  have := cubicThetaPositiveStrip_finite hε
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  apply MemLp.of_bound (cubicThetaCuspFourierWeight_continuous h W).aestronglyMeasurable (max C 0)
  apply Filter.Eventually.of_forall
  intro p
  rw [cubicThetaCuspFourierWeight,norm_mul,Circle.norm_coe,mul_one]
  by_cases hp : p.val.2∈tsupport W
  · exact (hC p.val.2 hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp,norm_zero]
    exact le_max_right _ _

def cubicThetaPositiveStripFourierTest {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    CubicThetaPositiveStripL2 ε :=
  (cubicThetaPositiveFourierWeight_memLp hε h W).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspWindowCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The doubled transition annulus still lies in a compact arithmetic core. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCuspWindow_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1 ≤ cubicThetaPointHeight p → cubicThetaPointHeight p≤4 →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S 4 := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y≤4 := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le hp₂
    apply (div_le_iff₀ (cubicThetaPointHeight_pos p)).mpr
    linarith
  have hyc : y.val∈cubicThetaSiegelCore 4 := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,?_⟩
  · change (k • q).val∈cubicThetaCompactCore S 4
    refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
    have he := congrArg cubicThetaPointCoordinates hpoint
    exact he
  · exact cubicThetaQuotient_covering.map_smul k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimePowerFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local conductor restriction for cubic Gauss coefficients at an
unramified prime power. The weight is the literal cubic residue symbol. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaLocalPrimePowerGauss_support {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein)
    (hG : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) h≠0) : p^n ∣ h := by
  let : Finite (Residues (p^(n+1))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^(n+1))) := Fintype.ofFinite _
  have he : p^(n+1) ∣ p*h := by
    apply residueFourier_inflation_support (pow_ne_zero _ hp.2.ne_zero)
      (dvd_pow_self p (Nat.succ_ne_zero n)) (fun x => (cubicResidueChar p hp x)^(n+1)) h
    simpa only [cubicThetaLocalPrimePowerGauss,tsum_fintype,
      cubicThetaPrimePowerWeight_inflation hp] using hG
  rwa [pow_succ,mul_comm (p^n) p,mul_dvd_mul_iff_left hp.2.ne_zero] at he

theorem cubicThetaLocalPrimePowerGauss_eq_zero {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) (hh : ¬p^n ∣ h) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) h=0 := by
  by_contra hn
  exact hh (cubicThetaLocalPrimePowerGauss_support hp n h hn)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussParity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaEisensteinGaussCoefficient_neg {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (-c) (-h)=cubicThetaEisensteinGaussCoefficient c h := by
  have hmod : modulus (3*(-c))=modulus (3*c) := by
    rw [show (3:Eisenstein)*(-c)= -(3*c) by ring]
    exact Ideal.span_singleton_neg (x:=(3*c:Eisenstein))
  let e : Residues (3*(-c)) ≃+* Residues (3*c) :=
    Ideal.quotEquivOfEq (R:=Eisenstein) hmod
  have hrep (x : Residues (3*(-c))) :
      Ideal.Quotient.mk (modulus (3*c)) (residueRepresentative (3*(-c)) x)=e x := by
    rw [← Ideal.quotEquivOfEq_mk hmod,residueRepresentative_spec]
  have hw (x : Residues (3*(-c))) :
      cubicThetaEisensteinResidueWeight (-c) x=cubicThetaEisensteinResidueWeight c (e x) := by
    rw [cubicThetaEisensteinResidueWeight,cubicThetaEisensteinWeight_neg_c]
    rw [← cubicThetaEisensteinResidueWeight_mk hc,hrep]
  unfold cubicThetaEisensteinGaussCoefficient
  rw [← e.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  rw [hw]
  congr 1
  have hphase := tracePhase_congr (mul_ne_zero (by norm_num : (3:Eisenstein)≠0) hc0) h
    ((hrep x).trans (residueRepresentative_spec (3*c) (e x)).symm)
  convert hphase using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  push_cast
  ring_nf

lemma cubicThetaFrequencyTerm_neg (s : ℂ) (h c : Eisenstein) :
    cubicThetaFrequencyTerm s (-h) (-c)=cubicThetaFrequencyTerm s h c := by
  have hn : norm (-c)=norm c := by simp only [norm,Subalgebra.coe_neg,Complex.normSq_neg]
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · have hc' : (3:Eisenstein)∣(-c) ∧ (-c)≠0 := by simpa using hc
    rw [cubicThetaFrequencyTerm,cubicThetaFrequencyTerm,ite_eq_left hc',ite_eq_left hc,
      cubicThetaEisensteinGaussCoefficient_neg hc.1 hc.2,hn]
  · have hc' : ¬((3:Eisenstein)∣(-c) ∧ (-c)≠0) := by simpa using hc
    simp only [cubicThetaFrequencyTerm,ite_eq_right hc',ite_eq_right hc]

theorem cubicThetaFrequencyDirichlet_neg (h : Eisenstein) (s : ℂ) :
    cubicThetaFrequencyDirichlet (-h) s=cubicThetaFrequencyDirichlet h s := by
  calc
    _ = ∑' c : Eisenstein, cubicThetaFrequencyTerm s (-h) (-c) :=
      ((Equiv.neg Eisenstein).tsum_eq (cubicThetaFrequencyTerm s (-h))).symm
    _ = _ := tsum_congr (cubicThetaFrequencyTerm_neg s h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaIncomingWindow_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (s : ℂ) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 4 →
        cubicThetaIncomingWindow p.val s=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspWindow_core
  refine ⟨S,fun s p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaIncomingWindowTerm r p.val s=0 by
    simp only [cubicThetaIncomingWindow,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤1
  · exact mul_eq_zero_of_left (cubicThetaIncomingWindowCutoff_low hlo) _
  by_cases hhi : 4 ≤ r.height p.val
  · exact mul_eq_zero_of_left (cubicThetaIncomingWindowCutoff_high hhi) _
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; linarith)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

lemma cubicThetaIncomingWindowSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaIncomingWindowSection s)) := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingWindow_core
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S 4)
  intro q hq
  by_contra h
  have hz := hS s (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaIncomingWindow (cubicThetaQuotientLift q).val s‖=0
  rw [hz,norm_zero]

def cubicThetaIncomingWindowTest (s : ℂ) : cubicThetaSmoothTests :=
  ⟨cubicThetaIncomingWindowSection s,by
    refine ⟨?_,cubicThetaIncomingWindowSection_compact s⟩
    apply (cubicThetaIncomingWindow_contDiffOn s).congr
    intro y hy
    change cubicThetaIncomingWindow (cubicThetaPointInclusion.symm y).val s=
      cubicThetaIncomingWindow y s
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaIncomingWindow p s) he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaHighWindowSeries_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (s : ℂ) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 4 →
        cubicThetaHighWindowSeries p.val s=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspWindow_core
  refine ⟨S,fun s p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaHighWindowTerm r p.val s=0 by
    simp only [cubicThetaHighWindowSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤2
  · exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s hlo)
  by_cases hhi : 4 ≤ r.height p.val
  · exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_high s hhi)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; linarith)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

lemma cubicThetaHighWindowSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaHighWindowSection s)) := by
  obtain ⟨S,hS⟩ := cubicThetaHighWindowSeries_core
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S 4)
  intro q hq
  by_contra h
  have hz := hS s (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaHighWindowSeries (cubicThetaQuotientLift q).val s‖=0
  rw [hz,norm_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global pairing with the high forcing is exactly the constant
cusp observation, first on actual sections and then on the energy closure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHighWindowSeries_off_cusp (s : ℂ) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉cubicThetaQuotientMap '' cubicThetaCuspStrip 2) :
    cubicThetaHighWindowSeries p.val s=0 := by
  suffices hz : ∀ r, cubicThetaHighWindowTerm r p.val s=0 by
    simp only [cubicThetaHighWindowSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val≤2
  · exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s hh)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction (H:=2) (r.completion • p) (by rw [he]; linarith)
  have hq : cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • (r.completion • p))=
      cubicThetaQuotientMap p :=
    (cubicThetaQuotient_covering.map_smul (cubicThetaPrincipalTranslation w)).trans
      (cubicThetaQuotient_covering.map_smul r.completion)
  exact False.elim (hp ⟨_,hw,hq⟩)

def cubicThetaHighWindowL2 (s : ℂ) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaHighWindowSection s)
    (cubicThetaHighWindowSection_compact s)).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact compact-window weak equation connects the low forcing
with the high cusp observation of every actual spectral residue. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaWindowForcingSection (s : ℂ) : CubicThetaSection :=
  cubicThetaHighWindowSection s-cubicThetaForcingSection s

lemma cubicThetaWindowForcingSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaWindowForcingSection s)) :=
  cubicThetaCompactSection_sub _ _ (cubicThetaHighWindowSection_compact s)
    (cubicThetaForcingSection_compact s)

lemma cubicThetaWindowForcingL2 (s : ℂ) :
    (cubicThetaCompactSection_memLp (cubicThetaWindowForcingSection s)
      (cubicThetaWindowForcingSection_compact s)).toLp _=
      cubicThetaHighWindowL2 s-cubicThetaForcingL2 s := by
  exact MemLp.toLp_sub (cubicThetaCompactSection_memLp (cubicThetaHighWindowSection s)
    (cubicThetaHighWindowSection_compact s))
    (cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s))

lemma cubicThetaWindow_coordinate_equation (s : ℂ) (p : ℂ × ℝ) (hp : 0<p.2) :
    cubicThetaCoordinateLaplacian (cubicThetaSectionFunction (cubicThetaIncomingWindowTest s)) p=
      s*(s-2)*cubicThetaSectionFunction (cubicThetaIncomingWindowTest s) p-
        cubicThetaSectionFunction (cubicThetaWindowForcingSection s) p := by
  have he : ∀ x y v, 0<v →
      cubicThetaSectionFunction (cubicThetaIncomingWindowTest s) (cubicThetaCartesianPoint x y v)=
        cubicThetaIncomingWindow (cubicThetaCartesianPoint x y v) s := by
    intro x y v hv
    rw [cubicThetaSectionFunction_apply _ hv]
    rfl
  rw [cubicThetaCoordinateLaplacian_hyperbolic,
    cubicThetaHyperbolicOperator_congr he p.1.re p.1.im hp,
    cubicThetaIncomingWindow_equation s p.1.re p.1.im hp,cubicThetaCartesianPoint_self,
    cubicThetaSectionFunction_apply _ hp,cubicThetaSectionFunction_apply _ hp]
  change s*(s-2)*cubicThetaIncomingWindow p s+cubicThetaForcingSeries p s-
    cubicThetaHighWindowSeries p s=
    s*(s-2)*cubicThetaIncomingWindow p s-
      (cubicThetaHighWindowSeries p s-cubicThetaForcingSeries p s)
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueVanishing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact incoming window kills every spurious real residue of the
actual arithmetic family: only the theta parameter can contribute. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticResidueEnergy_eq_zero_of_orthogonal (σ : ℝ)
    (h : inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=0) : cubicThetaArithmeticResidueEnergy σ=0 := by
  let K := (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))).ker
  let f := cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 σ)
  let c := cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)
  let Q := K.starProjection f
  have hR : cubicThetaArithmeticResidueEnergy σ=c • Q := rfl
  by_cases hc : c=0
  · rw [hR,hc,zero_smul]
  have hP : K.starProjection Q=Q := K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem f)
  have hQ : inner ℂ Q f=inner ℂ Q Q := by
    have hi := K.inner_starProjection_left_eq_right Q f
    rw [hP] at hi
    exact hi
  have hi : inner ℂ (c • Q) f=0 := by
    rw [← hR,ContinuousLinearMap.adjoint_inner_right]
    exact h
  rw [inner_smul_left (𝕜:=ℂ) Q f c,hQ] at hi
  have hself : inner ℂ Q Q=0 := (mul_eq_zero.mp hi).resolve_left (by simpa using hc)
  have hzero : Q=0 := (inner_self_eq_zero (𝕜:=ℂ) (x:=Q)).mp hself
  rw [hR,hzero,smul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite arithmetic Fourier coefficient under a primary change of
additive frequency. The relation is proved on the actual residue ring;
it is independent of any continuation or theta coefficient formula. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_mul {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0) (hu : primary u)
    (hcu : IsCoprime c u) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c (h*u)=
      star (cubicSymbol u c)*cubicThetaEisensteinGaussCoefficient c h := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3u : IsCoprime (3:Eisenstein) u :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
  obtain ⟨U,hU⟩ := residue_isUnit_of_isCoprime (h3u.mul_left hcu)
  let f (x : Residues (3*c)) : ℂ := cubicThetaEisensteinResidueWeight c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      ((h:ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ)
  let g (x : Residues (3*c)) : ℂ := cubicThetaEisensteinResidueWeight c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      (((h*u:Eisenstein):ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ)
  have he (x : Residues (3*c)) :
      Ideal.Quotient.mk (modulus (3*c)) (residueRepresentative (3*c) (U.mulLeft x))=
        Ideal.Quotient.mk (modulus (3*c)) (u*residueRepresentative (3*c) x) := by
    rw [residueRepresentative_spec,map_mul,residueRepresentative_spec]
    change (U:Residues (3*c))*x=Ideal.Quotient.mk (modulus (3*c)) u*x
    rw [hU]
  have ht (x : Residues (3*c)) : f (U.mulLeft x)=cubicSymbol u c*g x := by
    dsimp only [f,g]
    have hw : cubicThetaEisensteinResidueWeight c (U.mulLeft x)=
        cubicSymbol u c*cubicThetaEisensteinResidueWeight c x := by
      change cubicThetaEisensteinResidueWeight c ((U:Residues (3*c))*x)=_
      rw [hU,cubicThetaEisensteinResidueWeight_mul hc hu hcu]
    rw [hw,tracePhase_congr (mul_ne_zero (by norm_num) hc0) h (he x)]
    have hp : tracePair ((u*residueRepresentative (3*c) x:Eisenstein):ℂ)
        ((h:ℂ)/((3*c:Eisenstein)*traceLambda))=
        tracePair (residueRepresentative (3*c) x:ℂ)
          (((h*u:Eisenstein):ℂ)/((3*c:Eisenstein)*traceLambda)) := by
      unfold tracePair
      congr 2
      push_cast
      ring
    rw [hp]
    ring
  have hs : (∑ x : Residues (3*c), f x)=cubicSymbol u c*∑ x : Residues (3*c), g x := by
    rw [← Equiv.sum_comp U.mulLeft f]
    simp_rw [ht]
    rw [Finset.mul_sum]
  have hunit : star (cubicSymbol u c)*cubicSymbol u c=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hu hcu.symm]
    norm_num
  change (∑' x : Residues (3*c), g x)=star (cubicSymbol u c)*∑' x : Residues (3*c), f x
  rw [tsum_fintype,tsum_fintype,hs,← mul_assoc,hunit,one_mul]

theorem cubicThetaEisensteinGaussCoefficient_cubeFrequency {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0) (hu : primary u)
    (hcu : IsCoprime c u) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c (h*u^3)=cubicThetaEisensteinGaussCoefficient c h := by
  have hp : primary (u^3) := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using primary_mul (primary_mul hu hu) hu
  have hcp : IsCoprime c (u^3) := hcu.pow_right
  rw [cubicThetaEisensteinGaussCoefficient_mul hc hc0 hp hcp]
  have hchi : cubicSymbol (u^3) c=1 := by
    rw [show u^3=u*u*u by ring,cubicSymbol_mul_lower
      (mul_ne_zero (primary_ne_zero hu) (primary_ne_zero hu)) (primary_ne_zero hu),
      cubicSymbol_mul_lower (primary_ne_zero hu) (primary_ne_zero hu)]
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using cubicSymbol_cube_of_isCoprime hu c hcu.symm
  rw [hchi,star_one,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaEisensteinWeight_mix {u c : Eisenstein} (hu : primary u)
    (hc : (3:Eisenstein) ∣ c) (hcu : IsCoprime c u) (x y : Eisenstein) :
    cubicThetaEisensteinWeight (u*c) (3*c*x+u*y)=
      (cubicSymbol u (3*c)*cubicSymbol u c)*cubicSymbol u x*
        cubicThetaEisensteinWeight c y := by
  rw [cubicThetaEisensteinWeight_factor hu]
  have hs : cubicSymbol u (3*c*x+u*y)=cubicSymbol u (3*c*x) := by
    apply cubicSymbol_congr
    have hz : Ideal.Quotient.mk (modulus u) u=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl u))
    simp only [map_add,map_mul,hz,zero_mul,add_zero]
  have hw : cubicThetaEisensteinWeight c (3*c*x+u*y)=cubicThetaEisensteinWeight c (u*y) := by
    rw [add_comm (3*c*x)]
    exact cubicThetaEisensteinWeight_periodic hc (u*y) x
  rw [hs,hw,cubicSymbol_mul_upper hu,cubicThetaEisensteinWeight_mul hu hcu]
  ring

lemma cubicThetaEisensteinWeight_congr {c d e : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (he : Ideal.Quotient.mk (modulus (3*c)) d=Ideal.Quotient.mk (modulus (3*c)) e) :
    cubicThetaEisensteinWeight c d=cubicThetaEisensteinWeight c e := by
  rw [← cubicThetaEisensteinResidueWeight_mk hc,← cubicThetaEisensteinResidueWeight_mk hc,he]

lemma cubicThetaEisensteinWeight_congr_of_eq {q c d e : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hq : q=3*c)
    (he : Ideal.Quotient.mk (modulus q) d=Ideal.Quotient.mk (modulus q) e) :
    cubicThetaEisensteinWeight c d=cubicThetaEisensteinWeight c e := by
  subst q
  exact cubicThetaEisensteinWeight_congr hc he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowFiniteFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Fourier forms of the literal row and cubic-symbol sums.
These expose the same perfect codifferent pairing for Chinese remainders. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_fourier {c : Eisenstein} (hc : c≠0)
    (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c h=
      ∑' x : Residues (3*c), cubicThetaEisensteinWeight c (residueRepresentative (3*c) x)*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
          (Ideal.Quotient.mk (modulus (3*c)) h*x) := by
  unfold cubicThetaEisensteinGaussCoefficient cubicThetaEisensteinResidueWeight
  apply tsum_congr
  intro x
  rw [residueFourierChar_mk_mul]

theorem cubicThetaEisensteinGaussCoefficient_fourier_of_eq {q c : Eisenstein}
    (hc : c≠0) (hq : q≠0) (he : q=3*c) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c h=
      ∑' x : Residues q, cubicThetaEisensteinWeight c (residueRepresentative q x)*
        residueFourierChar q hq (Ideal.Quotient.mk (modulus q) h*x) := by
  subst q
  exact cubicThetaEisensteinGaussCoefficient_fourier hc h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unramified factorization of the Eisenstein-row Fourier coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_factor {u c : Eisenstein}
    (hu : primary u) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0) (hcu : IsCoprime c u)
    (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (u*c) h=
      (cubicSymbol u (3*c)*cubicSymbol u c)*cubicThetaSymbolFourier u (primary_ne_zero hu) h*
        cubicThetaEisensteinGaussCoefficient c h := by
  have hu0 := primary_ne_zero hu
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) hc0
  have huc : IsCoprime u (3*c) := by
    have h3 := isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
    exact h3.symm.mul_right hcu.symm
  have h3uc : (3:Eisenstein) ∣ u*c := dvd_mul_of_dvd_right hc u
  have hq : u*(3*c)=3*(u*c) := by ring
  let : Finite (Residues u) := finite_residues hu0
  let : Finite (Residues (3*c)) := finite_residues h3c
  let : Finite (Residues (u*(3*c))) := finite_residues (mul_ne_zero hu0 h3c)
  let : Fintype (Residues u) := Fintype.ofFinite _
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  let : Fintype (Residues (u*(3*c))) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix u (3*c)) (residueMix_bijective hu0 h3c huc)
  let F (x : Residues (u*(3*c))) : ℂ :=
    cubicThetaEisensteinWeight (u*c) (residueRepresentative (u*(3*c)) x)*
      residueFourierChar (u*(3*c)) (mul_ne_zero hu0 h3c)
        (Ideal.Quotient.mk (modulus (u*(3*c))) h*x)
  let f (x : Residues u) : ℂ := cubicSymbol u (residueRepresentative u x)*
    residueFourierChar u hu0 (Ideal.Quotient.mk (modulus u) h*x)
  let g (y : Residues (3*c)) : ℂ := cubicThetaEisensteinWeight c (residueRepresentative (3*c) y)*
    residueFourierChar (3*c) h3c (Ideal.Quotient.mk (modulus (3*c)) h*y)
  let C : ℂ := cubicSymbol u (3*c)*cubicSymbol u c
  have hF (v : Residues u × Residues (3*c)) : F (e v)=C*(f v.1*g v.2) := by
    have hr : Ideal.Quotient.mk (modulus (u*(3*c)))
        (residueRepresentative (u*(3*c)) (e v))=
      Ideal.Quotient.mk (modulus (u*(3*c)))
        ((3*c)*residueRepresentative u v.1+u*residueRepresentative (3*c) v.2) :=
      residueRepresentative_spec _ _
    have hw := cubicThetaEisensteinWeight_congr_of_eq h3uc hq hr
    dsimp only [F,f,g,C]
    rw [hw,cubicThetaEisensteinWeight_mix hu hc hcu]
    change _*residueFourierChar (u*(3*c)) (mul_ne_zero hu0 h3c)
      (Ideal.Quotient.mk (modulus (u*(3*c))) h*residueMix u (3*c) v)=_
    rw [residueFourierChar_mix hu0 h3c]
    ring
  rw [cubicThetaEisensteinGaussCoefficient_fourier_of_eq (mul_ne_zero hu0 hc0)
    (mul_ne_zero hu0 h3c) hq]
  change (∑' x, F x)=C*cubicThetaSymbolFourier u hu0 h*cubicThetaEisensteinGaussCoefficient c h
  rw [← e.tsum_eq]
  simp_rw [hF]
  rw [tsum_fintype,Fintype.sum_prod_type]
  rw [cubicThetaEisensteinGaussCoefficient_fourier hc0]
  change (∑ x : Residues u, ∑ y : Residues (3*c), C*(f x*g y))=
    C*(∑' x : Residues u, f x)*(∑' y : Residues (3*c), g y)
  rw [tsum_fintype,tsum_fintype]
  calc
    _ = ∑ x : Residues u, (C*f x)*(∑ y : Residues (3*c), g y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = (∑ x : Residues u, C*f x)*(∑ y : Residues (3*c), g y) :=
      (Finset.sum_mul ..).symm
    _ = _ := by congr 1; rw [Finset.mul_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRowRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local prime-power recurrences for the genuine arithmetic row coefficient. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_primePower {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0)
    (hcp : IsCoprime c p) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (p^n*c) h=
      (cubicSymbol p (3*c)*cubicSymbol p c)^n*
        cubicThetaLocalPrimePowerGauss p hp.2.ne_zero n h*
          cubicThetaEisensteinGaussCoefficient c h := by
  have hpn : primary (p^n) := by
    induction n with
    | zero => simpa using primary_one
    | succ n ih => simpa only [pow_succ] using primary_mul ih hp.1
  rw [cubicThetaEisensteinGaussCoefficient_factor hpn hc hc0 hcp.pow_right,
    cubicThetaSymbol_prime_pow hp,cubicThetaSymbol_prime_pow hp,← mul_pow]
  rfl

theorem cubicThetaEisensteinGaussCoefficient_prime_unit {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0)
    (hcp : IsCoprime c p) (h : Eisenstein) (hph : IsCoprime p h) :
    cubicThetaEisensteinGaussCoefficient (p*c) h=
      (cubicSymbol p c)^2*star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p*
        cubicThetaEisensteinGaussCoefficient c h := by
  rw [cubicThetaEisensteinGaussCoefficient_factor hp.1 hc hc0 hcp,
    cubicThetaSymbolFourier_prime hp,cubicThetaPrimeFourier_unit hp (by norm_num) h hph,
    pow_one,cubicThetaPrimeFourier_one_one hp,cubicSymbol_mul_upper hp.1]
  have hphase := cubicSymbol_three_lambda hp.1
  rw [cubicSymbol_mul_upper hp.1] at hphase
  calc
    _ = (cubicSymbol p 3*cubicSymbol p lambdaE)*
        ((cubicSymbol p c)^2*star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p*
          cubicThetaEisensteinGaussCoefficient c h) := by ring
    _ = _ := by rw [hphase,one_mul]

theorem cubicThetaEisensteinGaussCoefficient_highPrimePower {p c : Eisenstein}
    (hp : primaryPrime p) (hc : (3:Eisenstein) ∣ c) (hc0 : c≠0)
    (hcp : IsCoprime c p) (n : ℕ) (h : Eisenstein) (hph : ¬p ∣ h) :
    cubicThetaEisensteinGaussCoefficient (p^(n+2)*c) h=0 := by
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp hc hc0 hcp]
  have hpn : ¬p^(n+1) ∣ h := fun hd =>
    hph ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hd)
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+1) h hpn
  rw [show n+2=(n+1)+1 by omega,hz,mul_zero,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-power separation of the original arithmetic Dirichlet
series. Absolute convergence is used only for the iterated sum. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaDenominatorTerm (s : ℂ) (h : Eisenstein) (c : CubicThetaDenominator) : ℂ :=
  cubicThetaEisensteinGaussCoefficient c.val h*(norm c.val:ℂ)^(-s)

def cubicThetaPrimePowerTerm (p : Eisenstein) (hp : primaryPrime p) (s : ℂ) (h : Eisenstein)
    (v : ℕ × CubicThetaPrimeFreeDenominator p) : ℂ :=
  cubicThetaDenominatorTerm s h (cubicThetaPrimePowerDenominator p hp v)

lemma cubicThetaFrequencyDirichlet_denominators (s : ℂ) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=∑' c : CubicThetaDenominator, cubicThetaDenominatorTerm s h c := by
  have hs : Function.support (cubicThetaFrequencyTerm s h) ⊆
      {c : Eisenstein | (3:Eisenstein) ∣ c ∧ c≠0} := by
    intro c hc
    by_contra hp
    change ¬((3:Eisenstein) ∣ c ∧ c≠0) at hp
    exact hc (by rw [cubicThetaFrequencyTerm,ite_eq_right hp])
  rw [cubicThetaFrequencyDirichlet,← tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro c
  have hc : (3:Eisenstein) ∣ c.val ∧ c.val≠0 := c.property
  change cubicThetaFrequencyTerm s h c.val=_
  rw [cubicThetaFrequencyTerm,ite_eq_left hc]
  rfl

lemma cubicThetaDenominatorTerm_summable {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) :
    Summable (cubicThetaDenominatorTerm s h) := by
  have hf := (cubicThetaFrequencyTerm_norm_summable hs h).of_norm.subtype
    (fun c : Eisenstein => (3:Eisenstein) ∣ c ∧ c≠0)
  apply hf.congr
  intro c
  have hc : (3:Eisenstein) ∣ c.val ∧ c.val≠0 := c.property
  change cubicThetaFrequencyTerm s h c.val=_
  rw [cubicThetaFrequencyTerm,ite_eq_left hc]
  rfl

theorem cubicThetaFrequencyDirichlet_primePowers {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=∑' v : ℕ × CubicThetaPrimeFreeDenominator p,
      cubicThetaPrimePowerTerm p hp s h v := by
  rw [cubicThetaFrequencyDirichlet_denominators]
  exact ((cubicThetaPrimePowerDenominatorEquiv p hp).tsum_eq (cubicThetaDenominatorTerm s h)).symm

lemma cubicThetaPrimePowerTerm_summable {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) : Summable (cubicThetaPrimePowerTerm p hp s h) :=
  (cubicThetaDenominatorTerm_summable hs h).comp_injective
    (cubicThetaPrimePowerDenominatorEquiv p hp).injective

theorem cubicThetaFrequencyDirichlet_primePowers_iterated {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=∑' n : ℕ, ∑' d : CubicThetaPrimeFreeDenominator p,
      cubicThetaPrimePowerTerm p hp s h (n,d) := by
  rw [cubicThetaFrequencyDirichlet_primePowers hp]
  exact (cubicThetaPrimePowerTerm_summable hp hs h).tsum_prod

lemma cubicThetaPrimePowerTerm_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s h (n+2,d)=0 := by
  have hcp : IsCoprime d.val p := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+2)*d.val) h*
    (norm (p^(n+2)*d.val):ℂ)^(-s)=0
  rw [cubicThetaEisensteinGaussCoefficient_highPrimePower hp d.property.1 d.property.2.1 hcp n h hh,
    zero_mul]

theorem cubicThetaFrequencyDirichlet_two_terms {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet h s=
      (∑' d : CubicThetaPrimeFreeDenominator p, cubicThetaPrimePowerTerm p hp s h (0,d))+
      ∑' d : CubicThetaPrimeFreeDenominator p, cubicThetaPrimePowerTerm p hp s h (1,d) := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  rw [tsum_eq_sum (s:=({0,1}:Finset ℕ))]
  · simp
  · intro n hn
    have hn2 : 2 ≤ n := by simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn2
    have hz (d : CubicThetaPrimeFreeDenominator p) : cubicThetaPrimePowerTerm p hp s h (2+k,d)=0 := by
      simpa only [add_comm 2 k] using cubicThetaPrimePowerTerm_high hp s h hh k d
    simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeEulerStep
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact first local Euler step for a frequency prime to p. The two
remaining series retain their actual cubic twists on the prime-free rows. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeFreeDirichlet (p : Eisenstein) (s : ℂ) (h : Eisenstein) (j : ℕ) : ℂ :=
  ∑' d : CubicThetaPrimeFreeDenominator p, cubicThetaPrimeFreeTerm p s h j d

lemma cubicThetaPrimePowerTerm_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s h (0,d)=cubicThetaPrimeFreeTerm p s h 0 d := by
  simp [cubicThetaPrimePowerTerm,cubicThetaDenominatorTerm,cubicThetaPrimePowerDenominator,
    cubicThetaPrimeFreeTerm]

lemma cubicThetaPrimePowerTerm_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s h (1,d)=
      cubicThetaPrimeFirstFactor p s h*cubicThetaPrimeFreeTerm p s h 2 d := by
  have hcp : IsCoprime d.val p := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  have hph : IsCoprime p h := hp.2.coprime_iff_not_dvd.mpr hh
  change cubicThetaEisensteinGaussCoefficient (p^1*d.val) h*(norm (p^1*d.val):ℂ)^(-s)=_
  rw [pow_one,cubicThetaEisensteinGaussCoefficient_prime_unit hp d.property.1 d.property.2.1 hcp h hph,
    norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg d.val)]
  unfold cubicThetaPrimeFirstFactor cubicThetaPrimeFreeTerm
  ring

theorem cubicThetaFrequencyDirichlet_primeEulerStep {p : Eisenstein} (hp : primaryPrime p)
    {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet h s=cubicThetaPrimeFreeDirichlet p s h 0+
      cubicThetaPrimeFirstFactor p s h*cubicThetaPrimeFreeDirichlet p s h 2 := by
  rw [cubicThetaFrequencyDirichlet_two_terms hp hs h hh]
  simp_rw [cubicThetaPrimePowerTerm_zero hp,cubicThetaPrimePowerTerm_one hp s h hh]
  rw [tsum_mul_left]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeLocalCases
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact local factors at the first four powers, including zero
frequencies and the cubic return to the first character. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaLocalPrimePowerGauss_prime_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 1 (p*h)=0 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 0 (p*h)
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 1 (p^0*(p*h))=
    (norm (p^0):ℂ)*cubicThetaPrimeFourier p hp 1 (p*h) at he
  rw [cubicThetaPrimeFourier_one_multiple hp,mul_zero] at he
  simpa only [pow_zero,one_mul] using he

lemma cubicThetaLocalPrimePowerGauss_square_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^2*h)=0 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 1 (p*h)
  have hx : p^1*(p*h)=p^2*h := by ring
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^1*(p*h))=
    (norm (p^1):ℂ)*cubicThetaPrimeFourier p hp 2 (p*h) at he
  rw [hx,cubicThetaPrimeFourier_two_multiple hp,mul_zero] at he
  exact he

lemma cubicThetaLocalPrimePowerGauss_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=
      (norm (p^2):ℂ)*(if p ∣ h then (norm p:ℂ)-1 else -1) := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 2 h
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=
    (norm (p^2):ℂ)*cubicThetaPrimeFourier p hp 3 h at he
  rw [he,cubicThetaPrimeFourier_three hp]

lemma cubicThetaLocalPrimePowerGauss_fourth {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 4 (p^3*h)=
      (norm (p^3):ℂ)*cubicThetaPrimeFourier p hp 1 h := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 3 h
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 4 (p^3*h)=
    (norm (p^3):ℂ)*cubicThetaPrimeFourier p hp (1+3) h at he
  rw [he,cubicThetaPrimeFourier_period hp (by norm_num)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five possible local rows at a cubically multiplied frequency. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimeFree_cubeFrequency {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient d.val (p^3*h)=cubicThetaEisensteinGaussCoefficient d.val h := by
  rw [mul_comm (p^3)]
  exact cubicThetaEisensteinGaussCoefficient_cubeFrequency d.property.1 d.property.2.1 hp.1
    (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm h

lemma cubicThetaPrimePowerTerm_cube_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (0,d)=cubicThetaPrimeFreeTerm p s h 0 d := by
  rw [cubicThetaPrimePowerTerm_zero]
  unfold cubicThetaPrimeFreeTerm
  rw [cubicThetaPrimeFree_cubeFrequency hp]

lemma cubicThetaPrimePowerTerm_cube_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (1,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^1*d.val) (p^3*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hz : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 1 (p^3*h)=0 := by
    convert cubicThetaLocalPrimePowerGauss_prime_multiple hp (p^2*h) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  rw [hz,mul_zero,zero_mul,zero_mul]

lemma cubicThetaPrimePowerTerm_cube_two {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (2,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p^3*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hz : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^3*h)=0 := by
    convert cubicThetaLocalPrimePowerGauss_square_multiple hp (p*h) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  rw [hz,mul_zero,zero_mul,zero_mul]

lemma cubicThetaPrimePowerTerm_cube_three {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (3,d)=
      (norm p:ℂ)^2*((norm p:ℂ)-1)*((norm p:ℂ)^(-s))^3*cubicThetaPrimeFreeTerm p s h 0 d := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  have hG : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^3*h)=
      (norm (p^2):ℂ)*((norm p:ℂ)-1) := by
    convert cubicThetaLocalPrimePowerGauss_cube hp (p*h) using 1
    · congr 1; ring
    · rw [ite_eq_left (dvd_mul_right p h)]
  change cubicThetaEisensteinGaussCoefficient (p^3*d.val) (p^3*h)*
    (norm (p^3*d.val):ℂ)^(-s)= _
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaPrimeFree_phaseCube hp,one_mul,hG,cubicThetaPrimeFree_cubeFrequency hp,
    cubicThetaNormPower_cpow,eisenstein_norm_pow,Complex.ofReal_pow]
  unfold cubicThetaPrimeFreeTerm
  simp only [pow_zero,one_mul]
  ring

lemma cubicThetaEisensteinGaussCoefficient_fourth_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient (p^4*d.val) (p^3*h)=
      (norm (p^3):ℂ)*cubicThetaEisensteinGaussCoefficient (p*d.val) h := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    show (4:ℕ)=3+1 by omega,pow_succ,cubicThetaPrimeFree_phaseCube hp,one_mul,
    cubicThetaLocalPrimePowerGauss_fourth hp,cubicThetaPrimeFree_cubeFrequency hp,
    cubicThetaEisensteinGaussCoefficient_factor hp.1 d.property.1 d.property.2.1 hcp,
    cubicThetaSymbolFourier_prime hp]
  ring

lemma cubicThetaPrimePowerTerm_cube_four {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (4,d)=
      (norm p:ℂ)^3*((norm p:ℂ)^(-s))^3*cubicThetaPrimePowerTerm p hp s h (1,d) := by
  change cubicThetaEisensteinGaussCoefficient (p^4*d.val) (p^3*h)*
    (norm (p^4*d.val):ℂ)^(-s)=
    _*(cubicThetaEisensteinGaussCoefficient (p^1*d.val) h*(norm (p^1*d.val):ℂ)^(-s))
  rw [cubicThetaEisensteinGaussCoefficient_fourth_cube hp,cubicThetaNormPower_cpow,
    cubicThetaNormPower_cpow,eisenstein_norm_pow,Complex.ofReal_pow,pow_one]
  ring

lemma cubicThetaPrimePowerTerm_cube_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p^3*h) (n+5,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+5)*d.val) (p^3*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hn : ¬p^(n+4) ∣ p^3*h := by
    intro hdiv
    have h4 : p^4 ∣ p^3*h := (pow_dvd_pow p (by omega : 4 ≤ n+4)).trans hdiv
    rw [show (4:ℕ)=3+1 by omega,pow_succ,mul_dvd_mul_iff_left (pow_ne_zero 3 hp.2.ne_zero)] at h4
    exact hh h4
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+4) (p^3*h) hn
  rw [show n+5=(n+4)+1 by omega,hz,mul_zero,zero_mul,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact cube-index recurrence of the convergent Eisenstein series.
The prime-free term is retained explicitly; no claim about its residue is
made by this initial-half-plane identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaFrequencyDirichlet_five_terms {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^3*h) s=
      ∑ n ∈ Finset.range 5, ∑' d : CubicThetaPrimeFreeDenominator p,
        cubicThetaPrimePowerTerm p hp s (p^3*h) (n,d) := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  apply tsum_eq_sum
  intro n hn
  have hn5 : 5 ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn5
  have hz (d : CubicThetaPrimeFreeDenominator p) :
      cubicThetaPrimePowerTerm p hp s (p^3*h) (5+k,d)=0 := by
    simpa only [add_comm 5 k] using cubicThetaPrimePowerTerm_cube_high hp s h hh k d
  simp only [hz,tsum_zero]

theorem cubicThetaFrequencyDirichlet_cube_recurrence {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^3*h) s=
      (norm p:ℂ)^3*((norm p:ℂ)^(-s))^3*cubicThetaFrequencyDirichlet h s+
      (1-(norm p:ℂ)^2*((norm p:ℂ)^(-s))^3)*cubicThetaPrimeFreeDirichlet p s h 0 := by
  have he := cubicThetaFrequencyDirichlet_two_terms hp hs h hh
  simp_rw [cubicThetaPrimePowerTerm_zero hp] at he
  rw [cubicThetaFrequencyDirichlet_five_terms hp hs h hh]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  simp_rw [cubicThetaPrimePowerTerm_cube_zero hp,cubicThetaPrimePowerTerm_cube_one hp,
    cubicThetaPrimePowerTerm_cube_two hp,cubicThetaPrimePowerTerm_cube_three hp,
    cubicThetaPrimePowerTerm_cube_four hp]
  simp only [tsum_zero,add_zero,tsum_mul_left]
  rw [he]
  unfold cubicThetaPrimeFreeDirichlet
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeShiftRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeFree_primeFrequency {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient d.val (p*h)=
      star (cubicSymbol p d.val)*cubicThetaEisensteinGaussCoefficient d.val h := by
  rw [mul_comm p h]
  exact cubicThetaEisensteinGaussCoefficient_mul d.property.1 d.property.2.1 hp.1
    (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm h

lemma cubicThetaPrimePowerTerm_prime_zero {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (0,d)=cubicThetaPrimeFreeTerm p s h 2 d := by
  rw [cubicThetaPrimePowerTerm_zero]
  unfold cubicThetaPrimeFreeTerm
  rw [pow_zero,one_mul,cubicThetaPrimeFree_primeFrequency hp,cubicSymbol_sq_eq_star hp.1]

lemma cubicThetaPrimePowerTerm_prime_one {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (1,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^1*d.val) (p*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    cubicThetaLocalPrimePowerGauss_prime_multiple hp,mul_zero,zero_mul,zero_mul]

lemma cubicThetaEisensteinGaussCoefficient_second_prime {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h)
    (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p*h)=
      (norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p)*
        cubicThetaEisensteinGaussCoefficient d.val h := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  have hG : cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p*h)=
      (norm p:ℂ)*cubicThetaPrimeFourier p hp 2 h := by
    have he := cubicThetaLocalPrimePowerGauss_reduction hp 1 h
    change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 2 (p^1*h)=
      (norm (p^1):ℂ)*cubicThetaPrimeFourier p hp 2 h at he
    simpa only [pow_one] using he
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp,
    hG,cubicThetaPrimeFourier_two_unit hp h (hp.2.coprime_iff_not_dvd.mpr hh),
    cubicThetaPrimeFourier_one_one hp,cubicThetaPrimeFree_primeFrequency hp]
  have hsqrt : star (Real.sqrt (norm p):ℂ)=(Real.sqrt (norm p):ℂ) := by simp
  simp only [star_mul,hsqrt]
  calc
    _ = ((cubicSymbol p (3*d.val)*cubicSymbol p d.val)^2*
        star (cubicSymbol p lambdaE)*star (cubicSymbol p d.val))*
        ((norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p)*
          cubicThetaEisensteinGaussCoefficient d.val h) := by ring
    _ = _ := by rw [cubicThetaPrimeFree_secondPhase hp,one_mul]

lemma cubicThetaPrimePowerTerm_prime_two {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (2,d)=
      cubicThetaPrimeSecondFactor p s h*cubicThetaPrimeFreeTerm p s h 0 d := by
  change cubicThetaEisensteinGaussCoefficient (p^2*d.val) (p*h)*
    (norm (p^2*d.val):ℂ)^(-s)=_
  rw [cubicThetaEisensteinGaussCoefficient_second_prime hp h hh d,cubicThetaNormPower_cpow]
  unfold cubicThetaPrimeSecondFactor cubicThetaPrimeFreeTerm
  simp only [pow_zero,one_mul]
  ring

lemma cubicThetaPrimePowerTerm_prime_high {p : Eisenstein} (hp : primaryPrime p)
    (s : ℂ) (h : Eisenstein) (hh : ¬p ∣ h) (n : ℕ) (d : CubicThetaPrimeFreeDenominator p) :
    cubicThetaPrimePowerTerm p hp s (p*h) (n+3,d)=0 := by
  have hcp := (hp.2.coprime_iff_not_dvd.mpr d.property.2.2).symm
  change cubicThetaEisensteinGaussCoefficient (p^(n+3)*d.val) (p*h)*_=0
  rw [cubicThetaEisensteinGaussCoefficient_primePower hp d.property.1 d.property.2.1 hcp]
  have hn : ¬p^(n+2) ∣ p*h := by
    intro hd
    have h2 : p^2 ∣ p*h := (pow_dvd_pow p (by omega : 2 ≤ n+2)).trans hd
    have he : p^2=p*p := pow_two p
    rw [he,mul_dvd_mul_iff_left hp.2.ne_zero] at h2
    exact hh h2
  have hz := cubicThetaLocalPrimePowerGauss_eq_zero hp (n+2) (p*h) hn
  rw [show n+3=(n+2)+1 by omega,hz,mul_zero,zero_mul,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeHeckeRelation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaFrequencyDirichlet_primeShift {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p*h) s=cubicThetaPrimeFreeDirichlet p s h 2+
      cubicThetaPrimeSecondFactor p s h*cubicThetaPrimeFreeDirichlet p s h 0 := by
  rw [cubicThetaFrequencyDirichlet_primePowers_iterated hp hs]
  rw [tsum_eq_sum (s:=Finset.range 3)]
  · simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    simp_rw [cubicThetaPrimePowerTerm_prime_zero hp,cubicThetaPrimePowerTerm_prime_one hp,
      cubicThetaPrimePowerTerm_prime_two hp s h hh]
    simp only [tsum_zero,add_zero,tsum_mul_left]
    rfl
  · intro n hn
    have hn3 : 3 ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn3
    have hz (d : CubicThetaPrimeFreeDenominator p) :
        cubicThetaPrimePowerTerm p hp s (p*h) (3+k,d)=0 := by
      simpa only [add_comm 3 k] using cubicThetaPrimePowerTerm_prime_high hp s h hh k d
    simp only [hz,tsum_zero]

theorem cubicThetaFrequencyDirichlet_primeHecke {p : Eisenstein}
    (hp : primaryPrime p) {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaFrequencyDirichlet (p^3*h) s=
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-s))^3)*cubicThetaFrequencyDirichlet h s-
      cubicThetaPrimeFirstFactor p s h*cubicThetaFrequencyDirichlet (p*h) s := by
  rw [cubicThetaFrequencyDirichlet_cube_recurrence hp hs h hh,
    cubicThetaFrequencyDirichlet_primeShift hp hs h hh,
    cubicThetaFrequencyDirichlet_primeEulerStep hp hs h hh]
  have he := cubicThetaPrimeFactors_product hp s h hh
  linear_combination (cubicThetaPrimeFreeDirichlet p s h 0)*he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedIncoming
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaSection_strip_memLp (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (fun p : CubicThetaPoint => F.val p) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  apply (memLp_two_iff_integrable_sq_norm F.val.continuous.aestronglyMeasurable).mpr
  have hn : Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using hF.integrable_norm_pow (by norm_num)
  have hi := hn.integrableOn (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip 2)
  unfold IntegrableOn at hi
  rw [←cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num))] at hi
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using
    hi.comp_measurable cubicThetaQuotientMap_open.continuous.measurable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveHeightBand
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive lower height cutoffs, needed when Hecke dilations move a
compact Poincare profile below the unit cusp height. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaPositiveHeightBand_core {ε H : ℝ} (hε : 0<ε) :
    ∃ S : Finset SL(2,Eisenstein),∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      ε ≤ cubicThetaPointHeight p → cubicThetaPointHeight p≤H →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S (max H ε⁻¹) := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y ≤ max H ε⁻¹ := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le (hp₂.trans (le_max_left _ _))
    simpa only [one_div] using (inv_anti₀ hε hp₁).trans (le_max_right H ε⁻¹)
  have hyc : y.val∈cubicThetaSiegelCore (max H ε⁻¹) := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,cubicThetaQuotient_covering.map_smul k⟩
  change (k • q).val∈cubicThetaCompactCore S (max H ε⁻¹)
  refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
  exact congrArg cubicThetaPointCoordinates hpoint

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierProfile
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaPositiveFourierProfile_core (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ∃ (H : ℝ) (S : Finset SL(2,Eisenstein)),∀ p : CubicThetaPoint,
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S H →
        cubicThetaFourierProfileSeries h p.val W=0 := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  obtain ⟨S,hS⟩ := cubicThetaPositiveHeightBand_core (H:=B) hε
  refine ⟨max B ε⁻¹,S,fun p hp => ?_⟩
  suffices hz : ∀ r,cubicThetaFourierProfileTerm h r p.val W=0 by
    simp only [cubicThetaFourierProfileSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤ε
  · exact cubicThetaFourierProfileTerm_zero h r p.val W (hW _ hlo)
  by_cases hz : W (r.height p.val)=0
  · exact cubicThetaFourierProfileTerm_zero h r p.val W hz
  have hhi : r.height p.val≤B := hB (mem_image_of_mem id (subset_closure hz))
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; exact hhi)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

lemma cubicThetaPositiveFourierProfileSection_compact (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaPositiveFourierProfileSection h W hε hW)) := by
  obtain ⟨H,S,hS⟩ := cubicThetaPositiveFourierProfile_core h W hε hW
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S H)
  intro q hq
  by_contra hn
  have hz := hS (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaFourierProfileSeries h (cubicThetaQuotientLift q).val W‖=0
  rw [hz,norm_zero]

def cubicThetaPositiveFourierProfileL2 (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaPositiveFourierProfileSection h W hε hW)
    (cubicThetaPositiveFourierProfileSection_compact h W hε hW)).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierStripSeed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single half-open strip seed for the full Fourier Poincare sum.
Its translations have exactly one contributing term at every point. -/
noncomputable section
open Set
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaFourierStripSeed (h : Eisenstein) (W : C_c(ℝ,ℂ)) (p : CubicThetaPoint) : ℂ :=
  if p.val.1∈cubicThetaHorizontalCell then W p.val.2*cubicThetaHorizontalCharacter h p.val.1 else 0

lemma cubicThetaFourierStripSeed_translate (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaFourierStripSeed h W (cubicThetaPrincipalTranslation w • p)=
      if p.val.1+3*(w:ℂ)∈cubicThetaHorizontalCell then
        W p.val.2*cubicThetaHorizontalCharacter h p.val.1 else 0 := by
  unfold cubicThetaFourierStripSeed
  have he := cubicThetaPrincipalTranslation_coordinates w p
  change (cubicThetaPrincipalTranslation w • p).val=(p.val.1+3*(w:ℂ),p.val.2) at he
  rw [he,cubicThetaHorizontalCharacter_periodic]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareUnfolding
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unfolding against compact periodized seeds, using the actual
measurable arithmetic fundamental domain and absolute integrability. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators CompactlySupported Pointwise
namespace CubicFirstMoment

lemma cubicThetaFundamental_translates_summable {f : CubicThetaPoint → ℂ}
    (hf : Integrable f cubicThetaPointMeasure) :
    Summable (fun g : cubicThetaPrincipalGroup => ∫ p in cubicThetaFundamentalDomain,
      ‖f (g • p)‖ ∂cubicThetaPointMeasure) := by
  have hD := cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure
  have hsum : Integrable f (Measure.sum (fun g : cubicThetaPrincipalGroup =>
      cubicThetaPointMeasure.restrict (g • cubicThetaFundamentalDomain))) := by
    rwa [hD.sum_restrict]
  apply hsum.summable_integral.congr
  intro g
  exact (measurePreserving_smul g cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g) (fun p => ‖f p‖) cubicThetaFundamentalDomain

lemma cubicThetaFundamental_integral_tsum {f : CubicThetaPoint → ℂ}
    (hf : Integrable f cubicThetaPointMeasure) :
    (∫ p in cubicThetaFundamentalDomain, (∑' g : cubicThetaPrincipalGroup, f (g • p))
      ∂cubicThetaPointMeasure)=∫ p, f p ∂cubicThetaPointMeasure := by
  have hgi (g : cubicThetaPrincipalGroup) :
      IntegrableOn (fun p => f (g • p)) cubicThetaFundamentalDomain cubicThetaPointMeasure :=
    ((measurePreserving_smul g cubicThetaPointMeasure).integrable_comp_of_integrable hf).integrableOn
  calc
    _ = ∑' g : cubicThetaPrincipalGroup, ∫ p in cubicThetaFundamentalDomain,
        f (g • p) ∂cubicThetaPointMeasure :=
      (integral_tsum_of_summable_integral_norm hgi (cubicThetaFundamental_translates_summable hf)).symm
    _ = _ := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integral_eq_tsum'' f hf |>.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierStripSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support and absolute integrability of the half-open Fourier seed
at every positive height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourierStripSeed_compact (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ∃ K : Set CubicThetaPoint,IsCompact K ∧
      Function.support (cubicThetaFourierStripSeed h W)⊆K := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaHorizontalCell_compact_container
  let B := tsupport W ∩ Ici ε
  have hB : IsCompact B := W.hasCompactSupport.inter_right isClosed_Ici
  have hpos : L ×ˢ B⊆{y : ℂ × ℝ | 0<y.2} := fun y hy => lt_of_lt_of_le hε hy.2.2
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  refine ⟨cubicThetaPointInclusion.symm '' (L ×ˢ B),
    (hL.prod hB).image_of_continuousOn (hi.mono hpos),?_⟩
  intro p hp
  have hz : p.val.1∈cubicThetaHorizontalCell := by
    by_contra hn
    exact hp (by simp only [cubicThetaFourierStripSeed,ite_eq_right hn])
  have hw : W p.val.2≠0 := by
    intro hn
    exact hp (by simp only [cubicThetaFourierStripSeed,ite_eq_left hz,hn,zero_mul])
  refine ⟨p.val,⟨hcell hz,subset_tsupport W hw,?_⟩,?_⟩
  · exact (lt_of_not_ge (fun hv => hw (hW _ hv))).le
  · exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

lemma cubicThetaFourierStripSeed_pair_summable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection)
    (p : CubicThetaPoint) :
    Summable (fun g : cubicThetaPrincipalGroup =>
      star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p)) := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  have hs := (cubicTheta_compact_translates_locallyFinite hK).point_finite p
  apply summable_of_ne_finset_zero (s:=hs.toFinset)
  intro g hg
  have hgp : g • p∉K := fun hh => hg (hs.mem_toFinset.mpr hh)
  have hz : cubicThetaFourierStripSeed h W (g • p)=0 :=
    not_not.mp (fun hn => hgp (hsub hn))
  rw [hz,star_zero,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripFubini
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini and radial Fourier pairing at any positive cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveCuspStrip_fubini {ε : ℝ} (hε : 0≤ε) (f : ℂ × ℝ → ℂ)
    (hf : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure) :
    (∫ p in cubicThetaCuspStrip ε,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ v in Ioi ε,∫ z in cubicThetaHorizontalCell,f (z,v)/(v:ℂ)^3 := by
  have hi := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable ε) f).mp hf
  rw [cubicThetaPointIntegral_complex_density (cubicThetaCuspStrip_measurable ε),
    cubicThetaCuspStrip_coordinates hε]
  rw [cubicThetaCuspStrip_coordinates hε] at hi
  change Integrable (fun y : ℂ × ℝ => f y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi
  rw [←Measure.prod_restrict] at hi
  change (∫ y : ℂ × ℝ,f y/(y.2:ℂ)^3 ∂
    ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi ε))=_
  rw [←Measure.prod_restrict]
  exact integral_prod_symm _ hi

lemma cubicThetaFourierStripSeed_pair_on_strip (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (_hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    (∫ p,star (cubicThetaFourierStripSeed h W p)*F.val p ∂cubicThetaPointMeasure)=
      ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val p ∂cubicThetaPointMeasure := by
  have hz : ∀ p∉cubicThetaCuspStrip ε,star (cubicThetaFourierStripSeed h W p)*F.val p=0 := by
    intro p hp
    by_cases hc : p.val.1∈cubicThetaHorizontalCell
    · have hh : p.val.2≤ε := by
        by_contra hn
        exact hp ⟨lt_of_not_ge hn,hc⟩
      simp only [cubicThetaFourierStripSeed,ite_eq_left hc,hW _ hh,zero_mul,star_zero]
    · simp only [cubicThetaFourierStripSeed,ite_eq_right hc,star_zero,zero_mul]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable ε)
  intro p hp
  change ε<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
  simp only [cubicThetaFourierStripSeed,ite_eq_left hp.2]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripRepresentative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPositiveStripRepresentative_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) :
    IntegrableOn (fun y : ℂ × ℝ => cubicThetaPositiveStripRepresentative F y/(y.2:ℂ)^3)
      (cubicThetaHorizontalCell ×ˢ Ioi ε) := by
  have := cubicThetaPositiveStrip_finite hε
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply ((Lp.memLp F).integrable (by norm_num : (1:ℝ≥0∞)≤2)).congr
    filter_upwards with p
    rw [cubicThetaPositiveStripRepresentative_coordinates]
  have he := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable ε)
    (cubicThetaPositiveStripRepresentative F)).mp hi
  rwa [cubicThetaCuspStrip_coordinates hε.le] at he

lemma cubicThetaPositiveStripRepresentative_sq_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaPositiveStripRepresentative F y‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi ε) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      ‖cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p)‖^2)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply ((memLp_two_iff_integrable_sq_norm
      (Lp.stronglyMeasurable F).aestronglyMeasurable).mp (Lp.memLp F)).congr
    filter_upwards with p
    rw [cubicThetaPositiveStripRepresentative_coordinates]
  have he := (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable ε)
    (fun y => ‖cubicThetaPositiveStripRepresentative F y‖^2)).mp hi
  rwa [cubicThetaCuspStrip_coordinates hε.le] at he

lemma cubicThetaPositiveStripRepresentative_pair_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*F p)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaPositiveStripFourierTest hε h W) F
  apply hi.congr
  filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp] with p hp
  change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) (F p)=_
  rw [hp,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripHorizontalDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial tests recover the horizontal Fourier coefficient
of an arbitrary cusp L2 vector at almost every height. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
variable {ε : ℝ}

def cubicThetaPositiveStripHorizontalDensity (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,
    star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
      cubicThetaPositiveStripRepresentative F (z,v)/(v:ℂ)^3

lemma cubicThetaPositiveStripHorizontalDensity_integrable (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein) :
    IntegrableOn (cubicThetaPositiveStripHorizontalDensity F h) (Ioi ε) := by
  have hi := cubicThetaPositiveStripRepresentative_integrable hε F
  change Integrable (fun y : ℂ × ℝ => cubicThetaPositiveStripRepresentative F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi ε)) at hi
  rw [←Measure.prod_restrict] at hi
  have hc : Continuous (fun y : ℂ × ℝ =>
      star (Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ)) := by
    unfold tracePair
    fun_prop
  have hb := hi.bdd_mul hc.aestronglyMeasurable (c:=1)
    (Filter.Eventually.of_forall (fun y => by rw [norm_star]; exact (Circle.norm_coe _).le))
  have he := hb.integral_prod_right
  apply he.congr
  filter_upwards with v
  unfold cubicThetaPositiveStripHorizontalDensity
  apply integral_congr_ae
  filter_upwards with z
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripFourierSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial weights and the actual horizontal characters jointly
separate the literal cusp L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
variable {ε : ℝ}
local instance cubicThetaPositiveStripFourierSeparationCountable : Countable Eisenstein :=
  cubicThetaFourierIndex.injective.countable

lemma cubicThetaPositiveStripRepresentative_fiber_memLp (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) :
    ∀ᵐ v ∂(volume : Measure ℝ).restrict (Ioi ε),
      MemLp (fun z : ℂ => cubicThetaPositiveStripRepresentative F (z,v)) 2
        ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) := by
  have hi := cubicThetaPositiveStripRepresentative_sq_integrable hε F
  change Integrable (fun y : ℂ × ℝ => ‖cubicThetaPositiveStripRepresentative F y‖^2/y.2^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi ε)) at hi
  rw [←Measure.prod_restrict] at hi
  filter_upwards [hi.prod_left_ae,ae_restrict_mem measurableSet_Ioi] with v hv hv2
  have hv0 : v≠0 := (hε.trans hv2).ne'
  have hm : AEStronglyMeasurable (fun z : ℂ => cubicThetaPositiveStripRepresentative F (z,v))
      ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) :=
    ((cubicThetaPositiveStripRepresentative_measurable F).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (hv.mul_const (v^3)).congr
  filter_upwards with z
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPositiveFourierProfileTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaSmoothTests :=
  ⟨cubicThetaPositiveFourierProfileSection h W hε hW,by
    refine ⟨?_,cubicThetaPositiveFourierProfileSection_compact h W hε hW⟩
    apply (cubicThetaPositiveFourierProfile_contDiffOn h W hε hW hsm).congr
    intro y hy
    change cubicThetaFourierProfileSeries h (cubicThetaPointInclusion.symm y).val W=
      cubicThetaFourierProfileSeries h y W
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaFourierProfileSeries h p W) he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary cube coefficients isolated in DR v3 (5.17).
This connects the constructed theta expansion to the completed Gauss sum. -/
noncomputable section
namespace CubicFirstMoment

/-- The source uses `tau(mu)`, while our Whittaker coefficient is
`tau(mu)/|mu|`. -/
def cubicThetaTau (n : Eisenstein) : ℂ :=
  (‖cubicThetaFrequency n‖:ℂ)*cubicThetaArithmeticCoefficient n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullEisensteinFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaFullTorus (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  cubicThetaArithmeticTorus v s+(v:ℂ)^s • cubicThetaTorusFourier 0

attribute [local instance] OAI.CubicFirstMoment.cubicThetaFullEisensteinFourierMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaFullEisensteinFourierProbability
lemma cubicThetaFullTorus_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaFullTorus v s)) h=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaNonzeroFrequencyTerm (0,v) s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaFullTorus v s)=_
  rw [cubicThetaFullTorus,map_add,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusCoefficientMap_apply,smul_eq_mul]
  rw [cubicThetaArithmeticTorus_coefficient hv hs hh,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficient_basis,ite_eq_right hh,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootHorizontal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRootHorizontal_translate {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) (x : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeRootHorizontal (cubicThetaPrimeCubeRootSectionTranslate hp x F) v hv z=
      cubicThetaPrimeRootHorizontal F v hv (z+3*(x:ℂ)/((p^3:Eisenstein):ℂ)) := by
  change F.val (cubicThetaPrimeCubeRootElement hp x • cubicThetaHorizontalPoint v hv z)=
    F.val (cubicThetaHorizontalPoint v hv (z+3*(x:ℂ)/((p^3:Eisenstein):ℂ)))
  congr 1
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeCubeRootElement hp x) (z,v)=_
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaMobius_translation]
  push_cast
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaHighWindowTest (s : ℂ) : cubicThetaSmoothTests :=
  ⟨cubicThetaHighWindowSection s,by
    refine ⟨?_,cubicThetaHighWindowSection_compact s⟩
    apply (cubicThetaHighWindowSeries_smooth s).congr
    intro y hy
    change cubicThetaHighWindowSeries (cubicThetaPointInclusion.symm y).val s=
      cubicThetaHighWindowSeries y s
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaHighWindowSeries p s) he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal inverted cusp restriction extends continuously from
finite-energy sections and agrees with inversion on the energy completion. -/
noncomputable section
namespace CubicFirstMoment
local instance instAddCommGroupSubtypeContinuousMapCubicThetaPointComplexMemSubmoduleCubicThetaSectionCubicThetaFiniteEnergySections : AddCommGroup cubicThetaFiniteEnergySections := Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedRowInflation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaEisensteinGaussCoefficient_ramified_inflation {u : Eisenstein}
    (hu : primary u) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)*u) (lambdaE^n*h)=
      (norm (lambdaE^n):ℂ)*
        cubicThetaRamifiedBaseRow u (primary_ne_zero hu) ((n+2)%3) h := by
  let q : Eisenstein := 3*(lambdaE^(n+2)*u)
  let d : Eisenstein := 3*lambdaE^2*u
  have hq : q≠0 := mul_ne_zero (by norm_num)
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (primary_ne_zero hu))
  have hd : d≠0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero _ lambdaE_prime.ne_zero)) (primary_ne_zero hu)
  have he : q=d*lambdaE^n := by
    dsimp only [q,d]
    rw [pow_add]
    ring
  have hdq : d ∣ q := ⟨lambdaE^n,he⟩
  have hw (x : Residues q) :
      cubicThetaEisensteinWeight (lambdaE^(n+2)*u) (residueRepresentative q x)=
      cubicThetaEisensteinWeight (lambdaE^((n+2)%3)*u)
        (residueRepresentative d (residueReduction hdq x)) := by
    rw [cubicThetaEisensteinWeight_ramified_mod hu]
    apply cubicThetaEisensteinWeight_ramified_congr hu
    have hr : Ideal.Quotient.mk (modulus d) (residueRepresentative q x)=
        Ideal.Quotient.mk (modulus d)
          (residueRepresentative d (residueReduction hdq x)) := by
      rw [residueRepresentative_spec]
      have ht := congrArg (residueReduction hdq) (residueRepresentative_spec q x)
      simpa only [residueReduction_mk] using ht
    have hdiv := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (show
        Ideal.Quotient.mk (modulus d)
          (residueRepresentative q x-residueRepresentative d (residueReduction hdq x))=0 by
          rw [map_sub,hr,sub_self]))
    have hde : d= -(9*u) := by dsimp only [d]; rw [lambdaE_sq]; ring
    have hb : 9*u ∣ d := ⟨-1,by rw [hde]; ring⟩
    exact hb.trans hdiv
  rw [cubicThetaEisensteinGaussCoefficient_fourier_of_eq
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (primary_ne_zero hu)) hq rfl]
  simp_rw [hw]
  exact residueFourier_inflation_of_eq hq hd (pow_ne_zero _ lambdaE_prime.ne_zero)
    he hdq (fun x => cubicThetaEisensteinWeight (lambdaE^((n+2)%3)*u)
      (residueRepresentative d x)) h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedRowValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaEisensteinGaussCoefficient_ramified_value (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)) (lambdaE^n*h)=
      (norm (lambdaE^n):ℂ)*
        (if (3:Eisenstein) ∣ -h+2*(((n+2)%3:ℕ):Eisenstein) then
          9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) (-h))
        else 0) := by
  have he := cubicThetaEisensteinGaussCoefficient_ramified_inflation primary_one n h
  simpa only [mul_one,cubicThetaRamifiedBaseRow_one,cubicThetaRamifiedNineGauss_eq] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unit/ramified/primary separation of the actual Dirichlet series.
Reordering uses its already proved absolute convergence on Re(s)>2. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedTerm (s : ℂ) (h : Eisenstein)
    (v : Eisensteinˣ × ℕ × CubicThetaPrimaryPart) : ℂ :=
  cubicThetaDenominatorTerm s h (cubicThetaRamifiedDenominator v)

theorem cubicThetaFrequencyDirichlet_ramified (s : ℂ) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=
      ∑' v : Eisensteinˣ × ℕ × CubicThetaPrimaryPart, cubicThetaRamifiedTerm s h v := by
  rw [cubicThetaFrequencyDirichlet_denominators]
  exact (cubicThetaRamifiedDenominatorEquiv.tsum_eq (cubicThetaDenominatorTerm s h)).symm

lemma cubicThetaRamifiedTerm_summable {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) :
    Summable (cubicThetaRamifiedTerm s h) :=
  (cubicThetaDenominatorTerm_summable hs h).comp_injective
    cubicThetaRamifiedDenominatorEquiv.injective

theorem cubicThetaFrequencyDirichlet_ramified_iterated {s : ℂ} (hs : 2 < s.re)
    (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=
      ∑' u : Eisensteinˣ, ∑' n : ℕ, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (u,n,a) := by
  rw [cubicThetaFrequencyDirichlet_ramified]
  have hf := cubicThetaRamifiedTerm_summable hs h
  rw [hf.tsum_prod]
  apply tsum_congr
  intro u
  exact (hf.prod_factor u).tsum_prod

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaEisensteinGaussCoefficient_full_ramified_support (e : Eisensteinˣ)
    {u : Eisenstein} (hu : primary u) (n : ℕ) (h : Eisenstein)
    (hG : cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u) h≠0) :
    lambdaE^n ∣ h := by
  let c : Eisenstein := (e:Eisenstein)*lambdaE^(n+2)*u
  have hc : c≠0 := mul_ne_zero (mul_ne_zero e.ne_zero
    (pow_ne_zero _ lambdaE_prime.ne_zero)) (primary_ne_zero hu)
  have hq : (3:Eisenstein)*c≠0 := mul_ne_zero (by norm_num) hc
  let : Finite (Residues (3*c)) := finite_residues hq
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3 : (3:Eisenstein)∣c := by
    refine ⟨-(e:Eisenstein)*lambdaE^n*u,?_⟩
    dsimp only [c]
    rw [pow_add,lambdaE_sq]
    ring
  have hf (x b : Residues (3*c)) :
      cubicThetaEisensteinResidueWeight c (x+Ideal.Quotient.mk (modulus (3*c)) (9*u)*b)=
      cubicThetaEisensteinResidueWeight c x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul,← map_add,cubicThetaEisensteinResidueWeight_mk h3,
      cubicThetaEisensteinResidueWeight_mk h3]
    exact cubicThetaEisensteinWeight_full_ramified_periodic e hu (n+2) a b
  have hd : 3*c ∣ (9*u)*h := by
    apply residueFourier_reduction_support hq (cubicThetaEisensteinResidueWeight c) h hf
    change cubicThetaEisensteinGaussCoefficient c h≠0 at hG
    rw [cubicThetaEisensteinGaussCoefficient_fourier hc] at hG
    simpa only [cubicThetaEisensteinResidueWeight,tsum_fintype] using hG
  have he : 3*c=(9*u)*(-(e:Eisenstein)*lambdaE^n) := by
    dsimp only [c]
    rw [pow_add,lambdaE_sq]
    ring
  rw [he,mul_dvd_mul_iff_left (mul_ne_zero (by norm_num) (primary_ne_zero hu))] at hd
  exact (dvd_mul_left (lambdaE^n) (-(e:Eisenstein))).trans hd

theorem cubicThetaRamifiedTerm_high (s : ℂ) (h : Eisenstein)
    (e : Eisensteinˣ) (n : ℕ) (u : CubicThetaPrimaryPart) (hn : ¬lambdaE^n ∣ h) :
    cubicThetaRamifiedTerm s h (e,n,u)=0 := by
  have hz : cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u.val) h=0 := by
    by_contra he
    exact hn (cubicThetaEisensteinGaussCoefficient_full_ramified_support e u.property n h he)
  change cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u.val) h*
    (norm ((e:Eisenstein)*lambdaE^(n+2)*u.val):ℂ)^(-s)=0
  rw [hz,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero frequency leaves only finitely many ramified powers in
the actual Dirichlet series, uniformly over the unit and primary part. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaFrequencyDirichlet_ramified_finite {s : ℂ} (hs : 2 < s.re)
    (h : Eisenstein) (M : ℕ) (hM : ∀ n : ℕ, M ≤ n → ¬lambdaE^n ∣ h) :
    cubicThetaFrequencyDirichlet h s=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range M, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (e,n,a) := by
  rw [cubicThetaFrequencyDirichlet_ramified_iterated hs]
  apply tsum_congr
  intro e
  apply tsum_eq_sum
  intro n hn
  have hmn : M ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
  have hz (a : CubicThetaPrimaryPart) : cubicThetaRamifiedTerm s h (e,n,a)=0 :=
    cubicThetaRamifiedTerm_high s h e n a (hM n hmn)
  simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimaryFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the primary part of every actual ramified row. Reciprocity
reduces its correction to one explicit finite character squared. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_ramified_primary (e : Eisensteinˣ)
    {u : Eisenstein} (hu : primary u) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*u) h=
      (cubicSymbol u (e:Eisenstein)*(cubicSymbol u lambdaE)^n)^2*
        cubicThetaSymbolFourier u (primary_ne_zero hu) h*
          cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) h := by
  have hc : (3:Eisenstein) ∣ (e:Eisenstein)*lambdaE^(n+2) := by
    refine ⟨-(e:Eisenstein)*lambdaE^n,?_⟩
    rw [pow_add,lambdaE_sq]
    ring
  have hc0 : (e:Eisenstein)*lambdaE^(n+2)≠0 :=
    mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have hunit : IsCoprime (e:Eisenstein) u := ⟨(e⁻¹:Eisensteinˣ),0,by simp⟩
  have hcu : IsCoprime ((e:Eisenstein)*lambdaE^(n+2)) u :=
    hunit.mul_left ((primary_coprime_lambda hu).symm.pow_left)
  rw [mul_comm ((e:Eisenstein)*lambdaE^(n+2)) u,
    cubicThetaEisensteinGaussCoefficient_factor hu hc hc0 hcu,
    cubicThetaRamifiedPrimaryPhase e hu]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimarySeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaRamifiedFactor (e : Eisensteinˣ) (n : ℕ) (s : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) h*
    (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ)^(-s)

theorem cubicThetaRamifiedTerm_factor (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) :
    cubicThetaRamifiedTerm s h (e,n,a)=
      cubicThetaRamifiedFactor e n s h*cubicThetaPrimaryFourierTerm e n s h a := by
  change cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)*a.val) h*
    (norm ((e:Eisenstein)*lambdaE^(n+2)*a.val):ℂ)^(-s)=_
  rw [cubicThetaEisensteinGaussCoefficient_ramified_primary e a.property,
    norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  unfold cubicThetaRamifiedFactor cubicThetaPrimaryFourierTerm
  ring

theorem cubicThetaFrequencyDirichlet_primary_finite {s : ℂ} (hs : 2 < s.re)
    (h : Eisenstein) (M : ℕ) (hM : ∀ n : ℕ, M ≤ n → ¬lambdaE^n ∣ h) :
    cubicThetaFrequencyDirichlet h s=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range M,
        cubicThetaRamifiedFactor e n s h*cubicThetaPrimaryFourierSeries e n s h := by
  rw [cubicThetaFrequencyDirichlet_ramified_finite hs h M hM]
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [cubicThetaRamifiedTerm_factor]
  rw [tsum_mul_left]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaSymbolFourier_zero_noncube {c : Eisenstein} (hc : primary c)
    (hcb : ¬∃ j : Eisenstein, j^3=c) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) 0=0 := by
  obtain ⟨u,hu,hcu,hchi⟩ :=
    (cubicNumeratorChar_ne_one_iff cubicSupplementaryPeriodicity_proved c
      (primary_ne_zero hc)).mp
      (cubicNumeratorChar_noncube cubicSupplementaryPeriodicity_proved (primary_ne_zero hc) hcb)
  have hχ : cubicSymbol c u≠1 := by rwa [cubic_reciprocity hc hu]
  have hs : star (cubicSymbol c u)≠1 := by
    intro he
    apply hχ
    have ht := congrArg star he
    simpa only [star_star,star_one] using ht
  have he := cubicThetaSymbolFourier_mul hc hcu.of_mul_left_right 0
  simp only [zero_mul] at he
  exact eq_zero_of_mul_eq_self_left hs he.symm

theorem cubicThetaInvertedConstantGauss_eq {c : Eisenstein} (hc : primary c) :
    cubicThetaInvertedConstantGauss c=
      if ∃ j : Eisenstein, j^3=c then (Nat.card (Residues c)ˣ:ℂ) else 0 := by
  have he : cubicThetaInvertedConstantGauss c=
      cubicSymbol c 3*cubicThetaSymbolFourier c (primary_ne_zero hc) 0 := by
    unfold cubicThetaInvertedConstantGauss cubicThetaSymbolFourier
    simp_rw [cubicSymbol_mul_upper hc]
    simp only [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one,tsum_mul_left]
  rw [he]
  split_ifs with hcb
  · rw [cubicThetaSymbolFourier_zero_cube hc hcb,cubicThetaSymbol_primary_cube hc hcb,
      ite_eq_left (primary_coprime_three hc),one_mul]
  · rw [cubicThetaSymbolFourier_zero_noncube hc hcb,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ideal reindexing and Euler factor of the inverted-cusp
constant coefficient, derived from its actual finite character sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaInvertedConstantWeight_support (s : ℂ) :
    Function.support (cubicThetaInvertedConstantWeight s) ⊆
      {c : Eisenstein | primary c ∧ ∃ j : Eisenstein, j^3=c} := by
  intro c hc
  by_cases hp : primary c
  · refine ⟨hp,?_⟩
    by_contra hcb
    exact hc (by simp [cubicThetaInvertedConstantWeight,hp,
      cubicThetaInvertedConstantGauss_eq hp,hcb])
  · exact False.elim (hc (by simp [cubicThetaInvertedConstantWeight,hp]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitInflation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inflation of a ramified row with its global unit retained. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation
    (e : Eisensteinˣ) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) (lambdaE^n*h)=
      (norm (lambdaE^n):ℂ)*cubicThetaUnitRamifiedBase e ((n+2)%3) h := by
  let q : Eisenstein := 3*((e:Eisenstein)*lambdaE^(n+2))
  let d : Eisenstein := 3*(e:Eisenstein)*lambdaE^2
  have hq : q≠0 := mul_ne_zero (by norm_num)
    (mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))
  have hd : d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) e.ne_zero)
    (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he : q=d*lambdaE^n := by dsimp only [q,d]; rw [pow_add]; ring
  have hdq : d ∣ q := ⟨lambdaE^n,he⟩
  have h9d : (9:Eisenstein) ∣ d := by
    refine ⟨-(e:Eisenstein),?_⟩
    dsimp only [d]
    rw [lambdaE_sq]
    ring
  have hw (x : Residues q) :
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^(n+2)) (residueRepresentative q x)=
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^((n+2)%3))
        (residueRepresentative d (residueReduction hdq x)) := by
    rw [cubicThetaEisensteinWeight_unit_lambda_mod]
    apply cubicThetaEisensteinWeight_unit_lambda_congr
    have hr : Ideal.Quotient.mk (modulus d) (residueRepresentative q x)=
        Ideal.Quotient.mk (modulus d)
          (residueRepresentative d (residueReduction hdq x)) := by
      rw [residueRepresentative_spec]
      have ht := congrArg (residueReduction hdq) (residueRepresentative_spec q x)
      simpa only [residueReduction_mk] using ht
    apply h9d.trans
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hr
  rw [cubicThetaEisensteinGaussCoefficient_fourier_of_eq
    (mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)) hq rfl]
  simp_rw [hw]
  exact residueFourier_inflation_of_eq hq hd (pow_ne_zero _ lambdaE_prime.ne_zero)
    he hdq (fun x => cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^((n+2)%3))
      (residueRepresentative d x)) h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedAllRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit finite ramified factor for all six global units. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_all_ramified
    (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) (lambdaE^n*h)=
      (3:ℂ)^n*(if (3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
          2*(((n+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) then
        9*residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)) else 0) := by
  rw [cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation,
    cubicThetaUnitRamifiedBase_value e (r:ℕ) ((n+2)%3) he,
    cubicThetaRamifiedUnitNineGauss_eq,cubicThetaNorm_lambda_pow]
  push_cast
  rfl

theorem cubicThetaRamifiedFactor_value (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (n : ℕ) (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedFactor e n s (lambdaE^n*h)=
      ((3:ℂ)^n*(if (3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
          2*(((n+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) then
        9*residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)) else 0))*
        ((3:ℂ)^(n+2))^(-s) := by
  rw [cubicThetaRamifiedFactor,cubicThetaEisensteinGaussCoefficient_all_ramified e r he,
    cubicThetaNorm_unit_lambda_pow]
  push_cast
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitCube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic inflation with every unit retained, and its exact factor in the
convergent ramified/primary decomposition. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_unit_ramified_cube
    (e : Eisensteinˣ) (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+5)) (lambdaE^3*h)=
      27*cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(n+2)) h := by
  by_cases hd : lambdaE^n ∣ h
  · obtain ⟨t,rfl⟩ := hd
    have hp : lambdaE^3*(lambdaE^n*t)=lambdaE^(n+3)*t := by rw [pow_add]; ring
    rw [hp,show n+5=(n+3)+2 by omega,
      cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation,
      cubicThetaEisensteinGaussCoefficient_unit_ramified_inflation]
    have hm : (n+3+2)%3=(n+2)%3 := by omega
    rw [hm,cubicThetaNorm_lambda_pow,cubicThetaNorm_lambda_pow,pow_add]
    push_cast
    ring
  · have hn : ¬lambdaE^(n+3) ∣ lambdaE^3*h := by
      intro hx
      have hp : lambdaE^(n+3)=lambdaE^3*lambdaE^n := by rw [pow_add]; ring
      rw [hp,mul_dvd_mul_iff_left (pow_ne_zero _ lambdaE_prime.ne_zero)] at hx
      exact hd hx
    have hz (k : ℕ) (t : Eisenstein) (hk : ¬lambdaE^k ∣ t) :
        cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^(k+2)) t=0 := by
      by_contra he
      apply hk
      simpa only [mul_one] using
        cubicThetaEisensteinGaussCoefficient_full_ramified_support e primary_one k t
          (by simpa only [mul_one] using he)
    rw [show n+5=(n+3)+2 by omega,hz (n+3) _ hn,hz n _ hd,mul_zero]

theorem cubicThetaRamifiedFactor_cube (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) :
    cubicThetaRamifiedFactor e (n+3) s (lambdaE^3*h)=
      (27*(27:ℂ)^(-s))*cubicThetaRamifiedFactor e n s h := by
  unfold cubicThetaRamifiedFactor
  rw [show n+3+2=n+5 by omega,
    cubicThetaEisensteinGaussCoefficient_unit_ramified_cube,
    cubicThetaNorm_unit_lambda_pow,cubicThetaNorm_unit_lambda_pow]
  have hp : (3:ℝ)^(n+5)=(27:ℝ)*3^(n+2) := by
    rw [show n+5=3+(n+2) by omega,pow_add]
    norm_num
  rw [hp,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
  push_cast
  ring

theorem cubicThetaRamifiedTerm_cube (e : Eisensteinˣ) (n : ℕ) (s : ℂ)
    (h : Eisenstein) (a : CubicThetaPrimaryPart) :
    cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n+3,a)=
      (27*(27:ℂ)^(-s))*cubicThetaRamifiedTerm s h (e,n,a) := by
  rw [cubicThetaRamifiedTerm_factor,cubicThetaRamifiedTerm_factor,
    cubicThetaRamifiedFactor_cube,cubicThetaPrimaryFourierTerm_cube,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedDirichletCube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ramified cube step with its three low rows retained.
Their residues must be determined; this identity does not assume that they
vanish or that the full residue is cube-periodic. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaRamifiedLowDirichlet (s : ℂ) (h : Eisenstein) : ℂ :=
  ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range 3, ∑' a : CubicThetaPrimaryPart,
    cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n,a)

theorem cubicThetaFrequencyDirichlet_ramified_cube {s : ℂ} (hs : 2 < s.re)
    (h : Eisenstein) :
    cubicThetaFrequencyDirichlet (lambdaE^3*h) s=
      cubicThetaRamifiedLowDirichlet s h+
        (27*(27:ℂ)^(-s))*cubicThetaFrequencyDirichlet h s := by
  let : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  have hf := cubicThetaRamifiedTerm_summable hs (lambdaE^3*h)
  have hrow (e : Eisensteinˣ) :
      (∑' n : ℕ, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n,a))=
      (∑ n ∈ Finset.range 3, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n,a))+
      (27*(27:ℂ)^(-s))*(∑' n : ℕ, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (e,n,a)) := by
    rw [← (hf.prod_factor e).prod.sum_add_tsum_nat_add 3]
    simp_rw [cubicThetaRamifiedTerm_cube]
    simp_rw [tsum_mul_left]
  rw [cubicThetaFrequencyDirichlet_ramified_iterated hs,
    cubicThetaFrequencyDirichlet_ramified_iterated hs]
  simp_rw [hrow]
  rw [Summable.tsum_add Summable.of_finite Summable.of_finite,tsum_mul_left]
  rfl

theorem cubicThetaRamifiedLowDirichlet_primary (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedLowDirichlet s h=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range 3,
        cubicThetaRamifiedFactor e n s (lambdaE^3*h)*
          cubicThetaPrimaryFourierSeries e n s h := by
  unfold cubicThetaRamifiedLowDirichlet
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [cubicThetaRamifiedTerm_factor]
  rw [tsum_mul_left]
  change cubicThetaRamifiedFactor e n s (lambdaE^3*h)*
      cubicThetaPrimaryFourierSeries e n s (lambdaE^3*h)=_
  rw [cubicThetaPrimaryFourierSeries_lambda_cube]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMissingClass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first missing ramified valuation class vanishes already in the
convergent Eisenstein series. The argument retains all six unit classes. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_ramified_zero_row
    (e : Eisensteinˣ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^2) (lambdaE*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
      2*(((0+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    have hk := lambda_dvd_three.trans hd
    have hz : lambdaE ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
        lambdaE*(r:ℕ) := ⟨-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ),by ring⟩
    apply lambda_not_dvd_four
    convert dvd_sub hk hz using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  simpa only [pow_zero,one_mul,ite_eq_right hn,mul_zero] using
    cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 0 (lambdaE*h)

theorem cubicThetaEisensteinGaussCoefficient_ramified_one_row
    (e : Eisensteinˣ) {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
      2*(((1+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    have hk := lambda_dvd_three.trans hd
    norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero] at hk
    have hz : lambdaE ∣ lambdaE*(r:ℕ) := dvd_mul_right _ _
    have hp : lambdaE ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h := by
      simpa only [add_sub_cancel_right] using dvd_sub hk hz
    rcases hp with ⟨t,ht⟩
    apply hh
    refine ⟨-(e:Eisenstein)*t,?_⟩
    have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
    linear_combination -(e:Eisenstein)*ht-h*hi
  simpa only [pow_one,ite_eq_right hn,mul_zero] using
    cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 1 h

theorem cubicThetaFrequencyDirichlet_lambda_missing {s : ℂ} (hs : 2 < s.re)
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaFrequencyDirichlet (lambdaE*h) s=0 := by
  have hM : ∀ n : ℕ, 2 ≤ n → ¬lambdaE^n ∣ lambdaE*h := by
    intro n hn hd
    have hp : lambdaE^2 ∣ lambdaE*h := (pow_dvd_pow lambdaE hn).trans hd
    rw [pow_two,mul_dvd_mul_iff_left lambdaE_prime.ne_zero] at hp
    exact hh hp
  rw [cubicThetaFrequencyDirichlet_primary_finite hs (lambdaE*h) 2 hM]
  have hz (e : Eisensteinˣ) :
      ∑ n ∈ Finset.range 2, cubicThetaRamifiedFactor e n s (lambdaE*h)*
        cubicThetaPrimaryFourierSeries e n s (lambdaE*h)=0 := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      cubicThetaRamifiedFactor,cubicThetaEisensteinGaussCoefficient_ramified_zero_row,
      cubicThetaEisensteinGaussCoefficient_ramified_one_row e hh,zero_mul,add_zero]
  simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedLowRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only the middle of the three retained low rows can contribute to
the cubic step. Its coefficient is still the actual finite Gauss sum. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_ramified_two_row
    (e : Eisensteinˣ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^4) (lambdaE^3*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
      2*(((2+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    have h3 : lambdaE ∣ (3:Eisenstein) := by
      refine ⟨-lambdaE,?_⟩
      rw [mul_neg,← pow_two,lambdaE_sq]
      ring
    have hz : lambdaE ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+
        lambdaE*(r:ℕ) := ⟨-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ),by ring⟩
    have ht : lambdaE ∣ (2:Eisenstein) := by
      convert dvd_sub (h3.trans hd) hz using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    exact lambdaE_prime.not_isUnit
      ((primary_coprime_lambda primary_neg_two).isRelPrime (dvd_neg.mpr ht) dvd_rfl)
  have he := cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 2 (lambdaE*h)
  have hp : lambdaE^2*(lambdaE*h)=lambdaE^3*h := by ring
  simpa only [hp,ite_eq_right hn,mul_zero] using he

theorem cubicThetaRamifiedLowDirichlet_middle (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedLowDirichlet s h=
      ∑' e : Eisensteinˣ,
        cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)*
          (27:ℂ)^(-s)*cubicThetaPrimaryFourierSeries e 1 s h := by
  rw [cubicThetaRamifiedLowDirichlet_primary]
  apply tsum_congr
  intro e
  have hz0 : cubicThetaRamifiedFactor e 0 s (lambdaE^3*h)=0 := by
    unfold cubicThetaRamifiedFactor
    rw [show lambdaE^3*h=lambdaE*(lambdaE^2*h) by ring,
      cubicThetaEisensteinGaussCoefficient_ramified_zero_row,zero_mul]
  have hz2 : cubicThetaRamifiedFactor e 2 s (lambdaE^3*h)=0 := by
    unfold cubicThetaRamifiedFactor
    rw [cubicThetaEisensteinGaussCoefficient_ramified_two_row,zero_mul]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,hz0,hz2,
    zero_mul,add_zero]
  unfold cubicThetaRamifiedFactor
  rw [cubicThetaNorm_unit_lambda_pow]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMiddleValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two unit classes which survive in the middle ramified row. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_middle_one (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^3) (lambdaE^3*h)=
      27*residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h) := by
  have he := cubicThetaEisensteinGaussCoefficient_ramified_value 1 (lambdaE^2*h)
  have hp : lambdaE*(lambdaE^2*h)=lambdaE^3*h := by ring
  have hx : -(lambdaE^2*h)=3*h := by rw [lambdaE_sq]; ring
  have hd : (3:Eisenstein) ∣ 3*h := dvd_mul_right _ _
  have hφ := cubicThetaFourier_nine_triple h 1
  simp only [mul_one] at hφ
  norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero,
    pow_one,cubicThetaNorm_lambda_pow] at he
  rw [hp,hx,ite_eq_left hd,hφ] at he
  have hn : norm lambdaE=3 := by simpa only [pow_one] using cubicThetaNorm_lambda_pow 1
  rw [hn] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

theorem cubicThetaEisensteinGaussCoefficient_middle_neg_one (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (-lambdaE^3) (lambdaE^3*h)=
      27*residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (-h)) := by
  have h3 : (3:Eisenstein) ∣ lambdaE^3 := by
    refine ⟨-lambdaE,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  have he := cubicThetaEisensteinGaussCoefficient_neg h3
    (pow_ne_zero _ lambdaE_prime.ne_zero) (-(lambdaE^3*h))
  rw [neg_neg] at he
  rw [he,show -(lambdaE^3*h)=lambdaE^3*(-h) by ring,
    cubicThetaEisensteinGaussCoefficient_middle_one]

theorem cubicThetaEisensteinGaussCoefficient_middle_other (e : Eisensteinˣ)
    (hpos : e≠1) (hneg : e≠-1) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hr0 : (r:ℕ)≠0 := by
    intro hz
    simp only [hz,pow_zero] at hr
    rcases hr with hr | hr
    · exact hpos (Units.ext hr)
    · exact hneg (Units.ext hr)
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE^2*h)+
      2*(((1+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero] at hd
    have ht : (3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE^2*h) := by
      refine ⟨((e⁻¹:Eisensteinˣ):Eisenstein)*h,?_⟩
      rw [lambdaE_sq]
      ring
    have hd' : (3:Eisenstein) ∣ lambdaE*(r:ℕ) := by
      simpa only [add_sub_cancel_left] using dvd_sub hd ht
    obtain ⟨a,ha⟩ := hd'
    have hlam : lambdaE ∣ ((r:ℕ):Eisenstein) := by
      refine ⟨-a,?_⟩
      apply mul_left_cancel₀ lambdaE_prime.ne_zero
      calc
        lambdaE*(r:ℕ)=3*a := ha
        _ = lambdaE*(lambdaE*(-a)) := by
          have hs := lambdaE_sq
          linear_combination a*hs
    fin_cases r
    · exact hr0 rfl
    · have hu : lambdaE ∣ (1:Eisenstein) := by simpa using hlam
      exact lambdaE_prime.not_isUnit (isUnit_of_dvd_one hu)
    · exact lambdaE_prime.not_isUnit
        ((primary_coprime_lambda primary_neg_two).isRelPrime (dvd_neg.mpr hlam) dvd_rfl)
  have he := cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 1 (lambdaE^2*h)
  simpa only [pow_one,show lambdaE*(lambdaE^2*h)=lambdaE^3*h by ring,
    ite_eq_right hn,mul_zero] using he

theorem cubicThetaEisensteinGaussCoefficient_middle (e : Eisensteinˣ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)=
      if e=1 then 27*residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) h)
      else if e=-1 then 27*residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (-h)) else 0 := by
  split_ifs with hp hn
  · subst e
    simpa only [Units.val_one,one_mul] using cubicThetaEisensteinGaussCoefficient_middle_one h
  · subst e
    simpa only [Units.val_neg,Units.val_one,neg_one_mul] using
      cubicThetaEisensteinGaussCoefficient_middle_neg_one h
  · exact cubicThetaEisensteinGaussCoefficient_middle_other e hp hn h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedLowFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaRamifiedLowDirichlet_factor (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedLowDirichlet s h=
      cubicThetaRamifiedCubeFactor s*cubicThetaRamifiedTrace h*
        cubicThetaPrimaryFourierSeries 1 1 s h := by
  let : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  rw [cubicThetaRamifiedLowDirichlet_middle]
  have he (e : Eisensteinˣ) :
      cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)*
          (27:ℂ)^(-s)*cubicThetaPrimaryFourierSeries e 1 s h=
      (if e=1 then (27*residueFourierChar 3 (by norm_num)
          (Ideal.Quotient.mk (modulus 3) h))*(27:ℂ)^(-s)*
          cubicThetaPrimaryFourierSeries 1 1 s h else 0)+
      (if e=-1 then (27*residueFourierChar 3 (by norm_num)
          (Ideal.Quotient.mk (modulus 3) (-h)))*(27:ℂ)^(-s)*
          cubicThetaPrimaryFourierSeries 1 1 s h else 0) := by
    rw [cubicThetaEisensteinGaussCoefficient_middle]
    by_cases hp : e=1
    · subst e
      norm_num
    · by_cases hn : e=-1
      · subst e
        simp only [ite_eq_right hp,ite_true, if_true,cubicThetaPrimaryFourierSeries_neg_one,zero_add]
      · simp only [ite_eq_right hp,ite_eq_right hn,zero_mul,add_zero]
  simp_rw [he]
  rw [Summable.tsum_add Summable.of_finite Summable.of_finite]
  simp only [tsum_ite_eq]
  unfold cubicThetaRamifiedCubeFactor cubicThetaRamifiedTrace
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInvertedRowRadius_summable {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun a : Eisenstein => ‖cubicSymbol c (3*a)‖*
      (cubicThetaRowRadius c p (3*a))^(-s.re)) := by
  have hi : Function.Injective (fun a : Eisenstein => (c,3*a)) := by
    intro a b h
    exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) (Prod.mk.inj h).2
  have hr := (cubicThetaInvertedGrid_summable hp hs).norm.comp_injective hi
  have ht := hr.mul_left ((norm c/p.2)^s.re)
  have hc0 := primary_ne_zero hc
  apply ht.congr
  intro a
  dsimp only [Function.comp_apply]
  have hpos : 0<p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2) := by
    rw [←cubicThetaRowRadius_scale hc0]
    exact div_pos hp (mul_pos (norm_pos_of_ne_zero hc0) (cubicThetaRowRadius_pos c (3*a) hp))
  have he : cubicThetaInvertedGridTerm (c,3*a) p s=
      cubicSymbol c (3*a)*
        ((p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2):ℝ):ℂ)^s := by
    unfold cubicThetaInvertedGridTerm
    by_cases hcop : IsCoprime c (3*a)
    · rw [ite_eq_left ⟨hc,⟨a,rfl⟩,hcop⟩]
    · rw [ite_eq_right (by intro h; exact hcop h.2.2),
        cubicSymbol_eq_zero_of_not_isCoprime hc hcop,zero_mul]
  rw [he,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    cubicThetaRowRadius_power hc0 hp]
  ring

theorem cubicThetaInvertedRow_mellin {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaInvertedRowSeries c p s=
      ((p.2/norm c:ℝ):ℂ)^s*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(Real.exp (-p.2^2*t):ℂ)*
          cubicThetaInvertedGaussianRow c p.1 t := by
  have hscale : cubicThetaInvertedRowSeries c p s=
      ((p.2/norm c:ℝ):ℂ)^s*∑' a : Eisenstein,
        cubicSymbol c (3*a)*(cubicThetaRowRadius c p (3*a):ℂ)^(-s) := by
    unfold cubicThetaInvertedRowSeries
    rw [←tsum_mul_left]
    apply tsum_congr
    intro a
    rw [cubicThetaRowRadius_complex_power (primary_ne_zero hc) hp]
    ring
  have hM := cubicTheta_laplace_tsum (fun a => cubicSymbol c (3*a))
    (fun a => cubicThetaRowRadius c p (3*a)) (fun a => cubicThetaRowRadius_pos c (3*a) hp)
    (show 0 < s.re by linarith) (cubicThetaInvertedRowRadius_summable hc hp hs)
  rw [hscale,mul_left_comm,hM]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  unfold cubicThetaInvertedGaussianRow
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro a
  have he : Real.exp (-cubicThetaRowRadius c p (3*a)*t)=
      Real.exp (-p.2^2*t)*Real.exp (-t*‖p.1+3*(a:ℂ)/(c:ℂ)‖^2) := by
    rw [←Real.exp_add]
    congr 1
    unfold cubicThetaRowRadius
    rw [Complex.normSq_eq_norm_sq]
    change -(‖p.1+3*(a:ℂ)/(c:ℂ)‖^2+p.2^2)*t=_
    ring
  rw [he,Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInvertedWeightedHeat_summable {v : ℝ} (hv : 0<v) {s : ℂ}
    (hs : 1 < s.re) {c : Eisenstein} (hc : primary c) (z : ℂ) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaInvertedRowFourierCoefficient c z h*
        cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  have ht := (cubicThetaDualHeat_mass_summable hv hs).mul_left (Nat.card (Residues c):ℝ)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    simp_rw [cubicThetaInvertedRowFourierCoefficient,norm_mul,Circle.norm_coe,mul_one]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaInvertedGaussCoefficient_norm hc h)
      (integral_nonneg (fun _ => _root_.norm_nonneg _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInvertedFrequency_heat_norm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun ch : Eisenstein × Eisenstein =>
      ‖cubicThetaInvertedFrequencyTerm s ch.2 ch.1*
        (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency ch.2)):ℂ)*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale ch.2) t)‖) := by
  have hc := (summable_eisenstein_norm_rpow (show 1 < s.re-1 by linarith)).mul_left 9
  have hh := cubicThetaDualHeat_mass_summable hp (show 1 < s.re by linarith)
  have hprod : Summable (fun ch : Eisenstein × Eisenstein =>
      (9*(norm ch.1)^(-(s.re-1)))*
        (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale ch.2) t‖)) :=
    summable_mul_of_summable_norm hc.norm hh.norm
  apply hprod.of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ch
  rw [norm_mul,norm_mul,Circle.norm_coe,mul_one]
  exact mul_le_mul (cubicThetaInvertedFrequencyTerm_bound s ch.2 ch.1)
    (norm_integral_le_integral_norm _) (_root_.norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInvertedFourierCoefficients_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun h : Eisenstein => cubicThetaInvertedFrequencyDirichlet h s*
      (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)) := by
  have h := (cubicThetaInvertedFrequency_heat_norm_summable hp hs).of_norm.prod_symm.prod
  apply h.congr
  intro n
  dsimp only [Prod.swap]
  rw [tsum_mul_right,tsum_mul_right,cubicThetaInvertedFrequencyDirichlet_tsum]

lemma cubicThetaInvertedNonzeroTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) : Summable (cubicThetaInvertedNonzeroTerm p s) := by
  apply (cubicThetaInvertedFourierCoefficients_summable hp hs).norm.of_norm_bounded
  intro h
  by_cases hh : h=0
  · simp only [cubicThetaInvertedNonzeroTerm,ite_eq_left hh,norm_zero]
    exact _root_.norm_nonneg _
  · simp only [cubicThetaInvertedNonzeroTerm,ite_eq_right hh,le_refl]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedTorusRemainder (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein, cubicThetaInvertedNonzeroTerm (0,v) s h • cubicThetaTorusFourier h

lemma cubicThetaInvertedTorusRemainder_summable {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun h : Eisenstein =>
      cubicThetaInvertedNonzeroTerm (0,v) s h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  have he := (cubicThetaInvertedNonzeroTerm_summable (p:=(0,v)) hv hs).norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using he

lemma cubicThetaInvertedTorusRemainder_real {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (x : Fin 2 → ℝ) :
    cubicThetaInvertedTorusRemainder v s (fun i => (x i:UnitAddCircle))=
      ∑' h : Eisenstein, cubicThetaInvertedNonzeroTerm (cubicThetaPeriodCell x,v) s h := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaInvertedTorusRemainder_summable hv hs)
  change cubicThetaInvertedTorusRemainder v s (fun i => (x i:UnitAddCircle))=_ at he
  rw [he]
  apply tsum_congr
  intro h
  change cubicThetaInvertedNonzeroTerm (0,v) s h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaInvertedNonzeroTerm_phase]

attribute [local instance] OAI.CubicFirstMoment.cubicThetaInvertedTorusMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaInvertedTorusProbability
lemma cubicThetaInvertedTorusRemainder_coefficient {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ
      (cubicThetaInvertedTorusRemainder v s)) k=cubicThetaInvertedNonzeroTerm (0,v) s k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaInvertedTorusRemainder v s)=_
  rw [cubicThetaInvertedTorusRemainder,L.map_tsum (cubicThetaInvertedTorusRemainder_summable hv hs)]
  rw [tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

def cubicThetaInvertedTorus (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  cubicThetaInvertedConstantMode v s • cubicThetaTorusFourier 0+
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s) •
      cubicThetaInvertedTorusRemainder v s

lemma cubicThetaInvertedTorus_mean {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaInvertedTorus v s)) 0=
      cubicThetaInvertedConstantMode v s := by
  let L := (cubicThetaTorusCoefficientMap 0).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaInvertedTorus v s)=_
  rw [cubicThetaInvertedTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,
    cubicThetaInvertedTorusRemainder_coefficient hv hs,cubicThetaInvertedNonzeroTerm,
    smul_eq_mul,mul_one,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero Fourier observations at the inverted cusp retain the exact
primary Dirichlet coefficient and the original radial normalization. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_5
attribute [local instance] OAI.CubicFirstMoment.instIsProbabilityMeasureUnitAddCircleVolume_solutions_1
lemma cubicThetaInvertedTorus_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaInvertedTorus v s)) h=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaInvertedNonzeroTerm (0,v) s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaInvertedTorus v s)=_
  rw [cubicThetaInvertedTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
    ite_eq_right hh,cubicThetaInvertedTorusRemainder_coefficient hv hs,smul_eq_mul,mul_zero,zero_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResidueSystem
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal three-row ramified expansion at the actual theta pole.
All unit twists are retained as frequencies of the same arithmetic residue. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace CubicFirstMoment

instance instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
instance instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 : Fintype Eisensteinˣ := Fintype.ofFinite _

lemma cubicThetaRamifiedFactor_analytic (e : Eisensteinˣ) (n : ℕ)
    (h : Eisenstein) (s : ℂ) :
    AnalyticAt ℂ (fun z => cubicThetaRamifiedFactor e n z h) s := by
  have hN : (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero
      (mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))).ne'
  let _ : NeZero (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ) := ⟨hN⟩
  exact analyticAt_const.mul
    (((differentiable_const_cpow_of_neZero (norm ((e:Eisenstein)*lambdaE^(n+2)):ℂ)).analyticAt _).comp
      (f:=fun z : ℂ => -z) (x:=s) analyticAt_id.neg)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMiddleSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exactly two unit classes can contribute to the middle ramified row
above a frequency congruent to one modulo lambda. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRamifiedMiddleFactor_eq (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (h : Eisenstein) :
    cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)=
      if (3:Eisenstein)∣lambdaE*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ)) then
        (1/3:ℂ)*residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)))
      else 0 := by
  have hp : (27:ℂ)^(-(4/3:ℂ))=1/81 := by
    have ht := cubicThetaRamifiedCubeFactor_pole
    unfold cubicThetaRamifiedCubeFactor at ht
    linear_combination (1/27:ℂ)*ht
  have hv := cubicThetaRamifiedFactor_value e r he 1 (4/3) (lambdaE*h)
  simp only [pow_one] at hv
  rw [show lambdaE^2*h=lambdaE*(lambdaE*h) by ring,hv]
  norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero,pow_one]
  rw [hp]
  have hc : -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE*h)+lambdaE*(r:ℕ)=
      lambdaE*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ)) := by ring
  rw [hc]
  split_ifs <;> ring

lemma cubicThetaRamifiedMiddleFactor_norm_le (e : Eisensteinˣ) (h : Eisenstein) :
    ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖≤1/3 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  rw [cubicThetaRamifiedMiddleFactor_eq e r hr h]
  split_ifs
  · rw [norm_mul,residueFourierChar_mk]
    norm_num [Circle.norm_coe]
  · norm_num

theorem cubicThetaRamifiedMiddleFactor_support (e : Eisensteinˣ) {h : Eisenstein}
    (hh : lambdaE∣h-1)
    (hne : cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)≠0) :
    e=cubicThetaOmegaUnit ∨ e=-(cubicThetaOmegaUnit^2) := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hc : (3:Eisenstein)∣lambdaE*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+(r:ℕ)) := by
    by_contra hc
    rw [cubicThetaRamifiedMiddleFactor_eq e r hr h,ite_eq_right hc] at hne
    exact hne rfl
  have hd := (cubicThetaThree_dvd_lambda_mul _).mp hc
  have hE : lambdaE∣(e:Eisenstein)*(r:ℕ)-1 := by
    have hm := dvd_mul_of_dvd_right hd (e:Eisenstein)
    have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
    have ht : lambdaE∣-h+(e:Eisenstein)*(r:ℕ) := by
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      linear_combination h*hi
    convert dvd_add ht hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h1 : ¬lambdaE∣(1:Eisenstein) :=
    fun hd => lambdaE_prime.not_isUnit (isUnit_of_dvd_one hd)
  have h2 : ¬lambdaE∣(-2:Eisenstein) := fun hd =>
    lambdaE_prime.not_isUnit ((primary_coprime_lambda primary_neg_two).isRelPrime hd dvd_rfl)
  rcases hr with hr | hr
  · have hu : lambdaE∣(e:Eisenstein)-1 := by
      rw [hr]
      exact cubicThetaLambda_dvd_omega_pow_sub_one r
    have ht : lambdaE∣(r:ℕ)-1 := by
      convert dvd_sub hE (dvd_mul_of_dvd_left hu (r:ℕ)) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    fin_cases r
    · have ht' : lambdaE∣(-1:Eisenstein) := by simpa using ht
      exact (h1 (by simpa using dvd_neg.mp ht')).elim
    · exact Or.inl (Units.ext (by simpa [cubicThetaOmegaUnit] using hr))
    · exact (h1 (by norm_num at ht ⊢; exact ht)).elim
  · have hu : lambdaE∣(e:Eisenstein)+1 := by
      rw [hr]
      convert dvd_neg.mpr (cubicThetaLambda_dvd_omega_pow_sub_one r) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have ht : lambdaE∣-(r:ℕ)-1 := by
      convert dvd_sub hE (dvd_mul_of_dvd_left hu (r:ℕ)) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    fin_cases r
    · have ht' : lambdaE∣(-1:Eisenstein) := by simpa using ht
      exact (h1 (by simpa using dvd_neg.mp ht')).elim
    · exact (h2 (by norm_num at ht ⊢; exact ht)).elim
    · exact Or.inr (Units.ext (by simpa [cubicThetaOmegaUnit] using hr))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedContraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
instance instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 : Fintype Eisensteinˣ := Fintype.ofFinite _

lemma cubicThetaRamifiedFactor_neg (e : Eisensteinˣ) (h : Eisenstein) (s : ℂ) :
    cubicThetaRamifiedFactor e 1 s (-h)=cubicThetaRamifiedFactor (-e) 1 s h := by
  have h3 : (3:Eisenstein)∣(e:Eisenstein)*lambdaE^3 := by
    refine ⟨-(e:Eisenstein)*lambdaE,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  have h0 : (e:Eisenstein)*lambdaE^3≠0 :=
    mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he := cubicThetaEisensteinGaussCoefficient_neg h3 h0 (-h)
  rw [neg_neg] at he
  unfold cubicThetaRamifiedFactor
  norm_num only [Nat.reduceAdd]
  rw [cubicThetaNorm_unit_lambda_pow,cubicThetaNorm_unit_lambda_pow]
  rw [Units.val_neg,neg_mul,he]

lemma cubicThetaRamifiedMiddle_sum_norm_pos {h : Eisenstein} (hh : lambdaE∣h-1) :
    (∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖)≤2/3 := by
  rw [tsum_fintype]
  have hb (e : Eisensteinˣ) :
      ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖≤
        (if e=cubicThetaOmegaUnit then (1/3:ℝ) else 0)+
        (if e=-(cubicThetaOmegaUnit^2) then (1/3:ℝ) else 0) := by
    by_cases he : e=cubicThetaOmegaUnit
    · rw [ite_eq_left he]
      exact (cubicThetaRamifiedMiddleFactor_norm_le e h).trans (le_add_of_nonneg_right (by positivity))
    by_cases he' : e=-(cubicThetaOmegaUnit^2)
    · rw [ite_eq_left he',ite_eq_right he,zero_add]
      exact cubicThetaRamifiedMiddleFactor_norm_le e h
    · have hz : cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)=0 := by
        by_contra hz
        exact (cubicThetaRamifiedMiddleFactor_support e hh hz).elim he he'
      simp only [hz,norm_zero,ite_eq_right he,ite_eq_right he',add_zero,le_refl]
  calc
    _ ≤ ∑ e : Eisensteinˣ, ((if e=cubicThetaOmegaUnit then (1/3:ℝ) else 0)+
        (if e=-(cubicThetaOmegaUnit^2) then (1/3:ℝ) else 0)) :=
      Finset.sum_le_sum (fun e _ => hb e)
    _ = 2/3 := by rw [Finset.sum_add_distrib]; simp; norm_num

lemma cubicThetaRamifiedMiddle_sum_norm {h : Eisenstein}
    (hh : lambdaE∣h-1 ∨ lambdaE∣h+1) :
    (∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)‖)≤2/3 := by
  rcases hh with hh | hh
  · exact cubicThetaRamifiedMiddle_sum_norm_pos hh
  · have hn : lambdaE∣(-h)-1 := by
      convert dvd_neg.mpr hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    calc
      _ = ∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor (-e) 1 (4/3) (lambdaE^2*h)‖ :=
        ((Equiv.neg Eisensteinˣ).tsum_eq _).symm
      _ = ∑' e : Eisensteinˣ, ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(-h))‖ := by
        apply tsum_congr
        intro e
        rw [show lambdaE^2*(-h)=-(lambdaE^2*h) by ring,cubicThetaRamifiedFactor_neg]
      _ ≤ 2/3 := cubicThetaRamifiedMiddle_sum_norm_pos hn

theorem cubicThetaRamifiedUnitSystem_unique {h : Eisenstein} (hh : lambdaE∣h-1)
    (b f g : Eisensteinˣ → ℂ)
    (hf : ∀ d, f d=(∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*f (d*e))+b d)
    (hg : ∀ d, g d=(∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*g (d*e))+b d) : f=g := by
  let v (d : Eisensteinˣ) := f d-g d
  have hv (d : Eisensteinˣ) : v d=∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*v (d*e) := by
    dsimp only [v]
    rw [hf d,hg d,add_sub_add_right_eq_sub,←Summable.tsum_sub Summable.of_finite Summable.of_finite]
    apply tsum_congr
    intro e
    ring
  obtain ⟨d,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset Eisensteinˣ)
    (fun e => ‖v e‖) Finset.univ_nonempty
  have hn : ‖v d‖≤(2/3:ℝ)*‖v d‖ := by
    calc
      ‖v d‖ = ‖∑ e : Eisensteinˣ,
          cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*v (d*e)‖ := by
        rw [hv d,tsum_fintype]
      _ ≤ ∑ e : Eisensteinˣ,
          ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))*v (d*e)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ e : Eisensteinˣ,
          ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))‖*‖v d‖ := by
        apply Finset.sum_le_sum
        intro e _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmax (d*e) (Finset.mem_univ _)) (_root_.norm_nonneg _)
      _ = (∑' e : Eisensteinˣ,
          ‖cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*(d:Eisenstein)))‖)*‖v d‖ := by
        rw [tsum_fintype,Finset.sum_mul]
      _ ≤ (2/3:ℝ)*‖v d‖ := mul_le_mul_of_nonneg_right
        (cubicThetaRamifiedMiddle_sum_norm (cubicThetaUnitOrbit_lambda_class hh d)) (_root_.norm_nonneg _)
  have hz : ‖v d‖=0 := by have hp := _root_.norm_nonneg (v d); linarith
  funext e
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have he := hmax e (Finset.mem_univ _)
  change ‖f e-g e‖≤‖v d‖ at he
  rw [hz] at he
  exact le_antisymm he (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimarySupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from lambda, the literal frequency series is supported on the
two signed primary classes. This is a finite ramified selection rule. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_primary_support
    (e : Eisensteinˣ) (h : Eisenstein)
    (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^2) h=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*h+
      2*(((0+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_ofNat] at hd
    have hm : (3:Eisenstein) ∣ -h+(e:Eisenstein)*(4+lambdaE*(r:ℕ)) := by
      have ht := dvd_mul_of_dvd_right hd (e:Eisenstein)
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
      linear_combination h*hi
    rcases hr with he | he
    · have hc : (3:Eisenstein) ∣ (e:Eisenstein)*(4+lambdaE*(r:ℕ))-1 := by
        rw [he]
        exact unit_ramified_primary_congruence r
      apply hpos
      change (3:Eisenstein) ∣ h-1
      convert dvd_add (dvd_neg.mpr hm) hc using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · have hc : (3:Eisenstein) ∣ (e:Eisenstein)*(4+lambdaE*(r:ℕ))+1 := by
        rw [he]
        convert dvd_neg.mpr (unit_ramified_primary_congruence r) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      apply hneg
      change (3:Eisenstein) ∣ -h-1
      convert dvd_sub hm hc using 1
      all_goals try with_reducible_and_instances rfl
      ring
  simpa only [pow_zero,one_mul,ite_eq_right hn] using
    cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 0 h

theorem cubicThetaFrequencyDirichlet_primary_support {s : ℂ} (hs : 2 < s.re)
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaFrequencyDirichlet h s=0 := by
  have hM : ∀ n : ℕ, 1 ≤ n → ¬lambdaE^n ∣ h := by
    intro n hn hd
    exact hh ((pow_one lambdaE ▸ pow_dvd_pow lambdaE hn).trans hd)
  rw [cubicThetaFrequencyDirichlet_primary_finite hs h 1 hM]
  have hz (e : Eisensteinˣ) :
      ∑ n ∈ Finset.range 1, cubicThetaRamifiedFactor e n s h*
        cubicThetaPrimaryFourierSeries e n s h=0 := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      cubicThetaRamifiedFactor,cubicThetaEisensteinGaussCoefficient_primary_support e h hpos hneg,
      zero_mul]
  simp only [hz,tsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPhaseRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact phase of each of the two nonzero middle ramified rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRamifiedMiddle_first {h : Eisenstein} (hh : lambdaE∣h-1) :
    cubicThetaRamifiedFactor cubicThetaOmegaUnit 1 (4/3) (lambdaE^2*h)=
      (1/3:ℂ)*cubicThetaNinePhase (-omegaE^2*lambdaE*h) := by
  have ht : lambdaE∣omegaE^2*h-1 := by
    convert dvd_add (dvd_mul_of_dvd_left (cubicThetaLambda_dvd_omega_pow_sub_one 2) h) hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc : (3:Eisenstein)∣lambdaE*(-omegaE^2*h+1) :=
    (cubicThetaThree_dvd_lambda_mul _).mpr (by
      convert dvd_neg.mpr ht using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  rw [cubicThetaRamifiedMiddleFactor_eq cubicThetaOmegaUnit (1:Fin 3)
    (Or.inl (by norm_num [cubicThetaOmegaUnit])) h,cubicThetaOmegaUnit_inverse_value]
  norm_num only [Fin.val_one,Nat.cast_one]
  rw [ite_eq_left hc]
  congr 2
  ring_nf

lemma cubicThetaRamifiedMiddle_second {h : Eisenstein} (hh : lambdaE∣h-1) :
    cubicThetaRamifiedFactor (-(cubicThetaOmegaUnit^2)) 1 (4/3) (lambdaE^2*h)=
      (1/3:ℂ)*cubicThetaNinePhase (omegaE*lambdaE*h) := by
  have hi : (((-(cubicThetaOmegaUnit^2))⁻¹:Eisensteinˣ):Eisenstein)=-omegaE := by
    rw [inv_neg,Units.val_neg,cubicThetaOmegaUnit_square_inverse_value]
  have ht : lambdaE∣omegaE*h-1 := by
    convert dvd_add (dvd_mul_of_dvd_left (cubicThetaLambda_dvd_omega_pow_sub_one 1) h) hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc : (3:Eisenstein)∣lambdaE*(omegaE*h+2) :=
    (cubicThetaThree_dvd_lambda_mul _).mpr (by
      convert dvd_add ht cubicThetaLambda_dvd_three using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  rw [cubicThetaRamifiedMiddleFactor_eq (-(cubicThetaOmegaUnit^2)) (2:Fin 3)
    (Or.inr (by norm_num [Units.val_pow_eq_pow_val,cubicThetaOmegaUnit])) h,hi]
  norm_num only [Fin.val_two,Nat.cast_ofNat,neg_neg]
  rw [ite_eq_left hc]
  congr 2
  ring_nf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTopRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale of the top surviving ramified row at the theta pole. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRamifiedTopFactor_eq (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (h : Eisenstein) :
    cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*h)=
      if (3:Eisenstein)∣-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+2+lambdaE*(r:ℕ) then
        ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*
          cubicThetaNinePhase (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)
      else 0 := by
  rw [cubicThetaRamifiedFactor_value e r he 2 (4/3) h]
  norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_one,mul_one]
  change (9*(if (3:Eisenstein)∣-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+2+lambdaE*(r:ℕ) then
    9*cubicThetaNinePhase (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h) else 0))*
      (81:ℂ)^(-(4/3:ℂ))=_
  split_ifs
  · calc
      _ = ((81:ℂ)*(81:ℂ)^(-(4/3:ℂ)))*
          cubicThetaNinePhase (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h) := by ring
      _ = _ := by rw [cubicThetaRamifiedTopScale]
  · ring

lemma cubicThetaRamifiedTopFactor_positive_zero (e : Eisensteinˣ) {h : Eisenstein}
    (hh : lambdaE∣h-1) (he : lambdaE∣(e:Eisenstein)-1) :
    cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  rw [cubicThetaRamifiedTopFactor_eq e r hr h]
  apply ite_eq_right
  intro hd
  have h3 : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by rw [mul_neg,←pow_two,lambdaE_sq]; ring⟩
  have ht := dvd_mul_of_dvd_right (h3.trans hd) (e:Eisenstein)
  have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
  have hu : lambdaE∣-h+2*(e:Eisenstein) := by
    have heq : (e:Eisenstein)*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+2+lambdaE*(r:ℕ))=
        -h+2*(e:Eisenstein)+lambdaE*((e:Eisenstein)*(r:ℕ)) := by
      linear_combination -h*hi
    rw [heq] at ht
    convert dvd_sub ht (dvd_mul_right lambdaE ((e:Eisenstein)*(r:ℕ))) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h1 : lambdaE∣(1:Eisenstein) := by
    convert dvd_sub (dvd_add hu hh) (dvd_mul_of_dvd_right he (2:Eisenstein)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact lambdaE_prime.not_isUnit (isUnit_of_dvd_one h1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTopPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaRamifiedTop_negative_inverse {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    cubicThetaRamifiedFactor (-(cubicThetaOmegaUnit^(j:ℕ))⁻¹) 2 (4/3)
      (lambdaE^2*(h*omegaE^(j:ℕ)))=
        ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  let d : Eisensteinˣ := cubicThetaOmegaUnit^(j:ℕ)
  have hd : (d:Eisenstein)=omegaE^(j:ℕ) := by
    simp only [d,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne]
  have hiU : (-(d⁻¹))⁻¹=-d := by rw [inv_neg,inv_inv]
  have hi := congrArg (fun u : Eisensteinˣ => (u:Eisenstein)) hiU
  simp only [Units.val_neg] at hi
  have hc : (3:Eisenstein)∣(omegaE^(j:ℕ))^2*h+2+lambdaE*(cubicThetaInverseUnitIndex j:ℕ) := by
    have hm := dvd_mul_of_dvd_right hh ((omegaE^(j:ℕ))^2)
    convert dvd_add hm (cubicThetaTopUnit_congruence j) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [cubicThetaRamifiedTopFactor_eq (-(d⁻¹)) (cubicThetaInverseUnitIndex j)
    (Or.inr (cubicThetaNegativeInverseUnit_power j)) (h*omegaE^(j:ℕ)),hi,hd,neg_neg]
  have he : omegaE^(j:ℕ)*(h*omegaE^(j:ℕ))=(omegaE^(j:ℕ))^2*h := by ring
  rw [he,ite_eq_left hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPhaseEigen
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit modulus-nine phase is an eigenvector of the actual
middle-row operator, with eigenvalue two thirds. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaRamifiedMiddle_phase_eigen {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    (∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
        cubicThetaNinePhase ((omegaE^(j:ℕ)*(e:Eisenstein))^2*h))=
      (2/3:ℂ)*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  let : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  let F (e : Eisensteinˣ) :=
    cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*(e:Eisenstein))^2*h)
  have hclass := cubicThetaLambda_dvd_primary_omega_sub_one hh j
  have hfirst : F cubicThetaOmegaUnit=(1/3:ℂ)*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
    dsimp only [F]
    rw [cubicThetaRamifiedMiddle_first hclass]
    change ((1/3:ℂ)*cubicThetaNinePhase (-omegaE^2*lambdaE*(h*omegaE^(j:ℕ))))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*omegaE)^2*h)=_
    rw [mul_assoc,cubicThetaNinePhase_middle_first hh j]
  have hsecond : F (-(cubicThetaOmegaUnit^2))=
      (1/3:ℂ)*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
    dsimp only [F]
    rw [cubicThetaRamifiedMiddle_second hclass]
    change ((1/3:ℂ)*cubicThetaNinePhase (omegaE*lambdaE*(h*omegaE^(j:ℕ))))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*(-omegaE^2))^2*h)=_
    rw [mul_assoc,cubicThetaNinePhase_middle_second hh j]
  have hzero (e : Eisensteinˣ) (he : e≠cubicThetaOmegaUnit)
      (he' : e≠-(cubicThetaOmegaUnit^2)) : F e=0 := by
    have hz : cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))=0 := by
      by_contra hz
      exact (cubicThetaRamifiedMiddleFactor_support e hclass hz).elim he he'
    dsimp only [F]
    rw [hz,zero_mul]
  have hpoint (e : Eisensteinˣ) : F e=
      (if e=cubicThetaOmegaUnit then F cubicThetaOmegaUnit else 0)+
      (if e=-(cubicThetaOmegaUnit^2) then F (-(cubicThetaOmegaUnit^2)) else 0) := by
    by_cases he : e=cubicThetaOmegaUnit
    · subst e
      simp only [ite_true, if_true,ite_eq_right cubicThetaOmegaUnit_distinct,add_zero]
    by_cases he' : e=-(cubicThetaOmegaUnit^2)
    · subst e
      simp only [ite_eq_right he,ite_true, if_true,zero_add]
    · rw [hzero e he he',ite_eq_right he,ite_eq_right he',zero_add]
  change (∑' e : Eisensteinˣ, F e)=_
  rw [show (∑' e : Eisensteinˣ, F e)=∑' e : Eisensteinˣ,
      ((if e=cubicThetaOmegaUnit then F cubicThetaOmegaUnit else 0)+
       (if e=-(cubicThetaOmegaUnit^2) then F (-(cubicThetaOmegaUnit^2)) else 0)) from
    tsum_congr hpoint]
  rw [Summable.tsum_add Summable.of_finite Summable.of_finite]
  simp only [tsum_ite_eq,hfirst,hsecond]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sign symmetry of the literal finite ramified operators. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaRamifiedFactor_neg_all (e : Eisensteinˣ) (n : ℕ) (h : Eisenstein) (s : ℂ) :
    cubicThetaRamifiedFactor e n s (-h)=cubicThetaRamifiedFactor (-e) n s h := by
  have h3 : (3:Eisenstein)∣(e:Eisenstein)*lambdaE^(n+2) := by
    refine ⟨-(e:Eisenstein)*lambdaE^n,?_⟩
    rw [pow_add,lambdaE_sq]
    ring
  have h0 : (e:Eisenstein)*lambdaE^(n+2)≠0 :=
    mul_ne_zero e.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he := cubicThetaEisensteinGaussCoefficient_neg h3 h0 (-h)
  rw [neg_neg] at he
  unfold cubicThetaRamifiedFactor
  rw [cubicThetaNorm_unit_lambda_pow,cubicThetaNorm_unit_lambda_pow]
  rw [Units.val_neg,neg_mul,he]

def cubicThetaRamifiedUnitOperator (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (d : Eisensteinˣ) : ℂ :=
  ∑' e : Eisensteinˣ, cubicThetaRamifiedFactor e n (4/3) (lambdaE^2*(h*(d:Eisenstein)))*g (d*e)

lemma cubicThetaRamifiedUnitOperator_neg (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (d : Eisensteinˣ) :
    cubicThetaRamifiedUnitOperator n h g (-d)=cubicThetaRamifiedUnitOperator n h g d := by
  unfold cubicThetaRamifiedUnitOperator
  rw [←(Equiv.neg Eisensteinˣ).tsum_eq]
  apply tsum_congr
  intro e
  simp only [Equiv.neg_apply,Units.val_neg,neg_mul]
  rw [show lambdaE^2*(h*(-(d:Eisenstein)))=-(lambdaE^2*(h*(d:Eisenstein))) by ring,
    cubicThetaRamifiedFactor_neg_all,neg_neg]
  congr 1
  simp

lemma cubicThetaRamifiedUnitOperator_mul_right (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (a : ℂ) (d : Eisensteinˣ) :
    cubicThetaRamifiedUnitOperator n h (fun e => g e*a) d=
      cubicThetaRamifiedUnitOperator n h g d*a := by
  unfold cubicThetaRamifiedUnitOperator
  simp_rw [←mul_assoc]
  rw [tsum_mul_right]

lemma cubicThetaRamifiedUnitOperator_mul_left (n : ℕ) (h : Eisenstein)
    (g : Eisensteinˣ → ℂ) (a : ℂ) (d : Eisensteinˣ) :
    cubicThetaRamifiedUnitOperator n h (fun e => a*g e) d=
      a*cubicThetaRamifiedUnitOperator n h g d := by
  unfold cubicThetaRamifiedUnitOperator
  simp_rw [show ∀ e : Eisensteinˣ,
      cubicThetaRamifiedFactor e n (4/3) (lambdaE^2*(h*(d:Eisenstein)))*(a*g (d*e))=
      a*(cubicThetaRamifiedFactor e n (4/3) (lambdaE^2*(h*(d:Eisenstein)))*g (d*e)) from
    fun _ => by ring]
  rw [tsum_mul_left]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResidueFormula
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit solution of the actual ramified residue system. The phase
is obtained from the finite rows and uniqueness from their strict contraction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

instance instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveZeroWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero Fourier mode at every positive cutoff. The incoming Mellin
term is entire and therefore contributes no residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaPositiveZeroWindowMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaPositiveZeroWindowProbability
lemma cubicThetaFullTorus_zero {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaFullTorus v s)) 0=
      cubicThetaEisensteinConstantMode v s := by
  let L := (cubicThetaTorusCoefficientMap 0).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaFullTorus v s)=_
  rw [cubicThetaFullTorus,map_add,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusCoefficientMap_apply,
    cubicThetaTorusFourier_toLp,cubicThetaTorusCoefficient_basis,ite_true, if_true,
    smul_eq_mul,mul_one,cubicThetaArithmeticTorus_zero hv hs,sub_add_cancel]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelSection
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticModelSectionCountable
lemma cubicThetaArithmeticModel_three_periodic (A : ℂ) (w : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaArithmeticModel A (z+3*(w:ℂ),v)=cubicThetaArithmeticModel A (z,v) := by
  unfold cubicThetaArithmeticModel
  congr 1
  congr 1
  rw [cubicThetaArithmeticRowSeries,cubicThetaArithmeticRowSeries]
  apply tsum_congr
  intro h
  rw [cubicThetaArithmeticRowTerm_phase (z+3*(w:ℂ)),cubicThetaArithmeticRowTerm_phase z]
  change _*cubicThetaHorizontalCharacter h (z+3*(w:ℂ))=_*cubicThetaHorizontalCharacter h z
  rw [cubicThetaHorizontalCharacter_periodic]

lemma cubicThetaArithmeticModel_translation (A : ℂ) (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel A (cubicThetaPointCoordinates (cubicThetaPrincipalTranslation w • p))=
      cubicThetaArithmeticModel A p.val := by
  rw [cubicThetaPrincipalTranslation_coordinates,cubicThetaArithmeticModel_three_periodic]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inversion operator on quotient representatives, including
the cubic phase of the chosen Borel section. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaBorelInversionFunction (f : CubicThetaQuotient → ℂ)
    (q : CubicThetaQuotient) : ℂ :=
  cubicThetaBorelLift f (cubicThetaFullInversion • cubicThetaBorelSection q)

lemma cubicThetaBorelInversionFunction_measurable {f : CubicThetaQuotient → ℂ}
    (hf : Measurable f) : Measurable (cubicThetaBorelInversionFunction f) :=
  (cubicThetaBorelLift_measurable hf).comp
    ((measurable_const_smul cubicThetaFullInversion).comp cubicThetaBorelSection_measurable)

lemma cubicThetaBorelInversionFunction_norm (f : CubicThetaQuotient → ℂ)
    (q : CubicThetaQuotient) :
    ‖cubicThetaBorelInversionFunction f q‖=
      ‖f (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)‖ := by
  rw [cubicThetaBorelInversionFunction,cubicThetaBorelLift_norm,
    ←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellinPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact positive-real power bookkeeping for the additive theta transform. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaDualScale (q : Eisenstein) (Z : ℝ) : ℝ :=
  (2*Real.pi)^4*(cubicThetaLevelScale q)^4*Z

def cubicThetaDualPrefactor (q : Eisenstein) : ℂ :=
  (cubicThetaLevelScale q:ℂ)^(-2:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2:ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual far-left dual Dirichlet integral into the literal
metaplectic transform, using absolute sum/integral interchange. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaDualMellinKernel (q : Eisenstein) (ℓ : ℤ) (W : ℝ→ℂ)
    (Z : ℝ) (s : ℂ) : ℂ :=
  cubicThetaDualPrefactor q*((cubicThetaDualScale q Z:ℂ)^s*
    metaplecticGammaQuotient ℓ s*mellin W s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

def cubicThetaShiftedTorusSeries (b : Eisenstein) (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein, cubicThetaShiftedFourierTerm b v s h • cubicThetaTorusFourier h

def cubicThetaShiftedTorus (b : Eisenstein) (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s) •
    cubicThetaShiftedTorusSeries b v s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPeriodMeasure
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual period-nine cell and its exact volume normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaShiftedPeriodEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  cubicThetaPeriodEquiv.trans (complexMulEquiv 3 (by norm_num))

def cubicThetaShiftedHorizontalCell : Set ℂ :=
  (fun z : ℂ => 3*z) '' cubicThetaHorizontalCell

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact height windows in the actual period-nine cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaShiftedWindow (a d : ℝ) : Set CubicThetaPoint :=
  {p | p.val.1∈cubicThetaShiftedHorizontalCell ∧ p.val.2∈Icc a d}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFullObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full translated-cusp observation, including the entire incoming
correction at low height. Its residue is unchanged. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedIncomingWindow (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) (s : ℂ) : ℂ :=
  ∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
    cubicThetaIncomingEisenstein (cubicThetaShiftedInversion b • p).val s
      ∂cubicThetaPointMeasure

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedAngularMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire Mellin continuation for the two actual coefficient families
in the primary-projected rational-cusp transformation. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaProjectedAngularAxis (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k)
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaSelectedAngularAxis (g : SL(2,Eisenstein)) (rev : Bool) (k : ℕ) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaProjectedAngularCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaProjectedAngularAxis g hc rev k)) s+
    cubicThetaLevelAngularRoot (g 1 0) rev k*
      mellin (thetaUpper (cubicThetaSelectedAngularAxis g rev k)) (((2*k:ℕ):ℂ)-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSelectedAngularMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse reciprocal law gives entire Mellin continuation for the
actual selected coefficients as well as for the projected dual family. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSelectedAngularCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaSelectedAngularAxis g rev k)) s+
    (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
      mellin (thetaUpper (cubicThetaProjectedAngularAxis g hc rev k)) (((2*k:ℕ):ℂ)-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire continued Dirichlet series for the actual primary-projected
cusp pair, with the initial series fixed by the literal coefficients. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaProjectedDirichlet (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) k s*
    cubicThetaProjectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)

def cubicThetaSelectedDirichlet (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) k s*
    cubicThetaSelectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedSmoothMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin inversion for the literal primary-selected coefficients
at every primary rational cusp. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaSelectedAdditiveSum (g : SL(2,Eisenstein)) (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (Z : ℝ) : ℂ :=
  ∑' n : MetaplecticDualArgument,theta (cubicThetaCircleOrder (!rev) k) n.val*
    cubicThetaCoefficientTwist cubicThetaSelectedCoefficient (cubicThetaPrimaryCuspCenter g) n.val*
      (‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSelectedGaussSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact primary-pair reindexing of the smoothed additive sum. The common
numerator is lambda*c*d^3, so the squared frequency is N(c)N(d)^3/27. -/
noncomputable section
open Set
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaSelectedSmoothSum (ℓ : ℤ) (z : ℂ) (W : ℝ→ℂ) (Z : ℝ) : ℂ :=
  ∑' n : MetaplecticDualArgument,theta ℓ n.val*
    cubicThetaCoefficientTwist cubicThetaSelectedCoefficient z n.val*
      (‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNineCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInverseNine_spec (r : Eisenstein) (hr : primary r) :
    (9:Eisenstein)∣1-r*cubicThetaInverseNine r hr := by
  obtain ⟨y,hy⟩ := Classical.choose_spec (cubicTheta_coprime_nine hr)
  refine ⟨y,?_⟩
  change 1-r*Classical.choose (cubicTheta_coprime_nine hr)=9*y
  linear_combination -hy

def cubicThetaNineGaussMatrix (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) : SL(2,Eisenstein) :=
  let g := cubicThetaGaussCuspMatrix r hr u hu
  g*cubicThetaFullTranslation (-(cubicThetaInverseNine r hr*g 1 1))

lemma cubicThetaNineGaussMatrix_entries (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaNineGaussMatrix r hr u hu 0 0=lambdaE^3*u ∧
    cubicThetaNineGaussMatrix r hr u hu 1 0=r ∧
    cubicThetaNineGaussMatrix r hr u hu 1 1=
      cubicThetaGaussCuspMatrix r hr u hu 1 1*(1-r*cubicThetaInverseNine r hr) := by
  let g := cubicThetaGaussCuspMatrix r hr u hu
  change (g.val*(!![1,-(cubicThetaInverseNine r hr*g 1 1);0,1] :
    Matrix (Fin 2) (Fin 2) Eisenstein)) 0 0=_ ∧
    (g.val*!![1,-(cubicThetaInverseNine r hr*g 1 1);0,1]) 1 0=_ ∧
    (g.val*!![1,-(cubicThetaInverseNine r hr*g 1 1);0,1]) 1 1=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  dsimp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  simp only [mul_one,mul_zero,add_zero]
  refine ⟨rfl,rfl,?_⟩
  change r*(-(cubicThetaInverseNine r hr*g 1 1))+g 1 1=_
  ring

lemma cubicThetaNineGaussMatrix_nine (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    (9:Eisenstein)∣cubicThetaNineGaussMatrix r hr u hu 1 1 := by
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).2.2]
  exact dvd_mul_of_dvd_right (cubicThetaInverseNine_spec r hr) _

lemma cubicThetaNineGaussMatrix_primary (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    primary (cubicThetaNineGaussMatrix r hr u hu 1 0) := by
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).2.1]
  exact hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueCusps
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational-cusp lift on every residue. Nonunit residues get
an arbitrary determinant-one lift, and their cubic character weight is zero. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaResidueCuspMatrix (r : Eisenstein) (hr : primary r) (u : Eisenstein) :
    SL(2,Eisenstein) :=
  if hu : IsCoprime r u then cubicThetaNineGaussMatrix r hr u hu
  else cubicThetaPrimitiveMatrix r 1 isCoprime_one_right

lemma cubicThetaResidueCuspMatrix_bottom (r : Eisenstein) (hr : primary r) (u : Eisenstein) :
    cubicThetaResidueCuspMatrix r hr u 1 0=r := by
  unfold cubicThetaResidueCuspMatrix
  split_ifs with hu
  · exact (cubicThetaNineGaussMatrix_entries r hr u hu).2.1
  · rfl

theorem cubicThetaResidueCuspPrimary (r : Eisenstein) (hr : primary r) (u : Eisenstein) :
    primary (cubicThetaResidueCuspMatrix r hr u 1 0) := by
  rw [cubicThetaResidueCuspMatrix_bottom]
  exact hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAveragedVoronoi
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete finite character average of the proved angular additive
Voronoi formula. The coefficient is the actual finite cusp average; further
local/Moebius simplification is kept separate. -/
noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaResidueDualCoefficient (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] (n : Eisenstein) : ℂ :=
  ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
    cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u)))
      (cubicThetaPrimaryDualCenter (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))) n

def cubicThetaResidueDualTerm (r : Eisenstein) (hr : primary r) [Fintype (Residues r)]
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ) (n : MetaplecticDualArgument) : ℂ :=
  theta (cubicThetaCircleOrder rev k) n.val*cubicThetaResidueDualCoefficient r hr n.val/
    (‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
        (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonCuspCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dual three-cusp coefficient before local cube cancellation.
All dependence on a coprime additive numerator is in its cubic character. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

def cubicThetaCommonCuspCoefficient (n : Eisenstein) : ℂ :=
  (∑ j : Fin 3,omega^j.val*star (cubicThetaActualCuspCoefficient (j.val:ℤ) (-n)))/3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientMass
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Dirichlet mass of the literal theta coefficients. The
unit, ramified, squarefree and cube factors are kept separate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaCoefficientMassTerm (σ : ℝ) (n : Eisenstein) : ℝ :=
  ‖cubicThetaArithmeticCoefficient n‖^2 * (norm n)^(-σ)

def cubicThetaCoefficientMass (σ : ℝ) : ℝ :=
  ∑' n : Eisenstein, cubicThetaCoefficientMassTerm σ n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCancellation
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaCommonTau (n : Eisenstein) : ℂ :=
  (‖cubicThetaFrequency n‖:ℂ)*cubicThetaCommonCuspCoefficient n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete dual coefficient after free-cube removal. Its support
and the required ramified coefficient bound are proved from the actual
three-cusp arithmetic formulas. The summation identity is separate. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaCoreCoefficient (r : Eisenstein) (n : MetaplecticDualArgument) : ℂ :=
  if CubicThetaCoreSupport r n then cubicThetaCommonTau n.val else 0

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

def cubicThetaRemainderWeight (n : Eisenstein) : ℝ :=
  cubicThetaPositiveRemainderWeight n+cubicThetaNegativeRemainderWeight n+
    cubicThetaHighRemainderWeight n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyMellin
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini for the actual horizontal Fourier energy and its
coefficient Dirichlet mass. The frequency dilation is retained exactly. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaEnergyMellinTerm (σ : ℝ) (n : Eisenstein) (v : ℝ) : ℝ :=
  v^(2*σ-1)*‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierEnergyLowPole
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutting the arithmetic energy Mellin integral at height one preserves its pole. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaFourierEnergyHighMass (σ : ℝ) : ℝ :=
  ∫ v in Ioi (1:ℝ),v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v

def cubicThetaFourierEnergyLowMass (σ : ℝ) : ℝ :=
  ∫ v in Ioc (0:ℝ) 1,v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNonzeroRowHeat
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal two-coordinate Gaussian behind the nonzero-first-row bound. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNonzeroRowHeatTerm (p : ℂ × ℝ) (t : ℝ) (r : CubicThetaNonzeroRow) : ℝ :=
  Real.exp (-t*cubicThetaNonzeroRowQuadratic p r)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveRowFactorization
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique extraction of the primary common factor of a level-three row.
The inverse uses a Bezout identity for its actual gcd. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimitiveRowEquiv : PrimaryArgument × CubicThetaBottomRow ≃ CubicThetaFullRow :=
  Equiv.ofBijective (fun p => cubicThetaFullRowMultiply p.1 p.2)
    ⟨cubicThetaFullRowMultiply_injective,cubicThetaFullRowMultiply_surjective⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularHeatLow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-time Mellin remainder is integrable and continuous at the
critical exponent after subtracting the proved heat coefficient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

def cubicThetaRegularHeatLow (p : ℂ × ℝ) (s t : ℝ) : ℝ :=
  t^(s-1)*(cubicThetaFullGaussian p t-(4*Real.pi^2/243)/t^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularHeatPole
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar row Mellin transform has the exact pole supplied by the
four-dimensional affine lattice. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

def cubicThetaRegularHeatMass (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  (∫ t in Ioc (0:ℝ) 1,cubicThetaRegularHeatLow p s t)+
    ∫ t in Ioi (1:ℝ),t^(s-1)*cubicThetaFullGaussian p t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarHeightSeed
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp scalar height cutoff has an actual half-open strip seed. -/
noncomputable section
open Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaScalarHeightSeed (s : ℝ) (p : CubicThetaPoint) : ℝ :=
  if p.val.1∈cubicThetaHorizontalCell then cubicThetaScalarHeightWeight s p.val.2 else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarSeedPairing
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact periodization of the positive sharp-height seed times section energy. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaScalarEnergySeed (F : CubicThetaSection) (σ : ℝ) (p : CubicThetaPoint) : ℝ :=
  cubicThetaScalarHeightSeed (2+2*σ) p*‖F.val p‖^2

def cubicThetaScalarEnergyDensity (F : CubicThetaSection) (σ : ℝ)
    (q : CubicThetaQuotient) : ℝ :=
  cubicThetaScalarRankinKernel σ q*‖cubicThetaSectionRepresentative F q‖^2


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDerivativeRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic derivative remainder is dominated by the three
summable coordinate families. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaDerivativeRemainder (n : Eisenstein) : ℂ :=
  if n=lambdaE ∨ n= -lambdaE then 0
  else cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 1 n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeCubeParts
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the supported/free primary split used in the actual
dual cube expansion. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicTheta_primarySmallPart_mul {r a b : Eisenstein}
    (hr : r≠0) (ha : primary a) (hb : primary b)
    (hs : ∃ k : ℕ, a∣r^k) (hcop : IsCoprime b r) :
    primarySmallPart r (a*b)=a := by
  have hab := primary_mul ha hb
  apply primary_eq_of_idealExponentOf_eq (primarySmallPart_primary r hab) ha
  rw [primarySmallPart,idealExponentOf_primaryGenerator,
    idealExponentOf_mul (primary_ne_zero ha) (primary_ne_zero hb)]
  have hs' := idealExponent_support_of_dvd_power (primary_ne_zero ha) hr hs
  have hc := (isCoprime_iff_idealExponent_disjoint (primary_ne_zero hb) hr).mp hcop
  ext p
  change (if p∈(idealExponentOf r).support then
    (idealExponentOf a+idealExponentOf b) p else 0)=idealExponentOf a p
  by_cases hp : p∈(idealExponentOf r).support
  · rw [ite_eq_left hp,Finsupp.add_apply]
    have hbp : idealExponentOf b p=0 := (hc p).resolve_right (Finsupp.mem_support_iff.mp hp)
    rw [hbp,add_zero]
  · rw [ite_eq_right hp]
    exact (Finsupp.notMem_support_iff.mp (fun h => hp (hs' h))).symm

lemma cubicTheta_primaryOutsidePart_mul {r a b : Eisenstein}
    (hr : r≠0) (ha : primary a) (hb : primary b)
    (hs : ∃ k : ℕ, a∣r^k) (hcop : IsCoprime b r) :
    primaryOutsidePart r (a*b)=b := by
  have h := primary_small_outside_mul r (primary_mul ha hb)
  rw [cubicTheta_primarySmallPart_mul hr ha hb hs hcop] at h
  exact mul_left_cancel₀ (primary_ne_zero ha) h

lemma cubicTheta_supported_free_unique {r a b c d : Eisenstein}
    (hr : r≠0) (ha : primary a) (hb : primary b) (hc : primary c) (hd : primary d)
    (has : ∃ k : ℕ, a∣r^k) (hcs : ∃ k : ℕ, c∣r^k)
    (hbr : IsCoprime b r) (hdr : IsCoprime d r) (he : a*b=c*d) :
    a=c ∧ b=d := by
  have h1 := congrArg (primarySmallPart r) he
  have h2 := congrArg (primaryOutsidePart r) he
  rw [cubicTheta_primarySmallPart_mul hr ha hb has hbr,
    cubicTheta_primarySmallPart_mul hr hc hd hcs hdr] at h1
  rw [cubicTheta_primaryOutsidePart_mul hr ha hb has hbr,
    cubicTheta_primaryOutsidePart_mul hr hc hd hcs hdr] at h2
  exact ⟨h1,h2⟩

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

lemma cubicThetaFreeCubeJoin_injective {r : Eisenstein} (hr : r≠0) :
    Function.Injective (cubicThetaFreeCubeJoin r) := by
  intro a b he
  have hu := congrArg (fun x : CubicThetaCommonIndex => x.1) he
  have hk := congrArg (fun x : CubicThetaCommonIndex => x.2.1) he
  have hc := congrArg (fun x : CubicThetaCommonIndex => x.2.2.val.1) he
  have hd := congrArg (fun x : CubicThetaCommonIndex => x.2.2.val.2) he
  change a.1.val.1=b.1.val.1 at hu
  change a.1.val.2.1=b.1.val.2.1 at hk
  change a.1.val.2.2.val.1=b.1.val.2.2.val.1 at hc
  change a.1.val.2.2.val.2*(a.2.val:Eisenstein)=
    b.1.val.2.2.val.2*(b.2.val:Eisenstein) at hd
  have hs := cubicTheta_supported_free_unique hr a.1.val.2.2.property.2.1 a.2.val.property
    b.1.val.2.2.property.2.1 b.2.val.property a.1.property b.1.property
    a.2.property b.2.property hd
  exact Prod.ext (Subtype.ext (Prod.ext hu (Prod.ext hk (Subtype.ext (Prod.ext hc hs.1)))))
    (Subtype.ext (Subtype.ext hs.2))

lemma cubicThetaFreeCubeJoin_surjective {r : Eisenstein} (hr : r≠0) :
    Function.Surjective (cubicThetaFreeCubeJoin r) := by
  intro x
  let c := x.2.2.val.1
  let d := x.2.2.val.2
  have hd : primary d := x.2.2.property.2.1
  let y : CubicThetaCoreIndex r := ⟨(x.1,x.2.1,
    ⟨(c,primarySmallPart r d),x.2.2.property.1,primarySmallPart_primary r hd,
      x.2.2.property.2.2⟩),cubicTheta_primarySmallPart_supported hr hd⟩
  let e : CubicThetaFreeArgument r :=
    ⟨⟨primaryOutsidePart r d,primaryOutsidePart_primary r hd⟩,primaryOutsidePart_coprime hd hr⟩
  refine ⟨(y,e),?_⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact primary_small_outside_mul r hd

def cubicThetaFreeCubeEquiv (r : Eisenstein) (hr : r≠0) :
    (CubicThetaCoreIndex r × CubicThetaFreeArgument r) ≃ CubicThetaCommonIndex :=
  Equiv.ofBijective (cubicThetaFreeCubeJoin r)
    ⟨cubicThetaFreeCubeJoin_injective hr,cubicThetaFreeCubeJoin_surjective hr⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInverseResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaNineConductorUnit (r : Eisenstein) (hr : primary r) : (Residues r)ˣ :=
  (residue_isUnit_of_isCoprime
    ((cubicTheta_coprime_nine hr).mul_right ((primary_coprime_lambda hr).pow_right (n:=3)))).unit

def cubicThetaNineUnitInverse (r : Eisenstein) (hr : primary r) (u : (Residues r)ˣ) : Eisenstein :=
  Classical.choose (cubicThetaNineGaussMatrix_nine r hr (residueRepresentative r u)
    (cubicThetaUnitRepresentative_coprime r u))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalVoronoi
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonzero-angular summation formula with the finite cusp
average evaluated as its exact Ramanujan Euler product. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaLocalDualTerm (r : Eisenstein) (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) (n : MetaplecticDualArgument) : ℂ :=
  theta (cubicThetaCircleOrder rev k) n.val*
    (cubicThetaCommonCuspCoefficient n.val*metaplecticLocalCoefficient r n)/
      (‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
          (cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeLocalVoronoi
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaFreeLocalDualTerm (r : Eisenstein) (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) : ℂ :=
  theta (cubicThetaCircleOrder rev k) (cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x))*
    (cubicThetaCoreCoefficient r (cubicThetaCommonArgument x.1.val)*
      metaplecticLocalCoefficient r (cubicThetaCommonArgument x.1.val))/
        ((‖cubicThetaFrequency (cubicThetaCommonNumerator x.1.val)‖^2*
          norm (x.2.val:Eisenstein)^(5/2:ℝ):ℝ):ℂ)*
    metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
      (cubicThetaDualScale r (X/27)*
        ‖cubicThetaFrequency (cubicThetaCommonNumerator x.1.val)‖^2*
          norm (x.2.val:Eisenstein)^3)

end CubicFirstMoment

end

end OAI
end


