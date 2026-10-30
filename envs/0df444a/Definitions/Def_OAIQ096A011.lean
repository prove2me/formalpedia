-- Prove2me | Definitions.Def_OAIQ096A011
-- name    : OAIQ096A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:43:13.780269+00:00
-- url     : https://prove2.me/theorems/cf6bfcb8-8085-46eb-b934-d9fe9455da21
-- title:
--   Definitions bundle OAIQ096A011 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 347 declarations of OpenAI's Lean: 156 definitions, 12 instances and 179 theorems. The definitions and types are `OAI.CubicFirstMoment.angularNumeratorChar`, `OAI.CubicFirstMoment.angularPrimeCoordinateError`, `OAI.CubicFirstMoment.angularResidueNormTwist`, `OAI.CubicFirstMoment.angularSemiprimeSmoothedPolynomial`, `OAI.CubicFirstMoment.angularShortFamilyOfSmoothWeights`, `OAI.CubicFirstMoment.angularSquarefreeCoordinateError`, `OAI.CubicFirstMoment.angularTraceFourierCLM`, `OAI.CubicFirstMoment.angularTwistArithmetic`, `OAI.CubicFirstMoment.angular_distinguishedScaleNoStop`, `OAI.CubicFirstMoment.angular_distinguishedScaleStopped`, `OAI.CubicFirstMoment.angular_distinguishedScaleStoppedRow`, `OAI.CubicFirstMoment.angular_distinguishedStoppedDyad`, `OAI.CubicFirstMoment.angular_fullPrimeDivisorMellinMass`, `OAI.CubicFirstMoment.angular_largePrimeTupleExceptionalHighSum`, `OAI.CubicFirstMoment.angular_largePrimeTupleExceptionalNonflatSum`, `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum`, `OAI.CubicFirstMoment.angular_largePrimeTupleOrdinaryHighSum`, `OAI.CubicFirstMoment.angular_largePrimeTupleSelectedFlatHighSum`, `OAI.CubicFirstMoment.angular_largeTupleExceptionalSelector`, `OAI.CubicFirstMoment.angular_scaleFirstHighSum`, `OAI.CubicFirstMoment.angular_scaleFirstMiddleSum`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowArity`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryNoStopArity`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryNoStopTail`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryStoppedArity`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedEnvelopeTail`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedSum`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedWindow`, `OAI.CubicFirstMoment.angular_stoppedCharacterSum`, `OAI.CubicFirstMoment.angular_stoppedDistinguishedRows`, `OAI.CubicFirstMoment.angular_stoppedSelectedPrimeRow`, `OAI.CubicFirstMoment.angular_tailHighOrdinaryArity`, `OAI.CubicFirstMoment.angular_tailHighUpperArity`, `OAI.CubicFirstMoment.angular_tailPrimeOrdinaryTuple`, `OAI.CubicFirstMoment.angular_tailPrimeOrdinaryTupleSum`, `OAI.CubicFirstMoment.angular_tailPrimeTupleTail`, `OAI.CubicFirstMoment.angular_tailPrimeUpperTuple`, `OAI.CubicFirstMoment.angular_tailPrimeUpperTupleSum`, `OAI.CubicFirstMoment.angular_upperLowArity` and 116 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_LatticePoisson`, `CubicGram_MellinDecay`, `CubicGram_MellinNorm`, `CubicGram_SieveMajorant`, `CubicMoment_Angular_AngularArithmeticTwist`, `CubicMoment_Angular_AngularHeightDivisorBounds`, `CubicMoment_Angular_AngularLargeTupleExceptionalHigh`, `CubicMoment_Angular_AngularLargeTupleHighSum`, `CubicMoment_Angular_AngularLargeTupleOrdinarySum`, `CubicMoment_Angular_AngularLargeTupleSelectedFlat`, `CubicMoment_Angular_AngularNoStopNegligible`, `CubicMoment_Angular_AngularNumeratorCharacter`, `CubicMoment_Angular_AngularOrdinaryStoppedTail`, `CubicMoment_Angular_AngularOrdinaryTail`, `CubicMoment_Angular_AngularPrimeCoordinateCollection`, `CubicMoment_Angular_AngularRestrictedNoStopParameters`, `CubicMoment_Angular_AngularScaleFirstHighSum`, `CubicMoment_Angular_AngularScaleFirstMiddleSum`, `CubicMoment_Angular_AngularScaleFirstStoppedDyads`, `CubicMoment_Angular_AngularSemiprimeSmoothed`, `CubicMoment_Angular_AngularSmoothShortFamily`, `CubicMoment_Angular_AngularStoppedAggregation`, `CubicMoment_Angular_AngularStoppedDistinguishedRows`, `CubicMoment_Angular_AngularStoppedLongBinSaving`, `CubicMoment_Angular_AngularStoppedSelectedRow`, `CubicMoment_Angular_AngularTailHighDecomposition`, `CubicMoment_Angular_AngularTailHighOrdinaryNegligible`, `CubicMoment_Angular_AngularTailHighUpperNegligible`, `CubicMoment_Angular_AngularTailPrimeOrdinaryTuple`, `CubicMoment_Angular_AngularTailPrimeTailGeometry`, `CubicMoment_Angular_AngularTailPrimeUpperTuple`, `CubicMoment_Angular_AngularUpperLowTail`, `CubicMoment_Angular_AngularUpperNoStopNegligible`, `CubicMoment_Angular_AngularUpperStoppedSuffix`, `CubicMoment_Angular_AngularUpperTailAggregation`, `CubicMoment_Angular_AngularWeightOperator`, `CubicMoment_Decomposition_DistinguishedScalePartition`, `CubicMoment_Decomposition_PrimeProductDetector`, `CubicMoment_Decomposition_StoppedMatrixDyads`, `CubicMoment_Estimates_ArithmeticMellinKernel`, `CubicMoment_Estimates_CenteredMellinWindow`, `CubicMoment_Estimates_CentralProductSupport`, `CubicMoment_Estimates_CentralStoppingDecomposition`, `CubicMoment_Estimates_CoprimeMellinMass`, `CubicMoment_Estimates_CubeSchwartz`, `CubicMoment_Estimates_CubicNumeratorCharacter`, `CubicMoment_Estimates_CubicNumeratorCubeFactor`, `CubicMoment_Estimates_CubicNumeratorNoncube`, `CubicMoment_Estimates_CubicNumeratorOrder`, `CubicMoment_Estimates_GramStructuredRows`, `CubicMoment_Estimates_KummerPrimeFactorization`, `CubicMoment_Estimates_LargeTupleExponents`, `CubicMoment_Estimates_LargeTupleFlatCount`, `CubicMoment_Estimates_LargeTupleGrouping`, `CubicMoment_Estimates_LargeTuplePartition`, `CubicMoment_Estimates_MixedResidueCharacters`, `CubicMoment_Estimates_PrimaryCharacterNonprincipal`, `CubicMoment_Estimates_PrimeCoordinateDifference`, `CubicMoment_Estimates_PrimeIndicatorCollection`, `CubicMoment_Estimates_RamifiedCubicNonprincipal`, `CubicMoment_Estimates_RestrictedNoStopCentral`, `CubicMoment_Estimates_RestrictedNoStopWindow`, `CubicMoment_Estimates_ScaleFirstStoppedDyads`, `CubicMoment_Estimates_ScaleFirstStopping`, `CubicMoment_Estimates_ScaleFirstTailDecomposition`, `CubicMoment_Estimates_ScaleFirstTailDecompositionRows`, `CubicMoment_Estimates_ScaleFirstTuple`, `CubicMoment_Estimates_SemiprimeFullSupport`, `CubicMoment_Estimates_SemiprimePartition`, `CubicMoment_Estimates_TailHighCollection`, `CubicMoment_Estimates_TypeIProductFourier`, `CubicMoment_Estimates_TypeIProductSupport`, `CubicMoment_Estimates_TypeIProductWindow`, `CubicMoment_Estimates_UpperTailStopping`, `CubicMoment_Estimates_UpperTailTuple`, `CubicMoment_Theta_CubicThetaAngularFunctionalEquation`, `CubicMoment_Theta_CubicThetaAutomorphicSections`, `CubicMoment_Theta_CubicThetaC1ChartNorm`, `CubicMoment_Theta_CubicThetaC1Division`, `CubicMoment_Theta_CubicThetaC1Energy`, `CubicMoment_Theta_CubicThetaC1EnergyLinear`, `CubicMoment_Theta_CubicThetaC1EnergyNorm`, `CubicMoment_Theta_CubicThetaC1EnergySums`, `CubicMoment_Theta_CubicThetaC1GradientLinear`, `CubicMoment_Theta_CubicThetaC1L2`, `CubicMoment_Theta_CubicThetaC1Localization`, `CubicMoment_Theta_CubicThetaChartRestrictedIntegral`, `CubicMoment_Theta_CubicThetaChartSections`, `CubicMoment_Theta_CubicThetaChartTransition`, `CubicMoment_Theta_CubicThetaCompactC1Energy`, `CubicMoment_Theta_CubicThetaCompactCoreCover`, `CubicMoment_Theta_CubicThetaCompactCuspCutoff`, `CubicMoment_Theta_CubicThetaCompactEnergyCorrection`, `CubicMoment_Theta_CubicThetaCompactHeight`, `CubicMoment_Theta_CubicThetaCompactInCore`, `CubicMoment_Theta_CubicThetaComplexLocalization`, `CubicMoment_Theta_CubicThetaCoordinateData`, `CubicMoment_Theta_CubicThetaCoordinateEnergyClosure`, `CubicMoment_Theta_CubicThetaCoordinateSection`, `CubicMoment_Theta_CubicThetaCoordinateSectionNorm`, `CubicMoment_Theta_CubicThetaCoordinateSectionSupport`, `CubicMoment_Theta_CubicThetaCoreBumps`, `CubicMoment_Theta_CubicThetaCoreDenominator`, `CubicMoment_Theta_CubicThetaCoreDivision`, `CubicMoment_Theta_CubicThetaCoreProfiles`, `CubicMoment_Theta_CubicThetaCoreSections`, `CubicMoment_Theta_CubicThetaCuspDisjointness`, `CubicMoment_Theta_CubicThetaCuspExhaustion`, `CubicMoment_Theta_CubicThetaCuspFourierObservable`, `CubicMoment_Theta_CubicThetaCuspNeighborhoodCover`, `CubicMoment_Theta_CubicThetaCuspStrip`, `CubicMoment_Theta_CubicThetaCuspStripEnergy`, `CubicMoment_Theta_CubicThetaCuspStripMeasure`, `CubicMoment_Theta_CubicThetaCuspStripReduction`, `CubicMoment_Theta_CubicThetaEnergyPencilKernel`, `CubicMoment_Theta_CubicThetaExceptionalProjection`, `CubicMoment_Theta_CubicThetaFiniteCuspRestriction`, `CubicMoment_Theta_CubicThetaFiniteEnergySections`, `CubicMoment_Theta_CubicThetaForcedResidue`, `CubicMoment_Theta_CubicThetaForcingCore`, `CubicMoment_Theta_CubicThetaForcingL2`, `CubicMoment_Theta_CubicThetaFullRows`, `CubicMoment_Theta_CubicThetaFundamentalDomain`, `CubicMoment_Theta_CubicThetaFundamentalExtension`, `CubicMoment_Theta_CubicThetaGlobalEnergy`, `CubicMoment_Theta_CubicThetaGlobalGradient`, `CubicMoment_Theta_CubicThetaGlobalL2`, `CubicMoment_Theta_CubicThetaHorizontalCompact`, `CubicMoment_Theta_CubicThetaHyperbolicMeasure`, `CubicMoment_Theta_CubicThetaLevelReciprocity`, `CubicMoment_Theta_CubicThetaLocalLifts`, `CubicMoment_Theta_CubicThetaLocalQuotientMeasure`, `CubicMoment_Theta_CubicThetaPoincareLinear`, `CubicMoment_Theta_CubicThetaPoincareLocalization`, `CubicMoment_Theta_CubicThetaPoincareSections`, `CubicMoment_Theta_CubicThetaPoincareSmooth`, `CubicMoment_Theta_CubicThetaPrimeCubeMassOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphicL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCuspRestriction`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylL2`, `CubicMoment_Theta_CubicThetaQuotient`, `CubicMoment_Theta_CubicThetaQuotientCharts`, `CubicMoment_Theta_CubicThetaQuotientCore`, `CubicMoment_Theta_CubicThetaQuotientEnergy`, `CubicMoment_Theta_CubicThetaQuotientLocalFiniteness`, `CubicMoment_Theta_CubicThetaQuotientManifold`, `CubicMoment_Theta_CubicThetaQuotientMeasure`, `CubicMoment_Theta_CubicThetaScalarCuspQuotient`, `CubicMoment_Theta_CubicThetaSectionDifferential`, `CubicMoment_Theta_CubicThetaSiegelReduction`, `CubicMoment_Theta_CubicThetaStripFiniteVolume`, `CubicMoment_Theta_CubicThetaTranslatedCuspStrip`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A007` and `OAIQ096A008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A016`, `OAIQ096A017`, `OAIQ096A018`, `OAIQ096A019` and `OAIQ096A020`; the statements `OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_divisor_noncube_total_saving`, `OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual`, `OAI.CubicFirstMoment.angular_full_prime_centered_smoothed_bilinear_actual`, `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving`, `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual`, `OAI.CubicFirstMoment.angular_noncube_poisson_total_saving`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryLowTail_isLittleO_proved`, `OAI.CubicFirstMoment.angular_scaleFirstOrdinaryNoStopTail_isLittleO_proved`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO`, `OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic`, `OAI.CubicFirstMoment.angular_tailHighUpperArity_isLittleO_uniform`, `OAI.CubicFirstMoment.angular_two_prime_transition_centered`, `OAI.CubicFirstMoment.angular_upperNoStopTail_isLittleO_proved`, `OAI.CubicFirstMoment.angular_upperStoppedFilteredTail_isLittleO_uniform`, `OAI.CubicFirstMoment.coprime_noncube_mellin_integral_saving`, `OAI.CubicFirstMoment.divisor_noncube_total_saving`, `OAI.CubicFirstMoment.first_angular_primeCoordinateError_moment`, `OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment`, `OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer`, `OAI.CubicFirstMoment.full_prime_centered_product_bilinear_actual`, `OAI.CubicFirstMoment.full_prime_product_height_bilinear`, `OAI.CubicFirstMoment.height_radial_form_saving`, `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.noncube_poisson_total_saving`, `OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual`, `OAI.CubicFirstMoment.short_outer_low_bound_actual`, `OAI.CubicFirstMoment.sieved_full_model_asymptotic` and `OAI.CubicFirstMoment.two_prime_transition_centered`; the proofs of `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_twisted_tail_arbitrary_power`, `OAI_CubicFirstMoment_angular_low_noncube_mass`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO`, `OAI.CubicFirstMoment.angular_stoppedBeta_distinguished_log_saving_all`, `OAI.CubicFirstMoment.angular_stopped_noncube_mass`, `OAI_CubicFirstMoment_angular_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_balanced_common_squarefree_exponents`, `OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds`, `OAI.CubicFirstMoment.first_angular_primeCoordinateError_moment`, `OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment`, `OAI_CubicFirstMoment_low_noncube_mass`, `OAI_CubicFirstMoment_low_shrinking_variance_remainder`, `OAI.CubicFirstMoment.smallB_core_hybrid_sieve`, `OAI.CubicFirstMoment.small_conductor_frequency_sieve` and `OAI_CubicFirstMoment_stopped_rough_divisor_log`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein real coordinates, measure factors and translated lattice Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicFirstMoment
open CubicPoisson

lemma complexMulMatrix_det (q : ℂ) :
    (complexMulMatrix q).det = Complex.normSq q := by
  simp [complexMulMatrix, Matrix.det_fin_two, Complex.normSq_apply]

lemma complexMulMatrix_apply (q : ℂ) (x : Fin 2 → ℝ) :
    Complex.measurableEquivPi.symm (Matrix.toLin' (complexMulMatrix q) x) =
      q * Complex.measurableEquivPi.symm x := by
  apply Complex.ext <;>
    simp [complexMulMatrix, Matrix.toLin'_apply,
      Matrix.vecHead, Matrix.vecTail, Complex.mul_re, Complex.mul_im]
  <;> ring

lemma complexMul_map_volume (q : ℂ) (hq : q ≠ 0) :
    Measure.map (fun z : ℂ => q * z) volume =
      ENNReal.ofReal (Complex.normSq q)⁻¹ • (volume : Measure ℂ) := by
  have hn : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := complexMulMatrix q) (by rw [complexMulMatrix_det]; positivity)
  have he : (fun z : ℂ => q * z) ∘ Complex.measurableEquivPi.symm =
      Complex.measurableEquivPi.symm ∘ Matrix.toLin' (complexMulMatrix q) := by
    funext x
    exact (complexMulMatrix_apply q x).symm
  calc
    _ = Measure.map (fun z : ℂ => q * z)
        (Measure.map Complex.measurableEquivPi.symm volume) := by
      rw [Complex.volume_preserving_equiv_pi.symm.map_eq]
    _ = Measure.map Complex.measurableEquivPi.symm
        (Measure.map (Matrix.toLin' (complexMulMatrix q)) volume) := by
      rw [Measure.map_map (by fun_prop) Complex.measurableEquivPi.symm.measurable, he,
        Measure.map_map Complex.measurableEquivPi.symm.measurable
          (Matrix.toLin' (complexMulMatrix q)).continuous_of_finiteDimensional.measurable]
    _ = _ := by
      rw [hm, Measure.map_smul,
        Complex.volume_preserving_equiv_pi.symm.map_eq,
        complexMulMatrix_det, abs_of_pos (inv_pos.mpr hn), ENNReal.ofReal_inv_of_pos hn]

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

@[simp] lemma norm_gramMellinPhase (t x : ℝ) : ‖gramMellinPhase t x‖ = 1 :=
  Circle.norm_coe _

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin integral bounds for coprime radial forms. -/

section

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def coprimeMellinKernel (S H : Finset Eisenstein) (v w phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (t : ℝ) : ℂ :=
  ∑ h ∈ H, (phase h * gramMellinPhase t (x h)) * ∑ a ∈ S, ∑ b ∈ S,
    if IsCoprime a b then
      (v a * star (gramMellinPhase t (y a)) * star (cubicSymbol a h)) *
        star (w b * gramMellinPhase t (y b) * star (cubicSymbol b h)) else 0

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact sieve majorants and common-factor energy bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicSieveCutoff (t : ℝ) : ℂ := gramLogBump t

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedResidueCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed cubic residue characters and their finite Fourier transform. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyPhase_eq_fourierChar (q h n : Eisenstein) :
    huxleyPhase q h n = (Real.fourierChar
      (tracePair (n:ℂ) ((h:ℂ)/((q:ℂ)*traceLambda))) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold huxleyPhase tracePair
  dsimp only
  have hz (z : ℂ) : z+star z = (2*z.re:ℝ) := by
    apply Complex.ext <;> simp
    ring
  rw [hz]
  congr 1
  push_cast
  rw [show (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ)) =
    (n:ℂ)*((h:ℂ)/((q:ℂ)*traceLambda)) by ring]
  ring

/-- The raw Gauss transform has exactly the conductor square-root factor.
This identity holds also at nonunit frequencies (where the right side vanishes). -/
theorem mixedResidueChar_fourier {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b)
    [Fintype (Residues (a*b))] (n : Eisenstein) :
    (∑ x : Residues (a*b), mixedResidueChar a b ha hb x *
      huxleyPhase (a*b) (residueRepresentative (a*b) x) n) =
      ((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) /
        mixedCubic a b 3) * star (mixedCubic a b n) := by
  have hc : IsCoprime (a*b) 3 := by
    obtain ⟨k,hk⟩ := primary_mul ha hb
    refine ⟨1,-k,?_⟩
    linear_combination hk
  have hc3 : ‖mixedCubic a b 3‖ = 1 := mixedCubic_norm_of_coprime ha hb hc
  have hc30 : mixedCubic a b 3 ≠ 0 := norm_ne_zero_iff.mp (by rw [hc3]; norm_num)
  have hphase (x : Residues (a*b)) :
      huxleyPhase (a*b) (residueRepresentative (a*b) x) n =
      (Real.fourierChar (tracePair (residueRepresentative (a*b) x:ℂ)
        ((n:ℂ)/(((a*b:Eisenstein):ℂ)*traceLambda))) : ℂ) := by
    rw [huxleyPhase_eq_fourierChar]
    congr 2
    unfold tracePair
    congr 2
    ring
  have hsum : mixedCubic a b 3 * (∑ x : Residues (a*b), mixedResidueChar a b ha hb x *
      huxleyPhase (a*b) (residueRepresentative (a*b) x) n) =
      primaryMixedFourier a b n := by
    rw [primaryMixedFourier,tsum_fintype,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hphase]
    change mixedCubic a b 3 * (mixedCubic a b (residueRepresentative (a*b) x) * _) =
      mixedCubic a b (3*residueRepresentative (a*b) x) * _
    rw [mixedCubic_mul ha hb]
    ring
  apply (mul_left_cancel₀ hc30)
  rw [hsum,primaryMixedFourier_squarefree ha hb hsa hsb hab]
  field_simp [hc30]
  simp only [mixedCubic,star_mul,star_star]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryCharacterNonprincipal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonprincipality of the actual mixed character. The zero-frequency
Gauss identity and an explicit primary Chinese-remainder lift supply the
witness; nonprincipality is not imposed as an extra hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedResidueChar_ne_one {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b)) :
    mixedResidueChar a b ha hb ≠ 1 := by
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  have hz : mixedCubic a b 0 = 0 := by
    apply mixedCubic_eq_zero_of_nonunit ha hb
    intro h
    exact hnu (isCoprime_zero_right.mp (isCoprime_of_residue_isUnit h))
  have hsum := mixedResidueChar_fourier ha hb hsa hsb hab (0:Eisenstein)
  simp [huxleyPhase,hz] at hsum
  intro he
  rw [he,MulChar.sum_one_eq_card_units] at hsum
  exact (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero) :
    (Fintype.card (Residues (a*b))ˣ : ℂ) ≠ 0) hsum

/-- A primary witness for nonprincipality, on the actual prime-to-conductor
ideal character used in the finite-order Hecke input. -/
theorem mixedCubic_nonprincipal {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b)) : MixedCubicNonprincipal a b := by
  let χ := mixedResidueChar a b ha hb
  obtain ⟨v,hv⟩ := MulChar.ne_one_iff.mp (mixedResidueChar_ne_one ha hb hsa hsb hab hnu)
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective (v : Residues (a*b))
  obtain ⟨x,hx,hxy⟩ := exists_primary_residue_lift (primary_mul ha hb) y
  have hres : Ideal.Quotient.mk (modulus (a*b)) x = v := hxy.trans hy
  have hcx : IsCoprime (a*b) x := isCoprime_of_residue_isUnit (by rw [hres]; exact v.isUnit)
  refine ⟨x,hx,hcx,?_⟩
  intro he
  apply hv
  change mixedResidueChar a b ha hb v = 1
  rw [← hres,mixedResidueChar_mk]
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularArithmeticTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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
variable (ℓ : ℤ)

def angularResidueNormTwist (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ℂ :=
  angularResidueIdealChar q η ℓ ν*mellinPhase t (idealExponentNorm ν)

def angularTwistArithmetic (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) : MvPowerSeries EisensteinIdealPrime ℂ :=
  fun ν => ((MvPowerSeries.coeff ν A:ℝ):ℂ)*angularResidueNormTwist ℓ q η t ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateDifference
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateProductCutoff (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport (coordinateSupport W X Y)).filter (fun b => norm b ≤ 2*Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def coordinatePrimeSupport (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) (i : ι) : Finset Eisenstein :=
  (coordinateSupport W X Y i).filter Prime

def coordinatePrimeCutoff (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter (fun b => norm b ≤ 2*Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def angularPrimeCoordinateError (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinateProductCutoff W X Y,
    primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*theta ℓ z*V (norm z/Y))

def angularSquarefreeCoordinateError (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinatePrimeCutoff W X Y,
    squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*theta ℓ z*V (norm z/Y))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite numerator character needed for arbitrary v in the
exceptional moments. The only conditional input here is the periodicity
consequence of cubic reciprocity and the unit/ramified supplementary laws:
Dunn–Radziwiłł (2024), equations (1.4)–(1.5). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicNumeratorLift_primary (v : Eisenstein) {x : Eisenstein} (hx : primary x) :
    cubicNumeratorLift v x = cubicSymbol x v := by
  rw [cubicNumeratorLift,ite_eq_left (unit_residue_of_dvd_primary hx (dvd_refl x)),
    primaryNormalize_eq_self hx]

lemma cubicNumeratorLift_mul (v x y : Eisenstein) :
    cubicNumeratorLift v (x*y) = cubicNumeratorLift v x*cubicNumeratorLift v y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · by_cases hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)
    · simp only [cubicNumeratorLift,map_mul,IsUnit.mul_iff,hx,hy,true_and,ite_true, if_true]
      rw [primaryNormalize_mul_of_residue_units hx hy,
        cubicSymbol_mul_lower (primary_ne_zero (primaryNormalize_primary hx))
          (primary_ne_zero (primaryNormalize_primary hy))]
    · simp [cubicNumeratorLift,map_mul,IsUnit.mul_iff,hx,hy]
  · simp [cubicNumeratorLift,map_mul,IsUnit.mul_iff,hx]

lemma cubicNumeratorLift_one (v : Eisenstein) : cubicNumeratorLift v 1 = 1 := by
  rw [cubicNumeratorLift_primary v primary_one,cubicSymbol_one_lower]

lemma cubicNumeratorLift_nonunit {v x : Eisenstein}
    (hx : ¬IsUnit (Ideal.Quotient.mk (modulus (9*v)) x)) : cubicNumeratorLift v x = 0 := by
  by_cases h3 : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · rw [cubicNumeratorLift,ite_eq_left h3]
    apply cubicSymbol_eq_zero_of_not_isCoprime (primaryNormalize_primary h3)
    intro hcop
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hvx : IsCoprime v x := by
      rw [← hu] at hcop
      exact hcop.of_mul_left_left.symm
    have h9x : IsCoprime (9:Eisenstein) x := by
      convert (isCoprime_of_residue_isUnit h3).pow_left (m := 2) using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    exact hx (residue_isUnit_of_isCoprime (h9x.mul_left hvx))
  · simp only [cubicNumeratorLift,ite_eq_right h3]

def cubicNumeratorChar (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) : MulChar (Residues (9*v)) ℂ where
  toFun x := cubicNumeratorLift v (residueRepresentative (9*v) x)
  map_one' := by
    rw [cubicNumeratorLift_congr hpub hv (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) 1) =
        Ideal.Quotient.mk (modulus (9*v)) 1 by rw [residueRepresentative_spec,map_one])]
    exact cubicNumeratorLift_one v
  map_mul' x y := by
    rw [cubicNumeratorLift_congr hpub hv (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) (x*y)) =
        Ideal.Quotient.mk (modulus (9*v))
          (residueRepresentative (9*v) x*residueRepresentative (9*v) y) by
            rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact cubicNumeratorLift_mul v _ _
  map_nonunit' x hx := cubicNumeratorLift_nonunit (by rwa [residueRepresentative_spec])

lemma cubicNumeratorChar_mk (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (x : Eisenstein) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) x) =
      cubicNumeratorLift v x := cubicNumeratorLift_congr hpub hv (residueRepresentative_spec _ _)

lemma cubicNumeratorChar_primary (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) {x : Eisenstein} (hx : primary x) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) x) = cubicSymbol x v := by
  rw [cubicNumeratorChar_mk,cubicNumeratorLift_primary v hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullSquarefreePrimeSupport (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) : Finset Eisenstein :=
  (orderedConvolutionSupport (fullPrimeSupport R W X)).filter
    (fun b => Squarefree b ∧ IsCoprime b e)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeMellinMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The divisor expansion of the actual radial kernel is bounded by its
literal character-row masses. This keeps the oscillation that is lost in
the coarse operator norm bound. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeMellinMass (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) : ℝ :=
  ∑ s ∈ U.powerset,
    ((∑ h ∈ H, ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)‖^2)+
     (∑ h ∈ H, ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      w a*gramMellinPhase t (y a)*star (cubicSymbol a h)‖^2))/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_KummerPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-prime factorization for arbitrary numerator,
including units and powers of the ramified prime. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicNumeratorHom (v : Eisenstein) : Eisenstein →* ℂ where
  toFun := cubicNumeratorLift v
  map_one' := cubicNumeratorLift_one v
  map_mul' := cubicNumeratorLift_mul v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the Fourier-transform frequency to the arithmetic height in
N(n)^(it). The fixed factor 2π stays in the actual kernel. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

def arithmeticMellinCoefficient (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ t : ℝ) : ℂ :=
  normDenominatorMellinCoefficient M hM V hV hV' ρ (t/(2*Real.pi))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeSchwartz
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic pullback of the radial Fourier transform is a Schwartz function. -/

noncomputable section
open scoped SchwartzMap ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubeProfileSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) : 𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLM ℂ (by fun_prop : (fun z : ℂ => z^3).HasTemperateGrowth)
    cube_norm_growth (normProfileFourierSchwartz W hW hW')

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular common-divisor mass: exact empty row, rough-divisor
split, and shortened outer-sieve bound. The constants do not depend on the
angular index, since its coefficient factors have modulus one. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def angular_fullPrimeDivisorMellinMass (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u N : ℝ) (f : Eisenstein) (t : ℝ) : ℝ :=
  ((∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖^2)+
   (∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (angularHeightPrimeCoefficient ℓ R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖^2))/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

def smoothAngularShortTwist (ℓ : ℤ) {q : Eisenstein} (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (X t : ℝ) (n : Eisenstein) : ℂ :=
  theta ℓ n*smoothShortTwist η W X t n

lemma smoothAngularShortTwist_norm (ℓ : ℤ) {q : Eisenstein} (hq : q ≠ 0)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (hW : ∀ x, ‖W x‖ ≤ 1)
    (X t : ℝ) {n : Eisenstein} (hn : n ≠ 0) :
    ‖smoothAngularShortTwist ℓ η W X t n‖ ≤ 1 := by
  rw [smoothAngularShortTwist,norm_theta_mul hn]
  exact smoothShortTwist_norm hq η W hW X t n

def angularShortFamilyOfSmoothWeights {ι : Type*} (ℓ : ℤ) (F : ℝ) (X : ι → ℝ)
    (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hA : ∀ i, ShortArithmeticFactor F (A i)) (hX : ∀ i, 1 ≤ X i)
    (hq : ∀ i, q i ≠ 0) (hW : ∀ i x, ‖W i x‖ ≤ 1) : ShortFactorFamily ι where
  cutoff := fun _ => F
  length := fun _ => X
  coefficient := fun _ => A
  twist := fun _ i => smoothAngularShortTwist ℓ (η i) (W i) (X i) (t i)
  factor_spec := fun _ => hA
  length_ge_one := fun _ => hX
  twist_bound := fun _ i _ hn => smoothAngularShortTwist_norm ℓ (hq i) (η i) (W i)
    (hW i) (X i) (t i) (primary_ne_zero (mem_primaryElementBall.mp hn).1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularWeightOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed continuous operator from logarithmic test functions to plane
annuli. It makes the angular lattice bounds uniform over the given weights. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

def angularTraceFourierCLM : 𝓢(ℂ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Complex.conjCLE.trans (complexMulEquiv 2 (by norm_num)))).comp
      (SchwartzMap.fourierTransformCLM ℂ)).restrictScalars ℝ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def squarefreeProductEnvelope (Y : ℝ) : Finset Eisenstein :=
  (primaryElementBall Y).filter Squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The product-envelope Type-I integral equals the literal finite
height-Fourier kernel used in the detector decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def centeredHeightKernel (ℓ : ℤ) (W : ℝ → ℂ) (H T X X₀ : ℝ)
    (n : Eisenstein) : ℂ :=
  theta ℓ n*centeredGauss n*W (norm n/X)*
    heightFourierIntegral (lowHeightWeight H T) (Real.log (norm n)-Real.log X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredMellinWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a centered polynomial bound through the actual finite
Mellin window and the original low-height weight. The complementary
Mellin tail is kept separate and is not bounded by this lemma. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def centeredMellinWindow (A B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (X S u : ℝ) : ℂ :=
  ∫ τ in Icc (-S) S, zeroLineMellinWeight W X τ*
    centeredProductPolynomial A B α β ℓ (u-τ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_PrimeProductDetector
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the manuscript's exact prime detector to the actual central
integral kernel. The support is a concrete subset of the primary lattice,
with both norm endpoints enforced before the detector is invoked. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeProductSupport (X : ℝ) : Finset Eisenstein :=
  (squarefreeProductEnvelope (3*X)).filter (fun n => X/2 ≤ norm n)

def centralRoughProduct (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*
      centeredHeightKernel ℓ primeProductEnvelope H T X X n

def centralSemiprimeProduct (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ n ∈ primeProductSupport X with (primeFactors n).card = 2,
    (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*
      centeredHeightKernel ℓ primeProductEnvelope H T X X n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def semiprimePartitionCoefficient (X : ℝ) (j : ℕ) (p : Eisenstein) : ℂ :=
  semiprimeSmoothWeight (semiprimePartitionScale j/(X^(2/5:ℝ)))
    (norm p/semiprimePartitionScale j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeFullSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In a semiprime piece the full independent smooth prime supports can
replace the auxiliary cutoff at 3X. Extra primes give a zero product
envelope; missing primes have zero coordinate weight. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def semiprimeFullSupport (X : ℝ) (i : ℕ) : Finset Eisenstein :=
  fullPrimeSupport 2
    (fun _ : Unit => semiprimeSmoothWeight (semiprimePartitionScale i/(X^(2/5:ℝ))))
    (fun _ => semiprimePartitionScale i) ()

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CentralProductSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth product kernel permits the exact detector support to be
replaced by its full squarefree envelope. No nonzero term is removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def centralProductEnvelope (X : ℝ) : Finset Eisenstein :=
  squarefreeProductEnvelope (Real.exp primeProductWeights.radius*X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CentralStoppingDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact central stopping decomposition, with the whole distinguished
no-stop branch already controlled. The remaining terms are the literal
stopped matrix and the large distinguished-product rows. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def centralPrimaryFactors (X : ℝ) : Finset Eisenstein :=
  primaryElementBall (Real.exp primeProductWeights.radius*X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite smooth norm partition of the literal large-row prime tuples.
Every original support condition stays inside each summand. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleBox (i j : ℕ) (X : ℝ) :
    Finset ((Fin i → Eisenstein) × (Fin j → Eisenstein)) :=
  (Fintype.piFinset (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))).product
    (Fintype.piFinset (fun _ : Fin j => primeCutoff (Real.exp primeProductWeights.radius*X)))

def largePrimeTupleTerm (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : ℂ :=
  if (∏ a, q.1 a) ∈ (centralPrimaryFactors X).filter
      (fun r => ¬norm r < X^(38/100:ℝ)) then
    if (∏ b, q.2 b) ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (∏ a, q.1 a) then
      (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
        (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
          X X ((∏ a, q.1 a)*(∏ b, q.2 b))
    else 0
  else 0

def largePrimeTupleNorm {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : (Fin i ⊕ Fin j) → ℝ :=
  Sum.elim (fun a => norm (q.1 a)) (fun b => norm (q.2 b))

def largePrimeTuplePiece (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ q ∈ largePrimeTupleBox i j X,
      largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleExponents
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized logarithmic prime sizes in the actual large-row support.
They form a positive partition of one uniformly away from two thirds. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def largePrimeTupleProduct {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : Eisenstein :=
  (∏ a, q.1 a)*(∏ b, q.2 b)

def largePrimeTupleExponent {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) (a : Fin i ⊕ Fin j) : ℝ :=
  Real.log (largePrimeTupleNorm q a)/Real.log (norm (largePrimeTupleProduct q))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleGrouping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform grouping for the actual large-row prime tuples, outside the
specified neighborhood of the exceptional three-prime configuration. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def largePrimeTupleExceptional {i j : ℕ} (δ : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : Prop :=
  i+j = 3 ∧ (∑ a, |largePrimeTupleExponent q a-1/3|) < δ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleFlatCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The log-log count for flat triples applied to the actual nonzero
large-row partition pieces, with the original product cutoff intact. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleFlatBoxSet (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct G : ℕ) (H X : ℝ) :
    Finset ((Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :=
  Finset.univ.filter (fun d => largePrimeTuplePiece i j ℓ ξ Ct H X d ≠ 0 ∧
    ∃ B : ℝ, (∀ a, largeTupleNormScale (fun a => (d a).val) a ≤ B) ∧
      B^3 ≤ (∏ a, largeTupleNormScale (fun a => (d a).val) a)*(1+Real.log X)^G)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeTupleSelectedFlat
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
variable (ℓ : ℤ)

def angular_largePrimeTupleSelectedFlatHighSum (i j : ℕ) (ξ : ℝ) (Ct G : ℕ) (H X : ℝ)
    (select : ((Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) → Prop) : ℂ :=
  ∑ d ∈ largePrimeTupleFlatBoxSet i j ℓ ξ Ct G H X,
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧ select d then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeTupleExceptionalHigh
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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
variable (ℓ : ℤ)

def angular_largePrimeTupleExceptionalHighSum (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      ¬(∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

def angular_largeTupleExceptionalSelector (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : Prop :=
  ¬∃ q ∈ largePrimeTupleBox i j X,
    largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
      ¬largePrimeTupleExceptional δ q

def angular_largePrimeTupleExceptionalNonflatSum (i j : ℕ) (ξ δ : ℝ) (Ct G : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if (X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      angular_largeTupleExceptionalSelector ℓ i j ξ δ Ct H X d) ∧
      d ∉ largePrimeTupleFlatBoxSet i j ℓ ξ Ct G H X then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeTupleOrdinarySum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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
variable (ℓ : ℤ)

def angular_largePrimeTupleOrdinaryHighSum (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      (∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLargeTupleHighSum
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
variable (ℓ : ℤ)

def angular_largePrimeTupleHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      largePrimeTuplePiece i j ℓ ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TypeIProductWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def productGaussHeightWindowKernel (ℓ : ℤ) (W : ℝ → ℂ) (H T X X₀ : ℝ)
    (n : Eisenstein) : ℂ :=
  theta ℓ n*gauss n*W (norm n/X)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
      (Real.log (norm n)-Real.log X₀)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedNoStopWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The surviving no-stop part at a dyadic height. Its failed-prefix
predicate remains in the actual coefficient when Type I is applied. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def restrictedNoStopGaussWindowValue (R : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ Z B : ℝ) (ℓ : ℤ) (W : ℝ → ℂ)
    (H T X X₀ : ℝ) (P : Eisenstein → Eisenstein → Prop) : ℂ :=
  ∑ r ∈ R, v r*∑ u ∈ primaryElementBall (B*X),
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope (B*X)) (B*X) (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ (B*X)) (geometricBinLower ρ (B*X)) < Z ∧ P r m,
      cutoffMoebius ψ w m*productGaussHeightWindowKernel ℓ W H T X X₀ (r*(m*u))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMatrixDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent sharp side dyads for the stopped matrices. The
squarefree product envelope supplies the side support; no coprimality
restriction or boundary contribution is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedFactorSupport (P : Finset Eisenstein) (X : ℝ) : Finset Eisenstein :=
  P.filter (fun a => Squarefree a ∧ norm a ≤ Real.exp primeProductWeights.radius*X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedScalePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript partitions the distinguished prime scales before
splitting the rough remainder. This exact finite partition introduces no
partial-product cutoff in a high-scale coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedScaleCoefficient (i : ℕ) (ξ X : ℝ)
    (k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (r : Eisenstein) : ℂ :=
  distinguishedTupleCoefficient
    (fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X))
    (fun a p => normPartitionWeight (2*norm p/(4/3:ℝ)^(k a).val))
    primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RestrictedNoStopCentral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original no-stop branch, retaining an arbitrary extra predicate
on the two outer factors, obeys the derived central Type-I estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def restrictedNoStopCenteredValue (R : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w ρ Z B : ℝ) (ℓ : ℤ) (W : ℝ → ℂ)
    (H T X X₀ : ℝ) (P : Eisenstein → Eisenstein → Prop) : ℂ :=
  ∑ r ∈ R, v r*∑ u ∈ primaryElementBall (B*X),
    ∑ m ∈ primaryProductSlice (squarefreeProductEnvelope (B*X)) (B*X) (r*u) with
      norm r*primeSurrogate (primaryPrimeFactors m)
        (geometricPrimeBin ρ (B*X)) (geometricBinLower ρ (B*X)) < Z ∧ P r m,
      cutoffMoebius ψ w m*centeredHeightKernel ℓ W H T X X₀ (r*(m*u))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStopping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def stoppingFailedPrefix (ρ F Q : ℝ) (h : ℕ) (r m : Eisenstein) : Prop :=
  norm r*primeSurrogate
    (primeBinPrefix (primaryPrimeFactors m) (geometricPrimeBin ρ F) h)
    (geometricPrimeBin ρ F) (geometricBinLower ρ F) < Q

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstStoppedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def distinguishedStoppedAlpha (ρ ξ X : ℝ) (q : ℕ × ℕ × ℕ) : Eisenstein → ℂ :=
  stoppedAlpha (centralPrimaryFactors X) (centralPrimaryFactors X)
    primeDetectorCutoff (X^ξ)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)

def distinguishedStoppedBeta (i : ℕ) (ρ ξ X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) : Eisenstein → ℂ :=
  stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1 h
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early)

def distinguishedStoppedSide (X : ℝ) : Finset Eisenstein :=
  stoppedFactorSupport (primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X)) X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def scaleFirstTailKernel (ℓ : ℤ) (H U X : ℝ) (n : Eisenstein) : ℂ :=
  theta ℓ n*gauss n*primeProductEnvelope (norm n/X)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow U t)
      (Real.log (norm n)-Real.log X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTailDecompositionRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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

def scaleFirstTailScaleRow (i : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X d r*
    ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
      (Real.exp primeProductWeights.radius*X) r,
      (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*scaleFirstTailKernel ℓ H U X (r*u)

def scaleFirstTailNoStopRow (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ r ∈ centralPrimaryFactors X, distinguishedScaleCoefficient i ξ X d r*
    ∑ u ∈ centralPrimaryFactors X,
      ∑ m ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) (r*u) with
        stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h r m ∧
        norm r*primeSurrogate (primaryPrimeFactors m)
          (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
          (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) < X^(38/100:ℝ),
        cutoffMoebius primeDetectorCutoff (X^ξ) m*scaleFirstTailKernel ℓ H U X (r*(m*u))

def scaleFirstTailStoppedRow (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ) (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
      (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
    (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
      ∑ a ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
        ∑ b ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
          distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
            (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaleFirstTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full tuple pieces for the scale-first branch. The smooth total
product kernel enforces the squarefree envelope; no lower cutoff on the
actual distinguished product is inserted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def uncutPrimeTupleTerm (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : ℂ :=
  (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
    centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
      X X (largePrimeTupleProduct q)

def scaleFirstPrimeTuplePiece (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ q ∈ largePrimeTupleBox i j X,
      uncutPrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNoStopNegligible
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
variable (ℓ : ℤ)

def angular_scaleFirstOrdinaryNoStopArity (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(69/200:ℝ) then
          scaleFirstTailNoStopRow i ℓ ρ ξ H (T*(3/2:ℝ)^s) X h d else 0
    else 0

def angular_scaleFirstOrdinaryNoStopTail (m : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) : ℂ :=
  ∑ i ∈ Finset.range m, angular_scaleFirstOrdinaryNoStopArity ℓ i ρ ξ H T X h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular numerator character on the original modulus `9*v`.
The finite correction at three is absorbed into this modulus, so its norm
bound remains `81*N(v)`. -/
noncomputable section
namespace CubicFirstMoment

lemma angularNumeratorLift_mul (v x y : Eisenstein) (ℓ : ℤ) :
    angularNumeratorLift v ℓ (x*y)=angularNumeratorLift v ℓ x*angularNumeratorLift v ℓ y := by
  simp only [angularNumeratorLift,cubicNumeratorLift_mul,angularUnitCorrection_mul]
  ring

def angularNumeratorChar (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) : MulChar (Residues (9*v)) ℂ where
  toFun x := angularNumeratorLift v ℓ (residueRepresentative (9*v) x)
  map_one' := by
    rw [angularNumeratorLift_congr hpub hv ℓ (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) 1)=
        Ideal.Quotient.mk (modulus (9*v)) 1 by rw [residueRepresentative_spec,map_one])]
    simp only [angularNumeratorLift,cubicNumeratorLift_one,angularUnitCorrection_one,one_mul]
  map_mul' x y := by
    rw [angularNumeratorLift_congr hpub hv ℓ (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) (x*y))=
        Ideal.Quotient.mk (modulus (9*v))
          (residueRepresentative (9*v) x*residueRepresentative (9*v) y) by
            rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact angularNumeratorLift_mul v _ _ ℓ
  map_nonunit' x hx := by
    have hn : ¬IsUnit (Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) x)) :=
      by rwa [residueRepresentative_spec]
    simp only [angularNumeratorLift,cubicNumeratorLift_nonunit hn,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedAggregation
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
variable (ℓ : ℤ)

def angular_scaleFirstStoppedEnvelopeTail (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedRow i ℓ ρ ξ H (T*(3/2:ℝ)^s) X h early d
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularOrdinaryStoppedTail
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
variable (ℓ : ℤ)

def angular_scaleFirstStoppedWindow (i : ℕ) (ρ ξ H U X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      scaleFirstTailStoppedRow i ℓ ρ ξ H U X h early d else 0

def angular_scaleFirstOrdinaryStoppedArity (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      angular_scaleFirstStoppedWindow ℓ i ρ ξ H (T*(3/2:ℝ)^s) X h early else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularOrdinaryTail
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
variable (ℓ : ℤ)

def angular_scaleFirstOrdinaryLowArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(69/200:ℝ) then
          scaleFirstTailScaleRow i ℓ ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def angular_scaleFirstOrdinaryLowTail (m : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, angular_scaleFirstOrdinaryLowArity ℓ i ξ H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularRestrictedNoStopParameters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
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
variable (ℓ : ℤ)

def angular_distinguishedScaleNoStop (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (P : Eisenstein → Eisenstein → Prop) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      restrictedNoStopCenteredValue (centralPrimaryFactors X)
        (distinguishedScaleCoefficient i ξ X k) primeDetectorCutoff (X^ξ) ρ
        (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) ℓ primeProductEnvelope
        H ((1+Real.log X)^Ct) X X P else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstMiddleSum
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
variable (ℓ : ℤ)

def angular_scaleFirstMiddleSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleDistinguishedScale (fun a => (d a).val) < X^(38/100:ℝ) then
      scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstHighSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-scale branch is negligible. The middle interval is treated
by its distinguished group; the higher interval is the large-row high sum. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_scaleFirstHighSum (i j : ℕ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      scaleFirstPrimeTuplePiece i j ℓ ξ Ct H X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularScaleFirstStoppedDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact fixed-angular low-height stopping rows, retaining the original
coefficients, product support, and inverse-binomial factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def angular_distinguishedScaleStoppedRow (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
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
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

def angular_distinguishedScaleStopped (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool) : ℂ :=
  ∑ k : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength k < X^(69/200:ℝ) then
      angular_distinguishedScaleStoppedRow ℓ i ρ ξ Ct H X h early k else 0

def angular_scaleFirstStoppedSum (ℓ : ℤ) (m : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ)
    (h : ℕ) (early : Bool) : ℂ :=
  ∑ i ∈ Finset.range m, angular_distinguishedScaleStopped ℓ i ρ ξ Ct H X h early

def angular_distinguishedStoppedDyad (ℓ : ℤ) (i : ℕ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) : ℂ :=
  ∑ a ∈ stoppedNormDyad (distinguishedStoppedSide X) j,
    ∑ b ∈ stoppedNormDyad (distinguishedStoppedSide X) k,
      distinguishedStoppedAlpha ρ ξ X q a*distinguishedStoppedBeta i ρ ξ X h early d q b*
        (if a*b ∈ centralProductEnvelope X then
          centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSemiprimeSmoothed
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angularSemiprimeSmoothedPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  centeredProductSmoothed (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
    ℓ primeProductEnvelope X u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDistinguishedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def angular_stoppedDistinguishedRows (ℓ : ℤ) (B ρ a b w z u : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (W : ι → ℝ → ℂ) (D : Finset Eisenstein)
    (v e : Eisenstein) (i : ι) : ℂ :=
  ∑ t ∈ (coordinateComplementTuples (fun _ : ι => primeCutoff B) i ×ˢ D).filter
      (fun t => Squarefree ((∏ l, t.1 l)*t.2) ∧ IsCoprime ((∏ l, t.1 l)*t.2) e),
    (∏ l ∈ Finset.univ.erase i, distinguishedRadialWeight (W l) w z (norm (t.1 l)))*
    (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early
        (∏ l, t.1 l) t.2 ((∏ l, t.1 l)*(t.2*e)),
      cutoffMoebius primeDetectorCutoff w t.2*distinguishedRadialWeight (W i) w z (norm p)*
        normTwist u (((∏ l, t.1 l)*p)*t.2)*angularCubicSymbol ℓ (((∏ l, t.1 l)*p)*t.2) v)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedSelectedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def angular_stoppedSelectedPrimeRow (ℓ : ℤ) (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c v e : Eisenstein) : ℂ :=
  ∑ p ∈ stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e,
    cutoffMoebius primeDetectorCutoff w (p*c)*normTwist u (r*(p*c))*angularCubicSymbol ℓ (r*(p*c)) v


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedLongBinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def angular_stoppedCharacterSum (ℓ : ℤ) (B w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) : ℂ :=
  ∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B))
      (primaryElementBall B),
    stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) (primaryElementBall B)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
        (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected n*
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*angularCubicSymbol ℓ n v else 0)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperTailStopping
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper-height branch uses one stopping threshold, X^(1/3-κ).
The identity retains the actual envelope and inverse binomial weights. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def upperTailNoStopRow (i : ℕ) (ℓ : ℤ) (κ ρ ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  restrictedNoStopGaussWindowValue (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ) ρ
    (X^(1/3-κ)) (Real.exp primeProductWeights.radius) ℓ primeProductEnvelope H U X X
    (fun _ _ => True)

def upperTailStoppedRow (i : ℕ) (ℓ : ℤ) (κ ρ ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  let F := Real.exp primeProductWeights.radius*X
  ∑ q ∈ stoppingLabelBox ρ F, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
    ∑ a ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
      ∑ b ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
        stoppedAlpha (centralPrimaryFactors X) (centralPrimaryFactors X) primeDetectorCutoff
            (X^ξ) (stoppingRemainingTest (geometricPrimeBin ρ F) q.1 q.2.2) a *
          stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
            (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
            (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
              q.1 q.2.1 0 (X^(1/3-κ)) (X^(1/3-κ)) true) b *
          (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUpperNoStopNegligible
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
variable (ℓ : ℤ)

def angular_upperNoStopArity (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(1/3-2*κ) then
          upperTailNoStopRow i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def angular_upperNoStopTail (m : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, angular_upperNoStopArity ℓ i κ ρ ξ H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUpperTailAggregation
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
variable (ℓ : ℤ)

def angular_upperStoppedEnvelopeTail (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        upperTailStoppedRow i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUpperStoppedSuffix
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
variable (ℓ : ℤ)

def angular_upperStoppedWindow (i : ℕ) (κ ρ ξ H U X : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(1/3-2*κ) then
      upperTailStoppedRow i ℓ κ ρ ξ H U X d else 0

def angular_upperStoppedFilteredArity (i : ℕ) (κ ρ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      angular_upperStoppedWindow ℓ i κ ρ ξ H (T*(3/2:ℝ)^s) X else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularUpperLowTail
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
variable (ℓ : ℤ)

def angular_upperLowArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
        if distinguishedScaleLength d < X^(1/3-2*κ) then
          scaleFirstTailScaleRow i ℓ ξ H (T*(3/2:ℝ)^s) X d else 0
    else 0

def angular_upperLowTail (m : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ i ∈ Finset.range m, angular_upperLowArity ℓ i κ ξ H T X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UpperTailTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime-tuple Gauss kernel for upper height windows.
The high branch begins at X^(1/3-2κ), in the prime decomposition. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def tailPrimeTupleTerm (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : ℂ :=
  (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (q.1 a))*
    (∏ b, (1-(primeDetectorCutoff (norm (q.2 b)/(X^ξ)):ℂ)))*
    productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (largePrimeTupleProduct q)

def tailPrimeTuplePiece (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailHighCollection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of Gauss height-tail rows above any fixed scale threshold.
This retains the independent smooth norm partitions and product envelope. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailHighScaleRows (i : ℕ) (ℓ : ℤ) (ξ H U X V : ℝ) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if V ≤ distinguishedScaleLength d then scaleFirstTailScaleRow i ℓ ξ H U X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailHighDecomposition
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
variable (ℓ : ℤ)

def angular_tailHighOrdinaryArity (i : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      tailHighScaleRows i ℓ ξ H (T*(3/2:ℝ)^s) X (X^(69/200:ℝ)) else 0

def angular_tailHighUpperArity (i : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^s then
      tailHighScaleRows i ℓ ξ H (T*(3/2:ℝ)^s) X (X^(1/3-2*κ)) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailPrimeOrdinaryTuple
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
variable (ℓ : ℤ)

def angular_tailPrimeOrdinaryTuple (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
      tailPrimeTuplePiece i j ℓ ξ H (T*(3/2:ℝ)^v) X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailHighOrdinaryNegligible
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
variable (ℓ : ℤ)

def angular_tailPrimeOrdinaryTupleSum (i j : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      angular_tailPrimeOrdinaryTuple ℓ i j ξ H T X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailPrimeTailGeometry
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
variable (ℓ : ℤ)

def angular_tailPrimeTupleTail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    tailPrimeTuplePiece i j ℓ ξ H (T*(3/2:ℝ)^v) X k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailPrimeUpperTuple
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
variable (ℓ : ℤ)

def angular_tailPrimeUpperTuple (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^v then
      tailPrimeTuplePiece i j ℓ ξ H (T*(3/2:ℝ)^v) X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTailHighUpperNegligible
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
variable (ℓ : ℤ)

def angular_tailPrimeUpperTupleSum (i j : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      angular_tailPrimeUpperTuple ℓ i j ξ H T X d else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorOrder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic numerator characters have odd order. In particular a
nonprincipal one is not self-conjugate, as required when excluding the
real-character exceptional term in the prime estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorChar_ne_one_iff (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) :
    cubicNumeratorChar hpub v hv ≠ 1 ↔ ∃ a : Eisenstein,
      primary a ∧ IsCoprime (9*v) a ∧ cubicSymbol a v ≠ 1 := by
  constructor
  · intro hn
    obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hn
    let x := residueRepresentative (9*v) u
    have hx : IsUnit (Ideal.Quotient.mk (modulus (9*v)) x) := by
      simpa only [x,residueRepresentative_spec] using u.isUnit
    have hc := isCoprime_of_residue_isUnit hx
    have hc3 : IsCoprime (3:Eisenstein) x := hc.of_isCoprime_of_dvd_left ⟨3*v,by ring⟩
    have hx3 := residue_isUnit_of_isCoprime hc3
    obtain ⟨w,hw⟩ := primaryNormalize_associated x
    refine ⟨primaryNormalize x,primaryNormalize_primary hx3,?_,?_⟩
    · rw [←hw]
      exact (isCoprime_mul_unit_right_right w.isUnit (9*v) x).mpr hc
    · change cubicNumeratorLift v x ≠ 1 at hu
      simpa only [cubicNumeratorLift,ite_eq_left hx3] using hu
  · rintro ⟨a,ha,hcop,hval⟩ he
    have h := cubicNumeratorChar_primary hpub v hv ha
    rw [he,MulChar.one_apply (residue_isUnit_of_isCoprime hcop)] at h
    exact hval h.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCubeFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by a nonzero cube changes only deleted Euler factors,
not principality of the cubic numerator character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicNumeratorChar_mul_cube_ne_one (hpub : CubicSupplementaryPeriodicity)
    {r c : Eisenstein} (hr : r ≠ 0) (hc : c ≠ 0)
    (hn : cubicNumeratorChar hpub r hr ≠ 1) :
    cubicNumeratorChar hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc)) ≠ 1 := by
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hpub r hr).mp hn
  obtain ⟨y,hy,hcy⟩ := exists_coprime_residue_lift hc hcop
  have hyx : (3:Eisenstein) ∣ y-x :=
    (show (3:Eisenstein) ∣ 9*r from ⟨3*r,by ring⟩).trans hy
  have hyp : primary y := by
    change (3:Eisenstein) ∣ y-1
    convert dvd_add hyx hx using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hyc : IsCoprime y c := hcy.of_mul_left_right.symm
  have hyr : IsCoprime r y := hcy.of_mul_left_left.of_mul_left_right
  have hy9 : IsCoprime (9:Eisenstein) y := hcy.of_mul_left_left.of_mul_left_left
  apply (cubicNumeratorChar_ne_one_iff hpub (r*c^3) (mul_ne_zero hr (pow_ne_zero _ hc))).mpr
  refine ⟨y,hyp,hy9.mul_left (hyr.mul_left (hyc.symm.pow_left (m := 3))),?_⟩
  rw [cubicSymbol_mul_upper hyp,cubicSymbol_pow_upper hyp,
    cubicSymbol_cube_of_isCoprime hyp c hyc,mul_one,hpub r hr y x hyp hx hy]
  exact hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedCubicNonprincipal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonprincipality in the unit/ramified part, detected by the primary
arguments -2 and 1+3 omega. -/
noncomputable section
namespace CubicFirstMoment

lemma unit_ramified_cubic_nonprincipal (hpub : CubicSupplementaryPeriodicity)
    {u : Eisenstein} (hu : IsUnit u) (k : ℕ)
    (hn : ¬∃ c : Eisenstein, c^3=u*lambdaE^k) :
    cubicNumeratorChar hpub (u*lambdaE^k)
      (mul_ne_zero hu.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)) ≠ 1 := by
  obtain ⟨j,hj⟩ := eisenstein_unit_eq_signed_omega hu
  have hnot : ¬(3 ∣ j ∧ 3 ∣ k) := fun h => hn (ramified_cube_of_three_dvd hj h.1 h.2)
  apply (cubicNumeratorChar_ne_one_iff hpub _ _).mpr
  by_cases hj3 : 3 ∣ j
  · have hk3 : ¬3 ∣ k := fun hk => hnot ⟨hj3,hk⟩
    let x : Eisenstein := 1+3*omegaE
    have hx : primary x := primary_seven_factor
    have hval : cubicSymbol x u=1 := by
      have he : omega^(2*j)=1 :=
        (omega_primitive.pow_eq_one_iff_dvd _).mpr (dvd_mul_of_dvd_right hj3 2)
      rcases hj with rfl | rfl <;>
        simpa only [cubicSymbol_neg hx,cubicSymbol_pow_upper hx,x,
          cubicSymbol_seven_factor_omega,pow_mul] using he
    have hx9 : IsCoprime (9:Eisenstein) x := by
      convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    refine ⟨x,hx,hx9.mul_left ((unit_coprime_every _ _ hu).mul_left
      ((primary_coprime_lambda hx).symm.pow_left)),?_⟩
    rw [cubicSymbol_mul_upper hx,hval,one_mul,cubicSymbol_pow_upper hx,
      cubicSymbol_seven_factor_lambda,←pow_mul]
    intro he
    have hd := omega_primitive.dvd_of_pow_eq_one _ he
    exact hk3 ((Nat.prime_three.dvd_mul).mp hd |>.resolve_left (by norm_num))
  · have hx := primary_neg_two
    have hx9 : IsCoprime (9:Eisenstein) (-2:Eisenstein) := by
      convert ((primary_coprime_three hx).symm.pow_left (m := 2)) using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    refine ⟨-2,hx,hx9.mul_left ((unit_coprime_every _ _ hu).mul_left
      ((primary_coprime_lambda hx).symm.pow_left)),?_⟩
    rw [cubicSymbol_mul_upper hx,cubicSymbol_pow_upper hx,
      cubicSymbol_neg_two_lambda,one_pow,mul_one]
    have he : omega^j ≠ 1 := fun h => hj3 (omega_primitive.dvd_of_pow_eq_one _ h)
    rcases hj with rfl | rfl <;>
      simpa only [cubicSymbol_neg hx,cubicSymbol_pow_upper hx,cubicSymbol_neg_two_omega] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every noncube numerator defines a nonprincipal cubic character.
The proof keeps ramification and cube-factor deletions explicit. -/
noncomputable section
namespace CubicFirstMoment

lemma nonprincipal_transport (hpub : CubicSupplementaryPeriodicity)
    {v w : Eisenstein} (hv : v ≠ 0) (hw : w ≠ 0) (h : v=w) :
    (cubicNumeratorChar hpub v hv ≠ 1) ↔ (cubicNumeratorChar hpub w hw ≠ 1) := by
  subst w
  rfl

lemma mixed_ramified_cubic_nonprincipal (hpub : CubicSupplementaryPeriodicity)
    {r s t : Eisenstein} (hr : r ≠ 0) (hs : primary s) (ht : primary t)
    (hss : Squarefree s) (hst : Squarefree t) (hcop : IsCoprime s t)
    (hnu : ¬IsUnit (s*t)) (hrst : IsCoprime (s*t) r) :
    cubicNumeratorChar hpub (r*s*t^2)
      (mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs)) (pow_ne_zero _ (primary_ne_zero ht))) ≠ 1 := by
  obtain ⟨y,hy,hyc,hyne⟩ := mixedCubic_nonprincipal hs ht hss hst hcop hnu
  have hst9 : IsCoprime (s*t) (9:Eisenstein) := by
    convert (primary_coprime_three (primary_mul hs ht)).pow_right (n := 2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  obtain ⟨x,hxy,hxone⟩ := residue_crt_one (hst9.mul_right hrst) y
  have hx : primary x := (show (3:Eisenstein) ∣ 9*r from ⟨3*r,by ring⟩).trans hxone
  have hxst : IsCoprime (s*t) x := isCoprime_of_residue_congr hxy hyc
  have hx9r := isCoprime_of_dvd_sub_one hxone
  have hx9 := hx9r.of_mul_left_left
  have hxr := hx9r.of_mul_left_right
  have hxv : IsCoprime (r*s*t^2) x :=
    (hxr.mul_left hxst.of_mul_left_left).mul_left (hxst.of_mul_left_right.pow_left (m := 2))
  have hxrval : cubicSymbol x r=1 :=
    (hpub r hr x 1 hx primary_one hxone).trans (cubicSymbol_one_lower r)
  have hmix : mixedCubic s t x=mixedCubic s t y := by
    unfold mixedCubic
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub ((dvd_mul_right s t).trans hxy)),
      cubicSymbol_congr (residue_eq_of_dvd_sub ((dvd_mul_left t s).trans hxy))]
  apply (cubicNumeratorChar_ne_one_iff hpub _ _).mpr
  refine ⟨x,hx,hx9.mul_left hxv,?_⟩
  rw [cubicSymbol_mul_upper hx,cubicSymbol_mul_upper hx,hxrval,one_mul,
    cubicSymbol_pow_upper hx,cubicSymbol_sq_eq_star hx,
    cubic_reciprocity hx hs,cubic_reciprocity hx ht]
  change mixedCubic s t x ≠ 1
  rwa [hmix]

/-- Nonprincipality for the full numerator, with no squarefreeness,
primarity, unit, or ramification restrictions. -/
theorem cubicNumeratorChar_noncube (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) (hn : ¬∃ j : Eisenstein, j^3=v) :
    cubicNumeratorChar hpub v hv ≠ 1 := by
  obtain ⟨u,k,a,ha,hva⟩ := unit_ramified_primary_decomposition hv
  obtain ⟨s,t,c,hs,ht,hc,hss,hst,hcop,haeq⟩ := primary_cube_decomposition ha
  let r : Eisenstein := (u:Eisenstein)*lambdaE^k
  have hr : r ≠ 0 := mul_ne_zero u.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero)
  have he : v=(r*s*t^2)*c^3 := by rw [hva,haeq]; dsimp [r]; ring
  have hbase : r*s*t^2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs)) (pow_ne_zero _ (primary_ne_zero ht))
  have hbasechar : cubicNumeratorChar hpub (r*s*t^2) hbase ≠ 1 := by
    by_cases hunit : IsUnit (s*t)
    · have hs1 := primary_unit_eq_one (isUnit_of_mul_isUnit_left hunit) hs
      have ht1 := primary_unit_eq_one (isUnit_of_mul_isUnit_right hunit) ht
      have hnr : ¬∃ j : Eisenstein, j^3=r := by
        rintro ⟨j,hj⟩
        apply hn
        refine ⟨j*c,?_⟩
        rw [mul_pow,hj,he,hs1,ht1,one_pow,mul_one,mul_one]
      have hunitbase : r*s*t^2=r := by rw [hs1,ht1]; ring
      exact (nonprincipal_transport hpub hbase hr hunitbase).mpr
        (unit_ramified_cubic_nonprincipal hpub u.isUnit k hnr)
    · have hru : IsCoprime (s*t) (u:Eisenstein) :=
        (isCoprime_zero_left.mpr u.isUnit).of_isCoprime_of_dvd_left (dvd_zero (s*t))
      have hrst : IsCoprime (s*t) r :=
        hru.mul_right ((primary_coprime_lambda (primary_mul hs ht)).pow_right (n := k))
      exact mixed_ramified_cubic_nonprincipal hpub hr hs ht hss hst hcop hunit hrst
  have hout := cubicNumeratorChar_mul_cube_ne_one hpub hbase (primary_ne_zero hc) hbasechar
  exact (nonprincipal_transport hpub hv _ he).mpr hout

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows of the full Eisenstein modular group. Their proper
height function gives the full-group reduction needed for a finite cusp
cover of the principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaPrimitiveRow_height_superlevel_finite {p : ℂ × ℝ} (hp : 0<p.2)
    {a : ℝ} (ha : 0<a) : Set.Finite {r : CubicThetaPrimitiveRow | a ≤ r.height p} := by
  let K := 2+(1+2*Complex.normSq p.1)/p.2^2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (by norm_num) (div_nonneg (by linarith [Complex.normSq_nonneg p.1]) (sq_nonneg _))
  let B := K*(p.2/a)
  have hfin : Set.Finite {r : CubicThetaPrimitiveRow | norm r.c ≤ B ∧ norm r.d ≤ B} := by
    have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
      intro r t he
      exact CubicThetaPrimitiveRow.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2
    exact ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  apply hfin.subset
  intro r hr
  have hD : r.denominator p ≤ p.2/a := by
    apply (le_div_iff₀ ha).mpr
    have h := (le_div_iff₀ (r.denominator_pos hp)).mp hr
    nlinarith
  have hb : norm r.c+norm r.d ≤ B :=
    (r.norm_sum_bound hp).trans (mul_le_mul_of_nonneg_left hD hK)
  exact ⟨by linarith [norm_nonneg r.d],by linarith [norm_nonneg r.c]⟩

theorem cubicThetaFullGroup_exists_max_height {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ g : SL(2,Eisenstein), ∀ h : SL(2,Eisenstein),
      (cubicThetaMobius (cubicThetaFullComplex h) p).2 ≤
        (cubicThetaMobius (cubicThetaFullComplex g) p).2 := by
  let r0 := cubicThetaPrimitiveRow (1 : SL(2,Eisenstein))
  let S : Set CubicThetaPrimitiveRow := {r | r0.height p ≤ r.height p}
  have hfin : S.Finite := cubicThetaPrimitiveRow_height_superlevel_finite hp (r0.height_pos hp)
  have hne : hfin.toFinset.Nonempty := ⟨r0,by simp [S]⟩
  obtain ⟨r,hr,hmax⟩ := hfin.toFinset.exists_max_image (fun r => r.height p) hne
  obtain ⟨g,rfl⟩ := cubicThetaPrimitiveRow_surjective r
  refine ⟨g,?_⟩
  intro h
  change (cubicThetaPrimitiveRow h).height p ≤ (cubicThetaPrimitiveRow g).height p
  by_cases hh : r0.height p ≤ (cubicThetaPrimitiveRow h).height p
  · exact hmax _ (by simpa [S] using hh)
  · exact (lt_of_not_ge hh).le.trans (by simpa [S] using hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSiegelReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Siegel-set reduction for the full Eisenstein modular group, and
its finite translate cover of the actual principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaFullInversion_complex :
    cubicThetaFullComplex cubicThetaFullInversion=cubicThetaInversionMatrix 1 one_ne_zero := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (change (-1:ℂ)= -(1:ℂ)⁻¹; norm_num)

lemma cubicThetaFullInversion_height (p : ℂ × ℝ) :
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p).2=
      p.2/(Complex.normSq p.1+p.2^2) := by
  rw [cubicThetaFullInversion_complex]
  simp [cubicThetaMobius,cubicThetaMobiusDenominator,cubicThetaInversionMatrix]

theorem cubicThetaSiegelSet_meets_orbit {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ u : SL(2,Eisenstein), cubicThetaMobius (cubicThetaFullComplex u) p∈cubicThetaSiegelSet := by
  obtain ⟨g,hg⟩ := cubicThetaFullGroup_exists_max_height hp
  let q := cubicThetaMobius (cubicThetaFullComplex g) p
  let m := -nearestEisenstein q.1
  let u := cubicThetaFullTranslation m*g
  have hu : cubicThetaMobius (cubicThetaFullComplex u) p=
      (q.1-(nearestEisenstein q.1:ℂ),q.2) := by
    dsimp only [u]
    rw [map_mul,← cubicThetaMobius_comp _ _ hp,cubicThetaFullTranslation_complex,
      cubicThetaMobius_translation]
    simp only [m,Subalgebra.coe_neg,sub_eq_add_neg]
    rfl
  have hq : 0<q.2 := cubicThetaMobius_height_pos _ hp
  have hmax (h : SL(2,Eisenstein)) :
      (cubicThetaMobius (cubicThetaFullComplex h) p).2 ≤
        (cubicThetaMobius (cubicThetaFullComplex u) p).2 := by
    rw [hu]
    exact hg h
  have hinv := hmax (cubicThetaFullInversion*u)
  rw [map_mul,← cubicThetaMobius_comp _ _ hp,cubicThetaFullInversion_height,hu] at hinv
  have hn := cubicTheta_nearest_normSq_bound q.1
  have hD : 0<Complex.normSq (q.1-(nearestEisenstein q.1:ℂ))+q.2^2 :=
    add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hq)
  have hmul := (div_le_iff₀ hD).mp hinv
  have hD1 : 1 ≤ Complex.normSq (q.1-(nearestEisenstein q.1:ℂ))+q.2^2 := by nlinarith
  refine ⟨u,?_⟩
  rw [hu]
  exact ⟨hq,hn,by nlinarith⟩

theorem cubicThetaFiniteSiegelCover :
    ∃ S : Finset SL(2,Eisenstein), ∀ p : ℂ × ℝ, 0<p.2 →
      ∃ δ ∈ S, ∃ k : cubicThetaPrincipalGroup,
        cubicThetaMobius (cubicThetaFullComplex (δ*k.val)) p∈cubicThetaSiegelSet := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteCongruenceCover
  refine ⟨S,?_⟩
  intro p hp
  obtain ⟨u,hu⟩ := cubicThetaSiegelSet_meets_orbit hp
  obtain ⟨δ,hδ,k,hk⟩ := hS u
  exact ⟨δ,hδ,k,hk ▸ hu⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCoreCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite compact-core and cusp cover of the principal quotient. All
charts are actual hyperbolic transformations of the single Siegel set. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCompactCoreCuspCover :
    ∃ S : Finset SL(2,Eisenstein), ∀ V : ℝ, ∀ p : ℂ × ℝ, 0<p.2 →
      ∃ k : cubicThetaPrincipalGroup,
        cubicThetaMobius (cubicThetaPrincipalComplex k) p∈
          cubicThetaCompactCore S V ∪ cubicThetaCuspCharts S V := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro V p hp
  obtain ⟨δ,hδ,k,hk⟩ := hS p hp
  let q := cubicThetaMobius (cubicThetaFullComplex (δ*k.val)) p
  have hq : q∈cubicThetaSiegelSet := hk
  have he : cubicThetaMobius (cubicThetaFullComplex δ⁻¹) q=
      cubicThetaMobius (cubicThetaPrincipalComplex k) p := by
    dsimp [q]
    rw [cubicThetaMobius_comp _ _ hp,← map_mul]
    simp only [inv_mul_cancel_left]
    rfl
  refine ⟨k,?_⟩
  by_cases hV : q.2 ≤ V
  · left
    apply mem_iUnion_of_mem δ
    apply mem_iUnion_of_mem hδ
    exact ⟨q,cubicThetaSiegelSet_mem_core hq hV,he⟩
  · right
    apply mem_iUnion_of_mem δ
    apply mem_iUnion_of_mem hδ
    exact ⟨q,⟨hq,lt_of_not_ge hV⟩,he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual topological quotient by the principal level-three group.
Proper discontinuity supplies Hausdorffness; the open quotient map
preserves local compactness. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaQuotientMap_open : IsOpenQuotientMap cubicThetaQuotientMap :=
  MulAction.isOpenQuotientMap_quotientMk

instance cubicThetaQuotient_t2 : T2Space CubicThetaQuotient := inferInstance

instance cubicThetaQuotient_locallyCompact : LocallyCompactSpace CubicThetaQuotient :=
  cubicThetaQuotientMap_open.locallyCompactSpace

instance cubicThetaQuotient_secondCountable : SecondCountableTopology CubicThetaQuotient :=
  Topology.IsQuotientMap.secondCountableTopology cubicThetaQuotientMap_open.isQuotientMap
    cubicThetaQuotientMap_open.isOpenMap

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientCharts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete local coordinate charts for the principal quotient, obtained
from the proved covering map and the open positive-height half-space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

instance cubicThetaQuotient_chartedSpace : ChartedSpace (ℂ × ℝ) CubicThetaQuotient where
  atlas := Set.range cubicThetaQuotientChart
  chartAt := cubicThetaQuotientChart
  mem_chart_source := cubicThetaQuotientChart_source
  chart_mem_atlas q := ⟨q,rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFundamentalDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual measurable fundamental domain for the free principal
arithmetic action. It is the fixed-point set of the proved Borel section,
not a postulated domain or a boundary regularity assumption. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelSection_measurable : Measurable cubicThetaBorelSection :=
  (Classical.choose_spec cubicTheta_measurable_section_exists).1

lemma cubicThetaBorelSection_rightInverse :
    Function.RightInverse cubicThetaBorelSection cubicThetaQuotientMap :=
  (Classical.choose_spec cubicTheta_measurable_section_exists).2

lemma cubicThetaFundamentalDomain_measurable : MeasurableSet cubicThetaFundamentalDomain :=
  measurableSet_eq_fun
    (cubicThetaBorelSection_measurable.comp cubicThetaQuotientMap_open.continuous.measurable)
    measurable_id

lemma cubicThetaFundamentalDomain_unique (p : CubicThetaPoint) :
    ∃! g : cubicThetaPrincipalGroup, g • p∈cubicThetaFundamentalDomain := by
  have he := cubicThetaBorelSection_rightInverse (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  refine ⟨g,?_,?_⟩
  · change cubicThetaBorelSection (cubicThetaQuotientMap (g • p))=g • p
    rw [cubicThetaQuotient_covering.map_smul]
    exact hg.symm
  · intro h hh
    change cubicThetaBorelSection (cubicThetaQuotientMap (h • p))=h • p at hh
    rw [cubicThetaQuotient_covering.map_smul] at hh
    have hp : h • p=g • p := hh.symm.trans hg.symm
    have hf : (g⁻¹*h) • p=p := by rw [mul_smul,hp,inv_smul_smul]
    exact (inv_mul_eq_one.mp (cubicThetaPrincipal_fixed_eq_one _ _ hf)).symm

lemma cubicThetaFundamentalDomain_isFundamentalDomain (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain cubicThetaPrincipalGroup cubicThetaFundamentalDomain μ :=
  IsFundamentalDomain.mk' cubicThetaFundamentalDomain_measurable.nullMeasurableSet
    cubicThetaFundamentalDomain_unique

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFundamentalExtension
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable injective quotient chart can be included in a genuine
fundamental domain. This supplies the local quotient-volume formula. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFundamentalDomain_injOn :
    InjOn cubicThetaQuotientMap cubicThetaFundamentalDomain := by
  intro p hp q hq he
  exact hp.symm.trans ((congrArg cubicThetaBorelSection he).trans hq)

def cubicThetaFundamentalExtension (S : Set CubicThetaPoint) : Set CubicThetaPoint :=
  S ∪ (cubicThetaFundamentalDomain \ cubicThetaQuotientMap ⁻¹' (cubicThetaQuotientMap '' S))

lemma cubicThetaFundamentalExtension_measurable {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hQ : MeasurableSet (cubicThetaQuotientMap '' S)) :
    MeasurableSet (cubicThetaFundamentalExtension S) :=
  hS.union (cubicThetaFundamentalDomain_measurable.diff
    (hQ.preimage cubicThetaQuotientMap_open.continuous.measurable))

lemma cubicThetaFundamentalExtension_injOn {S : Set CubicThetaPoint}
    (hS : InjOn cubicThetaQuotientMap S) :
    InjOn cubicThetaQuotientMap (cubicThetaFundamentalExtension S) := by
  intro p hp q hq he
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact hS hp hq he
    · exact False.elim (hq.2 ⟨p,hp,he⟩)
  · rcases hq with hq | hq
    · exact False.elim (hp.2 ⟨q,hq,he.symm⟩)
    · exact cubicThetaFundamentalDomain_injOn hp.1 hq.1 he

lemma cubicThetaFundamentalExtension_covers (S : Set CubicThetaPoint) (p : CubicThetaPoint) :
    ∃ g : cubicThetaPrincipalGroup, g • p∈cubicThetaFundamentalExtension S := by
  by_cases hp : cubicThetaQuotientMap p∈cubicThetaQuotientMap '' S
  · obtain ⟨q,hq,he⟩ := hp
    obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
    refine ⟨g,Or.inl ?_⟩
    change g • p=q at hg
    rwa [hg]
  · obtain ⟨g,hg,_⟩ := cubicThetaFundamentalDomain_unique p
    refine ⟨g,Or.inr ⟨hg,?_⟩⟩
    simpa only [mem_preimage,cubicThetaQuotient_covering.map_smul] using hp

lemma cubicThetaFundamentalExtension_isFundamentalDomain {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hQ : MeasurableSet (cubicThetaQuotientMap '' S))
    (hi : InjOn cubicThetaQuotientMap S) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain cubicThetaPrincipalGroup (cubicThetaFundamentalExtension S) μ := by
  apply IsFundamentalDomain.mk' (cubicThetaFundamentalExtension_measurable hS hQ).nullMeasurableSet
  intro p
  obtain ⟨g,hg⟩ := cubicThetaFundamentalExtension_covers S p
  refine ⟨g,hg,fun h hh => ?_⟩
  have he : cubicThetaQuotientMap (h • p)=cubicThetaQuotientMap (g • p) := by
    rw [cubicThetaQuotient_covering.map_smul,cubicThetaQuotient_covering.map_smul]
  have hp := cubicThetaFundamentalExtension_injOn hi hh hg he
  have hf : (g⁻¹*h) • p=p := by rw [mul_smul,hp,inv_smul_smul]
  exact (inv_mul_eq_one.mp (cubicThetaPrincipal_fixed_eq_one _ _ hf)).symm

lemma cubicThetaFundamentalExtension_inter (S : Set CubicThetaPoint) :
    cubicThetaQuotientMap ⁻¹' (cubicThetaQuotientMap '' S) ∩ cubicThetaFundamentalExtension S=S := by
  ext p
  constructor
  · rintro ⟨hp,hS | hD⟩
    · exact hS
    · exact False.elim (hD.2 hp)
  · intro hp
    exact ⟨⟨p,hp,rfl⟩,Or.inl hp⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual invariant hyperbolic measure on positive-height points.
Its density is v^-3, and arithmetic invariance follows from the proved
Jacobian, not from an assumed invariant measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal
namespace CubicFirstMoment

lemma cubicThetaPointMeasure_image (g : SL(2,Eisenstein)) {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    cubicThetaPointMeasure ((fun p => g • p) '' S)=cubicThetaPointMeasure S := by
  have hI : MeasurableSet ((fun p : CubicThetaPoint => g • p) '' S) :=
    (Homeomorph.smul g).measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaPointMeasure_apply hI,cubicThetaPointMeasure_apply hS]
  have he : cubicThetaPointCoordinates '' ((fun p : CubicThetaPoint => g • p) '' S)=
      cubicThetaMobius (cubicThetaFullComplex g) '' (cubicThetaPointCoordinates '' S) := by
    rw [image_image,image_image]
    rfl
  rw [he]
  apply cubicThetaHyperbolicMeasure_image _
    (cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS)
  rintro p ⟨q,_,rfl⟩
  exact q.property

instance cubicThetaPointMeasure_invariant :
    SMulInvariantMeasure SL(2,Eisenstein) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g S hS := by
    have he : (fun p : CubicThetaPoint => g • p) ⁻¹' S=(fun p => g⁻¹ • p) '' S := by
      ext p
      constructor
      · intro hp
        exact ⟨g • p,hp,inv_smul_smul g p⟩
      · rintro ⟨q,hq,rfl⟩
        change g • (g⁻¹ • q)∈S
        rwa [smul_inv_smul]
    rw [he]
    exact cubicThetaPointMeasure_image g⁻¹ hS

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quotient Borel structure and intrinsic hyperbolic measure.
The measure is independent of the measurable fundamental domain. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

instance cubicThetaPrincipalPointMeasure_invariant :
    SMulInvariantMeasure cubicThetaPrincipalGroup CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g:cubicThetaPrincipalGroup).val hS

lemma cubicThetaQuotientMeasure_apply {S : Set CubicThetaQuotient} (hS : MeasurableSet S) :
    cubicThetaQuotientMeasure S=
      cubicThetaPointMeasure (cubicThetaQuotientMap ⁻¹' S ∩ cubicThetaFundamentalDomain) := by
  rw [cubicThetaQuotientMeasure,Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hS,
    Measure.restrict_apply (hS.preimage cubicThetaQuotientMap_open.continuous.measurable)]

lemma cubicThetaQuotientMeasure_independent {D : Set CubicThetaPoint}
    (hD : IsFundamentalDomain cubicThetaPrincipalGroup D cubicThetaPointMeasure) :
    cubicThetaQuotientMeasure=(cubicThetaPointMeasure.restrict D).map cubicThetaQuotientMap := by
  ext S hS
  rw [cubicThetaQuotientMeasure_apply hS,
    Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hS,
    Measure.restrict_apply (hS.preimage cubicThetaQuotientMap_open.continuous.measurable)]
  apply (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).measure_set_eq hD
    (hS.preimage cubicThetaQuotientMap_open.continuous.measurable)
  intro g
  ext p
  simp only [mem_preimage,cubicThetaQuotient_covering.map_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalQuotientMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an injective quotient chart, hyperbolic measure downstairs equals
hyperbolic measure upstairs. This follows by replacing the fundamental
domain with the proved measurable extension of that chart. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaQuotientMeasure_local_image {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hQ : MeasurableSet (cubicThetaQuotientMap '' S))
    (hi : InjOn cubicThetaQuotientMap S) :
    cubicThetaQuotientMeasure (cubicThetaQuotientMap '' S)=cubicThetaPointMeasure S := by
  rw [cubicThetaQuotientMeasure_independent
    (cubicThetaFundamentalExtension_isFundamentalDomain hS hQ hi cubicThetaPointMeasure),
    Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hQ,
    Measure.restrict_apply (hQ.preimage cubicThetaQuotientMap_open.continuous.measurable),
    cubicThetaFundamentalExtension_inter]

lemma cubicThetaQuotientChart_measurable_image
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    MeasurableSet (cubicThetaQuotientMap '' S) := by
  have ht := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (hS.preimage (measurable_subtype_coe : Measurable (Subtype.val : e.source → CubicThetaPoint)))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  constructor
  · rintro ⟨p,hp,hpq⟩
    exact ⟨⟨p,hSe hp⟩,hp,(congrFun he p).trans hpq⟩
  · rintro ⟨p,hp,hpq⟩
    exact ⟨p.val,hp,(congrFun he p.val).symm.trans hpq⟩

lemma cubicThetaQuotientMeasure_chart
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    cubicThetaQuotientMeasure (cubicThetaQuotientMap '' S)=cubicThetaPointMeasure S := by
  apply cubicThetaQuotientMeasure_local_image hS
    (cubicThetaQuotientChart_measurable_image e he hS hSe)
  intro p hp q hq hpq
  apply e.injOn (hSe hp) (hSe hq)
  simpa only [he] using hpq

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientLocalFiniteness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quotient's actual hyperbolic measure is locally finite. Small
compact neighborhoods are lifted through the proved covering charts. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

instance cubicThetaQuotientMeasure_locallyFinite : IsLocallyFiniteMeasure cubicThetaQuotientMeasure where
  finiteAtNhds q := by
    let p := cubicThetaQuotientLift q
    let e := cubicThetaCoveringChart p
    obtain ⟨K,hK,hpK,hKe⟩ := exists_compact_subset e.open_source (cubicThetaCoveringChart_source p)
    refine ⟨cubicThetaQuotientMap '' K,?_,?_⟩
    · have h := cubicThetaQuotientMap_open.isOpenMap.image_mem_nhds
        (mem_interior_iff_mem_nhds.mp hpK)
      rwa [cubicThetaQuotientLift_map] at h
    · rw [cubicThetaQuotientMeasure_chart e (cubicThetaCoveringChart_coe p)
        hK.isClosed.measurableSet hKe]
      exact cubicThetaPointMeasure_compact hK

instance cubicThetaQuotientMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts cubicThetaQuotientMeasure :=
  inferInstance

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved arithmetic core/cusp cover descends to the actual quotient;
the core is compact in its Hausdorff quotient topology. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaQuotientCore (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    Set CubicThetaQuotient :=
  cubicThetaQuotientMap '' {p : CubicThetaPoint | p.val∈cubicThetaCompactCore S V}

def cubicThetaQuotientCusps (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    Set CubicThetaQuotient :=
  cubicThetaQuotientMap '' {p : CubicThetaPoint | p.val∈cubicThetaCuspCharts S V}

lemma cubicThetaQuotientCore_compact (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    IsCompact (cubicThetaQuotientCore S V) := by
  have he : {p : CubicThetaPoint | p.val∈cubicThetaCompactCore S V}=
      cubicThetaPointInclusion.symm '' cubicThetaCompactCore S V := by
    ext p
    constructor
    · intro hp
      exact ⟨p.val,hp,cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)⟩
    · rintro ⟨q,hq,hqp⟩
      have ht : q∈cubicThetaPointInclusion.target := by
        rw [cubicThetaPointInclusion_target]
        exact cubicThetaCompactCore_positive S V hq
      have hv := cubicThetaPointInclusion.right_inv ht
      rw [hqp] at hv
      change p.val=q at hv
      change p.val∈cubicThetaCompactCore S V
      rw [hv]
      exact hq
  apply IsCompact.image _ cubicThetaQuotientMap_open.continuous
  rw [he]
  exact (cubicThetaCompactCore_compact S V).image_of_continuousOn
    (cubicThetaPointInclusion.symm.continuousOn.mono (by
      intro p hp
      rw [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target]
      exact cubicThetaCompactCore_positive S V hp))

lemma cubicThetaQuotientCore_cusps_cover :
    ∃ S : Finset SL(2,Eisenstein), ∀ V : ℝ,
      cubicThetaQuotientCore S V ∪ cubicThetaQuotientCusps S V=Set.univ := by
  obtain ⟨S,hS⟩ := cubicThetaCompactCoreCuspCover
  refine ⟨S,?_⟩
  intro V
  apply Set.eq_univ_of_forall
  intro q
  let p := cubicThetaQuotientLift q
  obtain ⟨k,hk⟩ := hS V p.val p.property
  have he : cubicThetaQuotientMap (k • p)=q :=
    cubicThetaQuotient_covering.map_smul k |>.trans (cubicThetaQuotientLift_map q)
  rcases hk with hk | hk
  · left
    exact ⟨k • p,hk,he⟩
  · right
    exact ⟨k • p,hk,he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalLifts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two local lifts of the actual arithmetic quotient differ by one fixed
deck transformation near any point. This is the local transition law for
both the geometric charts and the cubic multiplier. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaLocalLifts_eq {X : Type*} [TopologicalSpace X] {x : X}
    {F G : X → CubicThetaPoint} (hF : ContinuousAt F x) (hG : ContinuousAt G x)
    (hx : F x=G x)
    (h : ∀ᶠ y in 𝓝 x, cubicThetaQuotientMap (F y)=cubicThetaQuotientMap (G y)) :
    F =ᶠ[𝓝 x] G := by
  obtain ⟨U,hU,hxU,hUi⟩ := cubicThetaQuotient_localHomeomorph.isLocallyInjective (F x)
  have hFU : ∀ᶠ y in 𝓝 x, F y∈U := hF.preimage_mem_nhds (hU.mem_nhds hxU)
  have hGU : ∀ᶠ y in 𝓝 x, G y∈U := hG.preimage_mem_nhds (hU.mem_nhds (hx ▸ hxU))
  filter_upwards [hFU,hGU,h] with y hyF hyG hy
  exact hUi hyF hyG hy

lemma cubicThetaLocalLifts_deck {X : Type*} [TopologicalSpace X] {x : X}
    {F G : X → CubicThetaPoint} (hF : ContinuousAt F x) (hG : ContinuousAt G x)
    (h : ∀ᶠ y in 𝓝 x, cubicThetaQuotientMap (F y)=cubicThetaQuotientMap (G y)) :
    ∃ g : cubicThetaPrincipalGroup, F =ᶠ[𝓝 x] fun y => g • G y := by
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp h.self_of_nhds
  refine ⟨g,cubicThetaLocalLifts_eq hF ((continuous_const_smul g).continuousAt.comp hG) hg.symm ?_⟩
  filter_upwards [h] with y hy
  exact hy.trans (cubicThetaQuotient_covering.map_smul g).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaChartTransition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On every overlap, quotient coordinates differ locally by the actual
smooth Mobius action of one element of the principal group. -/
noncomputable section
open Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaChartTransition
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (y : ℂ × ℝ) : ℂ × ℝ :=
  (f.symm (e (cubicThetaPointInclusion.symm y))).val

def cubicThetaChartTransitionSource
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient) : Set (ℂ × ℝ) :=
  {y | y∈cubicThetaPointInclusion.target ∧
    cubicThetaPointInclusion.symm y∈e.source ∧
    e (cubicThetaPointInclusion.symm y)∈f.target}

lemma cubicThetaChartTransition_deck
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hf : (f : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {x : ℂ × ℝ} (hx : x∈cubicThetaChartTransitionSource e f) :
    ∃ g : cubicThetaPrincipalGroup, cubicThetaChartTransition e f =ᶠ[𝓝 x]
      cubicThetaMobius (cubicThetaPrincipalComplex g) := by
  let F : ℂ × ℝ → CubicThetaPoint := cubicThetaPointInclusion.symm
  let G : ℂ × ℝ → CubicThetaPoint := fun y => f.symm (e (F y))
  have hF : ContinuousAt F x := cubicThetaPointInclusion.symm.continuousAt hx.1
  have hE : ContinuousAt (fun y => e (F y)) x := (e.continuousAt hx.2.1).comp hF
  have hG : ContinuousAt G x := (f.symm.continuousAt hx.2.2).comp
    (x:=x) (f:=fun y => e (F y)) hE
  have htarget : ∀ᶠ y in 𝓝 x, e (F y)∈f.target :=
    hE.preimage_mem_nhds (f.open_target.mem_nhds hx.2.2)
  have hq : ∀ᶠ y in 𝓝 x, cubicThetaQuotientMap (G y)=cubicThetaQuotientMap (F y) := by
    filter_upwards [htarget] with y hy
    change cubicThetaQuotientMap (f.symm (e (F y)))=cubicThetaQuotientMap (F y)
    calc
      _ = f (f.symm (e (F y))) := (congrFun hf _).symm
      _ = e (F y) := f.right_inv hy
      _ = cubicThetaQuotientMap (F y) := congrFun he _
  obtain ⟨g,hg⟩ := cubicThetaLocalLifts_deck hG hF hq
  refine ⟨g,?_⟩
  have hpositive : ∀ᶠ y in 𝓝 x, y∈cubicThetaPointInclusion.target :=
    cubicThetaPointInclusion.open_target.mem_nhds hx.1
  filter_upwards [hg,hpositive] with y hy hp
  have hv : (F y).val=y := cubicThetaPointInclusion.right_inv hp
  have hv' := congrArg Subtype.val hy
  change cubicThetaChartTransition e f y=
    cubicThetaMobius (cubicThetaPrincipalComplex g) (F y).val at hv'
  rwa [hv] at hv'

lemma cubicThetaChartTransition_contDiffAt
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hf : (f : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {x : ℂ × ℝ} (hx : x∈cubicThetaChartTransitionSource e f) :
    ContDiffAt ℝ ∞ (cubicThetaChartTransition e f) x := by
  obtain ⟨g,hg⟩ := cubicThetaChartTransition_deck e f he hf hx
  have hp : 0<x.2 := by
    have h := hx.1
    rwa [cubicThetaPointInclusion_target] at h
  exact (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g) hp).congr_of_eventuallyEq hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientManifold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal quotient is a smooth real three-dimensional
manifold. Chart changes are the already proved smooth arithmetic actions. -/
noncomputable section
open scoped ContDiff Manifold
namespace CubicFirstMoment

lemma cubicThetaQuotientChart_transition_contDiff (p q : CubicThetaQuotient) :
    ContDiffOn ℝ ∞ ((cubicThetaQuotientChart p).symm.trans (cubicThetaQuotientChart q))
      ((cubicThetaQuotientChart p).symm.trans (cubicThetaQuotientChart q)).source := by
  intro x hx
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift p)
  let f := cubicThetaCoveringChart (cubicThetaQuotientLift q)
  have hsource : x∈cubicThetaChartTransitionSource e f := by
    change (x∈cubicThetaPointInclusion.target ∧ cubicThetaPointInclusion.symm x∈e.source) ∧
      (e (cubicThetaPointInclusion.symm x)∈f.target ∧
      f.symm (e (cubicThetaPointInclusion.symm x))∈cubicThetaPointInclusion.source) at hx
    exact ⟨hx.1.1,hx.1.2,hx.2.1⟩
  have h := cubicThetaChartTransition_contDiffAt e f
    (cubicThetaCoveringChart_coe _) (cubicThetaCoveringChart_coe _) hsource
  exact h.contDiffWithinAt

instance cubicThetaQuotient_isManifold :
    IsManifold (𝓘(ℝ,ℂ × ℝ)) ∞ CubicThetaQuotient := by
  apply isManifold_of_contDiffOn
  rintro e f ⟨p,rfl⟩ ⟨q,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.comp_id,
    Function.id_comp,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    cubicThetaQuotientChart_transition_contDiff p q

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreBumps
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite family of genuine compactly supported smooth chart cutoffs
controls the actual arithmetic core. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups Manifold ContDiff BigOperators
namespace CubicFirstMoment

def cubicThetaCoreBump (q : CubicThetaQuotient) :
    SmoothBumpFunction (𝓘(ℝ,ℂ × ℝ)) q := Classical.choice inferInstance

lemma cubicThetaCoreBump_finite_cover (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      ∃ c∈A, cubicThetaCoreBump c q=1 := by
  classical
  obtain ⟨A,_,hA⟩ := (cubicThetaQuotientCore_compact S V).elim_nhds_subcover
    (fun c => interior {q | cubicThetaCoreBump c q=1}) (fun c _ => by
      have h : {q | cubicThetaCoreBump c q=1}∈𝓝 c := (cubicThetaCoreBump c).eventuallyEq_one
      exact interior_mem_nhds.mpr h)
  refine ⟨A,fun q hq => ?_⟩
  obtain ⟨c,hc,hqc⟩ := mem_iUnion₂.mp (hA hq)
  have he : q∈{q | cubicThetaCoreBump c q=1} := interior_subset hqc
  exact ⟨c,hc,he⟩

lemma cubicThetaCoreBump_sum_sq (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      1 ≤ ∑ c∈A, (cubicThetaCoreBump c q)^2 := by
  obtain ⟨A,hA⟩ := cubicThetaCoreBump_finite_cover S V
  refine ⟨A,fun q hq => ?_⟩
  obtain ⟨c,hc,hqc⟩ := hA q hq
  have h := Finset.single_le_sum (fun d (_ : d∈A) => sq_nonneg (cubicThetaCoreBump d q)) hc
  simpa only [hqc,one_pow] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAutomorphicSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous sections with the actual cubic multiplier. Their norm
descends to the arithmetic quotient, and quotient cutoffs localize them. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSectionNorm_apply (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionNorm F (cubicThetaQuotientMap p)=‖F.val p‖ := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaSectionNorm
  rw [← hg,F.property g p,norm_mul,cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaSectionNorm_continuous (F : CubicThetaSection) :
    Continuous (cubicThetaSectionNorm F) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaSectionNorm F ∘ cubicThetaQuotientMap=fun p => ‖F.val p‖ :=
    funext (cubicThetaSectionNorm_apply F)
  rw [he]
  exact F.val.continuous.norm

def cubicThetaSectionCutoff (ψ : C(CubicThetaQuotient,ℂ)) (F : CubicThetaSection) :
    CubicThetaSection :=
  ⟨⟨fun p => ψ (cubicThetaQuotientMap p)*F.val p,
    (ψ.continuous.comp cubicThetaQuotientMap_open.continuous).mul F.val.continuous⟩,by
      intro g p
      change ψ (cubicThetaQuotientMap (g • p))*F.val (g • p)=
        cubicThetaKubotaValue g*(ψ (cubicThetaQuotientMap p)*F.val p)
      rw [cubicThetaQuotient_covering.map_smul g,F.property g p]
      ring⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreProfiles
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact core cutoffs become actual smooth Euclidean chart
profiles, with support entirely at positive height. -/
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
namespace CubicFirstMoment

def cubicThetaCoreProfile (c : CubicThetaQuotient) (y : ℂ × ℝ) : ℂ :=
  ((cubicThetaCoreBump c).toContDiffBump y:ℝ)

lemma cubicThetaCoreProfile_contDiff (c : CubicThetaQuotient) :
    ContDiff ℝ ∞ (cubicThetaCoreProfile c) :=
  Complex.ofRealCLM.contDiff.comp (cubicThetaCoreBump c).toContDiffBump.contDiff

lemma cubicThetaCoreProfile_compact (c : CubicThetaQuotient) :
    HasCompactSupport (cubicThetaCoreProfile c) :=
  (cubicThetaCoreBump c).toContDiffBump.hasCompactSupport.comp_left
    (g:=fun r : ℝ => (r:ℂ)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

lemma cubicThetaQuotientChart_target_positive (c : CubicThetaQuotient) :
    (cubicThetaQuotientChart c).target ⊆ {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  change y∈cubicThetaPointInclusion.target ∧ _ at hy
  rw [cubicThetaPointInclusion_target] at hy
  exact hy.1

lemma cubicThetaCoreProfile_support_target (c : CubicThetaQuotient) :
    tsupport (cubicThetaCoreProfile c) ⊆ (cubicThetaQuotientChart c).target := by
  have hs : tsupport (cubicThetaCoreProfile c) ⊆ tsupport (cubicThetaCoreBump c).toContDiffBump := by
    apply closure_mono
    intro y hy hz
    apply hy
    change ((cubicThetaCoreBump c).toContDiffBump y:ℂ)=0
    rw [hz]
    rfl
  intro y hy
  have hb := hs hy
  rw [ContDiffBump.tsupport_eq] at hb
  have ht := (cubicThetaCoreBump c).closedBall_subset ⟨hb,⟨y,rfl⟩⟩
  have ht' : y∈(cubicThetaQuotientChart c).target := by
    simp only [extChartAt_target,modelWithCornersSelf_coe_symm,Set.preimage_id_eq,
      modelWithCornersSelf_coe,Set.range_id,Set.inter_univ,id_eq] at ht
    change y∈(cubicThetaQuotientChart c).target at ht
    exact ht
  exact ht'

lemma cubicThetaCoreProfile_support_positive (c : CubicThetaQuotient) :
    tsupport (cubicThetaCoreProfile c) ⊆ {y : ℂ × ℝ | 0<y.2} :=
  (cubicThetaCoreProfile_support_target c).trans (cubicThetaQuotientChart_target_positive c)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported seeds produce actual continuous automorphic
sections by a locally finite sum with the cubic multiplier. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported
namespace CubicFirstMoment

lemma cubicTheta_compact_translates_locallyFinite {K : Set CubicThetaPoint} (hK : IsCompact K) :
    LocallyFinite (fun g : cubicThetaPrincipalGroup => (fun p => g • p) ⁻¹' K) := by
  intro p
  obtain ⟨L,hL,hLp⟩ := exists_compact_mem_nhds p
  refine ⟨L,hLp,?_⟩
  apply (finite_disjoint_inter_image (Γ:=cubicThetaPrincipalGroup) hL hK).subset
  rintro g ⟨q,hq,hqL⟩
  exact ⟨g • q,⟨q,hqL,rfl⟩,hq⟩

lemma cubicThetaPoincareTerm_locallyFinite (ψ : C_c(CubicThetaPoint,ℂ)) :
    LocallyFinite (fun g : cubicThetaPrincipalGroup => Function.support (cubicThetaPoincareTerm ψ g)) := by
  apply (cubicTheta_compact_translates_locallyFinite ψ.hasCompactSupport).subset
  intro g p hp
  apply subset_tsupport ψ
  intro hz
  exact hp (by simp [cubicThetaPoincareTerm,hz])

lemma cubicThetaPoincareTerm_continuous (ψ : C_c(CubicThetaPoint,ℂ))
    (g : cubicThetaPrincipalGroup) : Continuous (cubicThetaPoincareTerm ψ g) :=
  continuous_const.mul (ψ.continuous.comp (continuous_const_smul g))

def cubicThetaPoincareSection (ψ : C_c(CubicThetaPoint,ℂ)) : CubicThetaSection :=
  ⟨⟨fun p => ∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p,
    continuous_finsum (cubicThetaPoincareTerm_continuous ψ) (cubicThetaPoincareTerm_locallyFinite ψ)⟩,by
    intro h p
    change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g (h • p))=
      cubicThetaKubotaValue h*(∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)
    simp_rw [cubicThetaPoincareTerm_translate]
    change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaKubotaValue h • cubicThetaPoincareTerm ψ (g*h) p)=_
    rw [← smul_finsum]
    exact congrArg (fun z : ℂ => cubicThetaKubotaValue h • z)
      (finsum_comp_equiv (f:=fun g => cubicThetaPoincareTerm ψ g p) (Equiv.mulRight h))⟩

lemma cubicThetaPoincareSection_compact (ψ : C_c(CubicThetaPoint,ℂ)) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaPoincareSection ψ)) := by
  have hc := ψ.hasCompactSupport.image cubicThetaQuotientMap_open.continuous
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro q hq
  let p := cubicThetaQuotientLift q
  have hn : (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)≠0 := by
    intro hz
    apply hq
    change ‖∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p‖=0
    simp [hz]
  have hex : ∃ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p≠0 := by
    by_contra! hn'
    exact hn (by simp [hn'])
  obtain ⟨g,hg⟩ := hex
  refine ⟨g • p,?_,?_⟩
  · apply subset_tsupport ψ
    intro hz
    exact hg (by simp [cubicThetaPoincareTerm,hz])
  · exact (cubicThetaQuotient_covering.map_smul g).trans (cubicThetaQuotientLift_map q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of periodized compact seeds is proved locally by replacing
its locally finite arithmetic sum with an actual finite sum. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPoincareSection_contDiffOn (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ ∞
      (fun y => (cubicThetaPoincareSection ψ).val (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  have hy' : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  obtain ⟨s,hs⟩ := cubicTheta_locallyFinite_finsum _ (cubicThetaPoincareTerm_locallyFinite ψ)
    (cubicThetaPointInclusion.symm y)
  have he := hs.comp_tendsto (cubicThetaPointInclusion.symm.continuousAt hy')
  have hd : ContDiffAt ℝ ∞
      (fun x => ∑ g∈s, cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y :=
    ContDiffAt.sum (fun g _ => cubicThetaPoincareTerm_contDiffAt ψ hψ g hy)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaChartSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact Euclidean chart profile gives a genuine compact smooth
section. On its covering sheet the periodization is exactly the seed. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff
namespace CubicFirstMoment

def cubicThetaCoreSeed (c : CubicThetaQuotient) : C_c(CubicThetaPoint,ℂ) :=
  ⟨⟨fun p => cubicThetaCoreProfile c p.val,
    (cubicThetaCoreProfile_contDiff c).continuous.comp continuous_subtype_val⟩,
    cubicThetaPositiveSeed_compact (cubicThetaCoreProfile_compact c)
      (cubicThetaCoreProfile_support_positive c)⟩

lemma cubicThetaCoreSeed_contDiffOn (c : CubicThetaQuotient) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaCoreSeed c (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2} := by
  apply (cubicThetaCoreProfile_contDiff c).contDiffOn.congr
  intro y hy
  change cubicThetaCoreProfile c (cubicThetaPointInclusion.symm y).val=cubicThetaCoreProfile c y
  congr 1
  exact cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target])

lemma cubicThetaPoincareSection_on_sheet (ψ : C_c(CubicThetaPoint,ℂ))
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hs : Function.support ψ ⊆ e.source) {p : CubicThetaPoint} (hp : p∈e.source) :
    (cubicThetaPoincareSection ψ).val p=ψ p := by
  have hz : ∀ g : cubicThetaPrincipalGroup, g≠1 → cubicThetaPoincareTerm ψ g p=0 := by
    intro g hg
    have hgp : g • p∉Function.support ψ := by
      intro h
      have heq : e (g • p)=e p := by
        rw [he,cubicThetaQuotient_covering.map_smul]
      have hf : g • p=p := e.injOn (hs h) hp heq
      exact hg (cubicThetaPrincipal_fixed_eq_one g p hf)
    have hz : ψ (g • p)=0 := by simpa only [Function.mem_support,not_not] using hgp
    simp only [cubicThetaPoincareTerm,hz,mul_zero]
  change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)=ψ p
  rw [finsum_eq_single _ 1 hz]
  simp [cubicThetaPoincareTerm,cubicThetaKubotaValue]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual automorphic sections as global L2 vectors. A Borel section
chooses representatives, while the norm is the continuous intrinsic norm
on the quotient, so compact smooth sections are square integrable. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaSectionRepresentative (F : CubicThetaSection) (q : CubicThetaQuotient) : ℂ :=
  F.val (cubicThetaBorelSection q)

lemma cubicThetaSectionRepresentative_measurable (F : CubicThetaSection) :
    Measurable (cubicThetaSectionRepresentative F) :=
  F.val.continuous.measurable.comp cubicThetaBorelSection_measurable

lemma cubicThetaSectionRepresentative_norm (F : CubicThetaSection) (q : CubicThetaQuotient) :
    ‖cubicThetaSectionRepresentative F q‖=cubicThetaSectionNorm F q := by
  have h := cubicThetaSectionNorm_apply F (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse q] at h
  exact h.symm

lemma cubicThetaSectionRepresentative_memLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure := by
  have hnorm : MemLp (cubicThetaSectionNorm F) 2 cubicThetaQuotientMeasure :=
    (cubicThetaSectionNorm_continuous F).memLp_of_hasCompactSupport F.property.2
  apply (memLp_norm_iff (cubicThetaSectionRepresentative_measurable F).aestronglyMeasurable).mp
  simpa only [cubicThetaSectionRepresentative_norm] using hnorm

def cubicThetaGlobalMass : cubicThetaSmoothTests →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun F := (cubicThetaSectionRepresentative_memLp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(cubicThetaSectionRepresentative_memLp (F+G)).coeFn_toLp,
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp,
      (cubicThetaSectionRepresentative_memLp G).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaSectionRepresentative_memLp F).toLp _)
        ((cubicThetaSectionRepresentative_memLp G).toLp _)] with q hFG hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hFG,hadd,hF,hG]
    rfl
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(cubicThetaSectionRepresentative_memLp (c • F)).coeFn_toLp,
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaSectionRepresentative_memLp F).toLp _)] with q hCF hF hsmul
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hsmul
    rw [hCF,hsmul,hF]
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionDifferential
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate the actual cubic automorphy law. Its unit multiplier
and the conformal tangent map imply invariance of hyperbolic energy. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

def cubicThetaSectionFunction (F : CubicThetaSection) (y : ℂ × ℝ) : ℂ :=
  F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaSectionFunction_apply (F : CubicThetaSection) {y : ℂ × ℝ}
    (hy : 0<y.2) : cubicThetaSectionFunction F y=F.val ⟨y,hy⟩ := by
  apply congrArg F.val
  apply Subtype.ext
  have hy' : y∈cubicThetaPointInclusion.target := by
    rwa [cubicThetaPointInclusion_target]
  have h := cubicThetaPointInclusion.right_inv hy'
  exact h

lemma cubicThetaSectionFunction_differentiable (F : cubicThetaSmoothTests)
    {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaSectionFunction F) y :=
  (F.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

def cubicThetaSectionDifferential (F : CubicThetaSection) (p : CubicThetaPoint) :
    CubicThetaTangent →L[ℝ] ℂ :=
  (fderiv ℝ (cubicThetaSectionFunction F) p.val).comp
    cubicThetaTangentCoordinates.toContinuousLinearMap

lemma cubicThetaSectionFunction_automorphy (F : CubicThetaSection)
    (g : cubicThetaPrincipalGroup) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaPrincipalComplex g) y)=
      cubicThetaKubotaValue g*cubicThetaSectionFunction F y := by
  unfold cubicThetaSectionFunction
  rw [cubicThetaPointInclusion_action g hy,F.property]

lemma cubicThetaSectionDifferential_automorphy (F : cubicThetaSmoothTests)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    (cubicThetaSectionDifferential F (g • p)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g) p.val)=
      cubicThetaKubotaValue g • cubicThetaSectionDifferential F p := by
  have hm := cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g) p.property
  have hM := (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g)
    p.property).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hF := cubicThetaSectionFunction_differentiable F p.property
  have hG := cubicThetaSectionFunction_differentiable F hm
  have he : (fun y => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaPrincipalComplex g) y)) =ᶠ[𝓝 p.val]
        (fun y => cubicThetaKubotaValue g*cubicThetaSectionFunction F y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with y hy
    exact cubicThetaSectionFunction_automorphy F g hy
  have hd := ((hG.hasFDerivAt.comp p.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    (hF.hasFDerivAt.const_mul (cubicThetaKubotaValue g))
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) hd
  have hgp : (g • p).val=cubicThetaMobius (cubicThetaPrincipalComplex g) p.val := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,hgp,
    ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hv

def cubicThetaSectionEnergy (F : CubicThetaSection) (p : CubicThetaPoint) : ℝ :=
  p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential F p)

lemma cubicThetaSectionEnergy_invariant (F : cubicThetaSmoothTests)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy F (g • p)=cubicThetaSectionEnergy F p := by
  have he := congrArg cubicThetaTangentEnergy (cubicThetaSectionDifferential_automorphy F g p)
  rw [cubicThetaTangentEnergy_derivative _ _ p.property,
    cubicThetaTangentEnergy_complex_smul,cubicThetaKubotaValue_norm,one_pow,one_mul] at he
  change (cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (g • p))=
    p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential F p)
  calc
    _ = p.val.2^2*(((cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2/p.val.2)^2*
        cubicThetaTangentEnergy (cubicThetaSectionDifferential F (g • p))) := by
      field_simp [p.property.ne']
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine differential energy descends to a continuous function
on the quotient. Compact smooth sections have compactly supported
gradient norm, hence square-integrable gradient. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionEnergy_continuous (F : cubicThetaSmoothTests) :
    Continuous (cubicThetaSectionEnergy F) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by simp)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  unfold cubicThetaSectionEnergy cubicThetaTangentEnergy cubicThetaSectionDifferential
  apply ((continuous_snd.comp continuous_subtype_val).pow 2).mul
  apply continuous_finsetSum
  intro i hi
  exact ((hd.clm_apply continuous_const).norm).pow 2

def cubicThetaQuotientEnergy (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaSectionEnergy F (cubicThetaQuotientLift q)

lemma cubicThetaQuotientEnergy_apply (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaQuotientEnergy F (cubicThetaQuotientMap p)=cubicThetaSectionEnergy F p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaQuotientEnergy
  rw [← hg,cubicThetaSectionEnergy_invariant]

lemma cubicThetaQuotientEnergy_continuous (F : cubicThetaSmoothTests) :
    Continuous (cubicThetaQuotientEnergy F) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaQuotientEnergy F ∘ cubicThetaQuotientMap=cubicThetaSectionEnergy F :=
    funext (cubicThetaQuotientEnergy_apply F)
  rw [he]
  exact cubicThetaSectionEnergy_continuous F

lemma cubicThetaSectionDifferential_eq_zero (F : CubicThetaSection) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉tsupport (cubicThetaSectionNorm F)) :
    cubicThetaSectionDifferential F p=0 := by
  have hzero := notMem_tsupport_iff_eventuallyEq.mp hp
  have htarget : p.val∈cubicThetaPointInclusion.target := by
    rw [cubicThetaPointInclusion_target]
    exact p.property
  have hinv : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  have hmap : ContinuousAt (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)) p.val :=
    cubicThetaQuotientMap_open.continuous.continuousAt.comp
      (cubicThetaPointInclusion.symm.continuousAt htarget)
  have hmap' : Tendsto (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
      (𝓝 p.val) (𝓝 (cubicThetaQuotientMap p)) := by
    have he := congrArg (fun r : CubicThetaPoint => 𝓝 (cubicThetaQuotientMap r)) hinv
    exact he ▸ hmap.tendsto
  have he : cubicThetaSectionFunction F =ᶠ[𝓝 p.val] (fun _ => (0:ℂ)) := by
    filter_upwards [hzero.comp_tendsto hmap'] with y hy
    change cubicThetaSectionNorm F (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=0 at hy
    rw [cubicThetaSectionNorm_apply] at hy
    exact norm_eq_zero.mp hy
  have hd : fderiv ℝ (cubicThetaSectionFunction F) p.val=0 := by
    rw [he.fderiv_eq]
    exact fderiv_const_apply (0:ℂ)
  ext u
  simp only [cubicThetaSectionDifferential,hd,ContinuousLinearMap.zero_comp,zero_apply]

lemma cubicThetaQuotientEnergy_compact (F : cubicThetaSmoothTests) :
    HasCompactSupport (cubicThetaQuotientEnergy F) := by
  apply F.property.2.mono'
  intro q hq
  by_contra hn
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  apply hq
  simp only [cubicThetaQuotientEnergy,cubicThetaSectionEnergy,hd,
    cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,mul_zero]

def cubicThetaQuotientGradientNorm (F : cubicThetaSmoothTests) : CubicThetaQuotient → ℝ :=
  fun q => Real.sqrt (cubicThetaQuotientEnergy F q)

lemma cubicThetaQuotientGradientNorm_memLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaQuotientGradientNorm F) 2 cubicThetaQuotientMeasure :=
  (cubicThetaQuotientEnergy_continuous F).sqrt.memLp_of_hasCompactSupport
    ((cubicThetaQuotientEnergy_compact F).comp_left (g:=Real.sqrt) Real.sqrt_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalGradient
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual L2 gradient vector, obtained by evaluating the differential
in an orthonormal frame at the measurable representative. Its norm is
intrinsic even though its coordinates use that representative. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaSectionGradient (F : CubicThetaSection) (p : CubicThetaPoint) : CubicThetaGradient :=
  WithLp.toLp 2 (fun i => p.val.2 • cubicThetaSectionDifferential F p (cubicThetaTangentBasis i))

lemma cubicThetaSectionGradient_continuous (F : cubicThetaSmoothTests) :
    Continuous (cubicThetaSectionGradient F) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (F.property.1.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by simp)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaSectionGradient_norm_sq (F : CubicThetaSection) (p : CubicThetaPoint) :
    ‖cubicThetaSectionGradient F p‖^2=cubicThetaSectionEnergy F p := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cubicThetaSectionGradient,WithLp.ofLp_toLp,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs,cubicThetaSectionEnergy,cubicThetaTangentEnergy,Finset.mul_sum]

def cubicThetaGradientRepresentative (F : CubicThetaSection) (q : CubicThetaQuotient) :
    CubicThetaGradient := cubicThetaSectionGradient F (cubicThetaBorelSection q)

lemma cubicThetaGradientRepresentative_measurable (F : cubicThetaSmoothTests) :
    Measurable (cubicThetaGradientRepresentative F) :=
  (cubicThetaSectionGradient_continuous F).measurable.comp cubicThetaBorelSection_measurable

lemma cubicThetaGradientRepresentative_norm (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) :
    ‖cubicThetaGradientRepresentative F q‖=cubicThetaQuotientGradientNorm F q := by
  have he := cubicThetaQuotientEnergy_apply F (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse] at he
  unfold cubicThetaQuotientGradientNorm
  rw [he,← cubicThetaSectionGradient_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]
  rfl

lemma cubicThetaGradientRepresentative_memLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure := by
  apply (memLp_norm_iff (cubicThetaGradientRepresentative_measurable F).aestronglyMeasurable).mp
  simpa only [cubicThetaGradientRepresentative_norm] using cubicThetaQuotientGradientNorm_memLp F

lemma cubicThetaSectionFunction_add (F G : cubicThetaSmoothTests) :
    cubicThetaSectionFunction ((F+G : cubicThetaSmoothTests) : CubicThetaSection)=
      cubicThetaSectionFunction F+cubicThetaSectionFunction G := rfl

lemma cubicThetaSectionFunction_smul (c : ℂ) (F : cubicThetaSmoothTests) :
    cubicThetaSectionFunction ((c • F : cubicThetaSmoothTests) : CubicThetaSection)=
      c • cubicThetaSectionFunction F := rfl

lemma cubicThetaSectionGradient_add (F G : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionGradient ((F+G : cubicThetaSmoothTests) : CubicThetaSection) p=
      cubicThetaSectionGradient F p+cubicThetaSectionGradient G p := by
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,
    cubicThetaSectionFunction_add,fderiv_add (cubicThetaSectionFunction_differentiable F p.property)
      (cubicThetaSectionFunction_differentiable G p.property),
    ContinuousLinearMap.comp_apply,add_apply,smul_add]
  rfl

lemma cubicThetaSectionGradient_smul (c : ℂ) (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionGradient ((c • F : cubicThetaSmoothTests) : CubicThetaSection) p=
      c • cubicThetaSectionGradient F p := by
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,cubicThetaSectionFunction_smul,
    fderiv_const_smul (cubicThetaSectionFunction_differentiable F p.property) c,
    ContinuousLinearMap.comp_apply,smul_apply]
  exact smul_comm p.val.2 c (cubicThetaSectionDifferential F p (cubicThetaTangentBasis i))

def cubicThetaGlobalGradient : cubicThetaSmoothTests →ₗ[ℂ] CubicThetaGradientL2 where
  toFun F := (cubicThetaGradientRepresentative_memLp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(cubicThetaGradientRepresentative_memLp (F+G)).coeFn_toLp,
      (cubicThetaGradientRepresentative_memLp F).coeFn_toLp,
      (cubicThetaGradientRepresentative_memLp G).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaGradientRepresentative_memLp F).toLp _)
        ((cubicThetaGradientRepresentative_memLp G).toLp _)] with q hFG hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hFG,hadd,hF,hG]
    exact cubicThetaSectionGradient_add F G _
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(cubicThetaGradientRepresentative_memLp (c • F)).coeFn_toLp,
      (cubicThetaGradientRepresentative_memLp F).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaGradientRepresentative_memLp F).toLp _)] with q hCF hF hsmul
    simp only [Pi.smul_apply] at hsmul
    simp only [RingHom.id_apply]
    rw [hCF,hsmul,hF]
    exact cubicThetaSectionGradient_smul c F _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global energy completion of genuine compact smooth cubic
sections. Its two coordinates are the value and the actual gradient. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaGlobalEnergyGraph : cubicThetaSmoothTests →ₗ[ℂ] CubicThetaGlobalEnergyAmbient :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).symm.toLinearMap.comp
    (cubicThetaGlobalMass.prod cubicThetaGlobalGradient)

def cubicThetaGlobalEnergySpace : Submodule ℂ CubicThetaGlobalEnergyAmbient :=
  cubicThetaGlobalEnergyGraph.range.topologicalClosure

instance cubicThetaGlobalEnergySpace_complete : CompleteSpace cubicThetaGlobalEnergySpace :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaGlobalInclusion : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGlobalL2 :=
  (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).comp
    cubicThetaGlobalEnergySpace.subtypeL

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A half-open three-Eisenstein period cell gives a genuinely injective
high cusp strip in the arithmetic quotient. Boundary points retain their
unique representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPeriodCoordinates_continuous : Continuous cubicThetaPeriodCoordinates :=
  eisensteinRealCoords.symm.continuous.comp (continuous_id.div_const 3)

lemma cubicThetaPeriodCoordinates_translate (z : ℂ) (w : Eisenstein) :
    cubicThetaPeriodCoordinates (z+3*(w:ℂ))=
      cubicThetaPeriodCoordinates z+fun i => ((coordinatesEquiv.symm w) i:ℝ) := by
  have hw : (w:ℂ)=eisensteinRealCoords (fun i => ((coordinatesEquiv.symm w) i:ℝ)) := by
    rw [eisensteinRealCoords_integer]
    change (w:ℂ)=(coordinatesEquiv (coordinatesEquiv.symm w):ℂ)
    rw [LinearEquiv.apply_symm_apply]
  unfold cubicThetaPeriodCoordinates
  rw [show (z+3*(w:ℂ))/3=z/3+(w:ℂ) by ring,map_add,hw,
    ContinuousLinearEquiv.symm_apply_apply]

lemma cubicThetaPeriodCoordinates_injective : Function.Injective cubicThetaPeriodCoordinates := by
  intro z w h
  have h' := eisensteinRealCoords.symm.injective h
  exact (div_left_inj' (by norm_num : (3:ℂ)≠0)).mp h'

lemma cubicThetaCuspStrip_measurable (H : ℝ) : MeasurableSet (cubicThetaCuspStrip H) := by
  have hc : Continuous cubicThetaPointCoordinates := continuous_subtype_val
  have hv : Measurable (fun p : CubicThetaPoint => (cubicThetaPointCoordinates p).2) :=
    (continuous_snd.comp hc).measurable
  have hx (i : Fin 2) : Measurable (fun p : CubicThetaPoint =>
      cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1 i) :=
    ((continuous_apply i).comp
      (cubicThetaPeriodCoordinates_continuous.comp (continuous_fst.comp hc))).measurable
  have hall : MeasurableSet {p : CubicThetaPoint | ∀ i,
      cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1 i∈Ico (0:ℝ) 1} := by
    convert MeasurableSet.iInter (fun i =>
      (measurableSet_Ico : MeasurableSet (Ico (0:ℝ) 1)).preimage (hx i)) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [mem_iInter,mem_preimage,mem_ofPred_eq]
  exact (measurableSet_Ioi.preimage hv).inter hall

theorem cubicThetaCuspStrip_injective {H : ℝ} (hH : 1≤H) :
    InjOn cubicThetaQuotientMap (cubicThetaCuspStrip H) := by
  intro p hp q hq he
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change g • q=p at hg
  have hp' : 1<p.val.2 := lt_of_le_of_lt hH hp.1
  have hq' : 1<q.val.2 := lt_of_le_of_lt hH hq.1
  have hgp : 1<(g • q).val.2 := by
    change 1<(cubicThetaPointCoordinates (g • q)).2
    rw [hg]
    exact hp'
  obtain ⟨w,hw⟩ := cubicThetaPrincipal_high_translation g hq' hgp
  change cubicThetaPointCoordinates (g • q)=(q.val.1+3*(w:ℂ),q.val.2) at hw
  rw [hg] at hw
  have hz : (cubicThetaPointCoordinates p).1=(cubicThetaPointCoordinates q).1+3*(w:ℂ) :=
    congrArg Prod.fst hw
  have hc : cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1=
      cubicThetaPeriodCoordinates (cubicThetaPointCoordinates q).1 := by
    funext i
    apply halfOpen_integer_unique (hp.2 i) (hq.2 i) (n:=(coordinatesEquiv.symm w) i)
    rw [hz,cubicThetaPeriodCoordinates_translate]
    rfl
  apply Subtype.ext
  apply Prod.ext
  · exact cubicThetaPeriodCoordinates_injective hc
  · have hv := congrArg (fun z : ℂ × ℝ => z.2) hw
    exact hv

lemma cubicThetaQuotient_injective_image_measurable {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S) :
    MeasurableSet (cubicThetaQuotientMap '' S) :=
  hS.image_of_continuousOn_injOn cubicThetaQuotientMap_open.continuous.continuousOn hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quotient integration on the half-open arithmetic cusp strip.
This identifies the cusp mass and energy with their global restrictions,
including the boundary convention of the horizontal period cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInjective_map_restrict {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap=
      cubicThetaQuotientMeasure.restrict (cubicThetaQuotientMap '' S) := by
  ext B hB
  have hT := (hB.preimage cubicThetaQuotientMap_open.continuous.measurable).inter hS
  have hTi := hi.mono (inter_subset_right : cubicThetaQuotientMap ⁻¹' B ∩ S⊆S)
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable),
    ← cubicThetaQuotientMeasure_local_image hT
      (cubicThetaQuotient_injective_image_measurable hT hTi) hTi,
    Set.image_preimage_inter,Measure.restrict_apply hB]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heights of all representatives above a compact quotient set are
uniformly bounded. The arithmetic denominator bound is essential here:
a nonparabolic transformation sends height v to at most 1/v. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPointHeight_local_bound (q : CubicThetaQuotient) :
    ∃ U∈𝓝 q, ∃ C : ℝ, ∀ p : CubicThetaPoint,
      cubicThetaQuotientMap p∈U → ∀ δ : SL(2,Eisenstein), cubicThetaPointHeight (δ • p)≤C := by
  let p := cubicThetaQuotientLift q
  let e := cubicThetaCoveringChart p
  have hp : p∈e.source := cubicThetaCoveringChart_source p
  have he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap :=
    cubicThetaCoveringChart_coe p
  have heq : e p=q := by rw [he]; exact cubicThetaQuotientLift_map q
  have hq : q∈e.target := heq ▸ e.map_source hp
  have hinv : e.symm q=p := by rw [← heq]; exact e.left_inv hp
  let v := cubicThetaPointHeight p
  have hv : 0<v := cubicThetaPointHeight_pos p
  have hcont : ContinuousAt (fun r => cubicThetaPointHeight (e.symm r)) q :=
    cubicThetaPointHeight_continuous.continuousAt.comp
      (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hq))
  have hI : ∀ᶠ r in 𝓝 q, cubicThetaPointHeight (e.symm r)∈Ioo (v/2) (2*v) := by
    apply hcont.eventually
    apply Ioo_mem_nhds
    · change v/2 < cubicThetaPointHeight (e.symm q)
      rw [hinv]
      change v/2<v
      linarith
    · change cubicThetaPointHeight (e.symm q)<2*v
      rw [hinv]
      change v<2*v
      linarith
  let U := {r | r∈e.target ∧ cubicThetaPointHeight (e.symm r)∈Ioo (v/2) (2*v)}
  refine ⟨U,inter_mem (e.open_target.mem_nhds hq) hI,max (2*v) (2/v),?_⟩
  intro x hx δ
  let y := e.symm (cubicThetaQuotientMap x)
  have hy : cubicThetaQuotientMap y=cubicThetaQuotientMap x := by
    have h := e.right_inv hx.1
    change e y=cubicThetaQuotientMap x at h
    rwa [he] at h
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp hy.symm
  change g.val • y=x at hg
  have hb := cubicThetaPointHeight_full_smul_le (δ*g.val) y
  rw [mul_smul,hg] at hb
  apply hb.trans
  apply max_le
  · exact hx.2.2.le.trans (le_max_left _ _)
  · have hdiv : 1/cubicThetaPointHeight y≤2/v := by
      apply (div_le_div_iff₀ (cubicThetaPointHeight_pos y) hv).mpr
      have hylow : v/2 < cubicThetaPointHeight y := hx.2.1
      linarith
    exact hdiv.trans (le_max_right _ _)

theorem cubicThetaCompact_all_cusp_height_bound {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ p : CubicThetaPoint, cubicThetaQuotientMap p∈K →
      ∀ δ : SL(2,Eisenstein), cubicThetaPointHeight (δ • p)≤C := by
  classical
  choose U hU C hC using cubicThetaPointHeight_local_bound
  obtain ⟨A,_,hA⟩ := hK.elim_nhds_subcover U (fun q _ => hU q)
  refine ⟨∑ q∈A, max (C q) 0,Finset.sum_nonneg (fun q _ => le_max_right _ _),?_⟩
  intro p hp δ
  obtain ⟨q,hq,hpq⟩ := mem_iUnion₂.mp (hA hp)
  exact (hC q p hpq δ).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun r _ => le_max_right (C r) 0) hq))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar mass and energy on the exact half-open high cusp
strip. These are the Fubini bounds for the radial Hardy estimate. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalCell : Set ℂ :=
  {z | ∀ i, cubicThetaPeriodCoordinates z i∈Ico (0:ℝ) 1}

lemma cubicThetaCuspStrip_coordinates {H : ℝ} (hH : 0≤H) :
    cubicThetaPointCoordinates '' cubicThetaCuspStrip H=
      cubicThetaHorizontalCell ×ˢ Ioi H := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨hp.2,hp.1⟩
  · rintro ⟨hy,hv⟩
    exact ⟨⟨y,lt_of_le_of_lt hH hv⟩,⟨hv,hy⟩,rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTranslatedCuspStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every arithmetic cusp strip remains injective after an integral
Mobius transformation. Normality of the actual level-three group and
invariance of hyperbolic measure give the exact transported integrals. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaTranslatedCuspStrip (δ : SL(2,Eisenstein)) (H : ℝ) : Set CubicThetaPoint :=
  (fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCompact
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact parallelogram contains the actual half-open cusp
cell, giving its finite measure and a uniform horizontal norm bound. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCell_compact_container :
    ∃ K : Set ℂ, IsCompact K ∧ cubicThetaHorizontalCell⊆K := by
  let Q : Set (Fin 2 → ℝ) := Icc 0 1
  let f : (Fin 2 → ℝ) → ℂ := fun x => 3*eisensteinRealCoords x
  refine ⟨f '' Q,isCompact_Icc.image (continuous_const.mul eisensteinRealCoords.continuous),?_⟩
  intro z hz
  refine ⟨cubicThetaPeriodCoordinates z,?_,?_⟩
  · exact ⟨fun i => (hz i).1,fun i => (hz i).2.le⟩
  · dsimp only [f,cubicThetaPeriodCoordinates]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ring

lemma cubicThetaHorizontalCell_measure_ne_top : volume cubicThetaHorizontalCell≠⊤ := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact (lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top).ne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1Energy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The value and differential of compact C1 sections define genuine
L2 data. Smooth approximation will place these data in the energy graph. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Differential_automorphy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    (cubicThetaSectionDifferential F (g • p)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g) p.val)=
      cubicThetaKubotaValue g • cubicThetaSectionDifferential F p := by
  have hd {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaSectionFunction F) y :=
    (hF.contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt (by norm_num)
  have hm := cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g) p.property
  have hM := (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g)
    p.property).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hF := hd p.property
  have hG := hd hm
  have he : (fun y => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaPrincipalComplex g) y))=ᶠ[𝓝 p.val]
      (fun y => cubicThetaKubotaValue g*cubicThetaSectionFunction F y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with y hy
    exact cubicThetaSectionFunction_automorphy F g hy
  have hd' := ((hG.hasFDerivAt.comp p.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    (hF.hasFDerivAt.const_mul (cubicThetaKubotaValue g))
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) hd'
  have hgp : (g • p).val=cubicThetaMobius (cubicThetaPrincipalComplex g) p.val := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,hgp,
    ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hv

lemma cubicThetaC1Energy_invariant (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy F (g • p)=
      cubicThetaSectionEnergy F p := by
  have he := congrArg cubicThetaTangentEnergy (cubicThetaC1Differential_automorphy F hF g p)
  rw [cubicThetaTangentEnergy_derivative _ _ p.property,
    cubicThetaTangentEnergy_complex_smul,cubicThetaKubotaValue_norm,one_pow,one_mul] at he
  change (cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (g • p))=
    p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential F p)
  calc
    _ = p.val.2^2*(((cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2/p.val.2)^2*
        cubicThetaTangentEnergy (cubicThetaSectionDifferential F (g • p))) := by
      field_simp [p.property.ne']
    _ = _ := by rw [he]

lemma cubicThetaC1Energy_continuous (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2}) :
    Continuous (cubicThetaSectionEnergy F) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (hF.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  unfold cubicThetaSectionEnergy cubicThetaTangentEnergy cubicThetaSectionDifferential
  apply ((continuous_snd.comp continuous_subtype_val).pow 2).mul
  apply continuous_finsetSum
  intro i hi
  exact ((hd.clm_apply continuous_const).norm).pow 2


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1L2
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 sections have genuine value-gradient L2 data, before
any assertion that they belong to the closed smooth energy graph. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaC1QuotientEnergy (F : CubicThetaSection) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaSectionEnergy F (cubicThetaQuotientLift q)

lemma cubicThetaC1QuotientEnergy_apply (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    cubicThetaC1QuotientEnergy F (cubicThetaQuotientMap p)=cubicThetaSectionEnergy F p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaC1QuotientEnergy
  rw [← hg,cubicThetaC1Energy_invariant F hF]

lemma cubicThetaC1QuotientEnergy_continuous (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaC1QuotientEnergy F) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaC1QuotientEnergy F ∘ cubicThetaQuotientMap=cubicThetaSectionEnergy F :=
    funext (cubicThetaC1QuotientEnergy_apply F hF)
  rw [he]
  exact cubicThetaC1Energy_continuous F hF

lemma cubicThetaC1QuotientEnergy_compact (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    HasCompactSupport (cubicThetaC1QuotientEnergy F) := by
  apply hc.mono'
  intro q hq
  by_contra hn
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  apply hq
  simp only [cubicThetaC1QuotientEnergy,cubicThetaSectionEnergy,hd,
    cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,mul_zero]

lemma cubicThetaC1Gradient_continuous (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaSectionGradient F) := by
  have hd : Continuous (fun p : CubicThetaPoint => fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (hF.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaC1Gradient_norm_sq (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) (q : CubicThetaQuotient) :
    ‖cubicThetaGradientRepresentative F q‖^2=cubicThetaC1QuotientEnergy F q := by
  unfold cubicThetaGradientRepresentative
  rw [cubicThetaSectionGradient_norm_sq,← cubicThetaC1QuotientEnergy_apply F hF,
    cubicThetaBorelSection_rightInverse]

lemma cubicThetaC1Gradient_memLp (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure := by
  have hm : Measurable (cubicThetaGradientRepresentative F) :=
    (cubicThetaC1Gradient_continuous F hF).measurable.comp cubicThetaBorelSection_measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [cubicThetaC1Gradient_norm_sq F hF] using
    (cubicThetaC1QuotientEnergy_continuous F hF).integrable_of_hasCompactSupport
      (cubicThetaC1QuotientEnergy_compact F hc)

lemma cubicThetaCompactSection_memLp (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure := by
  apply (memLp_norm_iff (cubicThetaSectionRepresentative_measurable F).aestronglyMeasurable).mp
  simpa only [cubicThetaSectionRepresentative_norm] using
    (cubicThetaSectionNorm_continuous F).memLp_of_hasCompactSupport hc

def cubicThetaC1EnergyData (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) : CubicThetaGlobalEnergyAmbient :=
  WithLp.toLp 2 ((cubicThetaCompactSection_memLp F hc).toLp _,
    (cubicThetaC1Gradient_memLp F hF hc).toLp _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1EnergyNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of compact C1 value-gradient data is the actual
hyperbolic mass-plus-gradient integral. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1EnergyData_norm_sq (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    ‖cubicThetaC1EnergyData F hF hc‖^2=
      ∫ q, cubicThetaSectionNorm F q^2+cubicThetaC1QuotientEnergy F q
        ∂cubicThetaQuotientMeasure := by
  let m := cubicThetaCompactSection_memLp F hc
  let g := cubicThetaC1Gradient_memLp F hF hc
  have hm : Integrable (fun q => ‖cubicThetaSectionRepresentative F q‖^2)
      cubicThetaQuotientMeasure := m.integrable_norm_pow (by norm_num)
  have hg : Integrable (fun q => ‖cubicThetaGradientRepresentative F q‖^2)
      cubicThetaQuotientMeasure := g.integrable_norm_pow (by norm_num)
  have hv : (∫ q, ‖m.toLp (cubicThetaSectionRepresentative F) q‖^2 ∂cubicThetaQuotientMeasure)=
      ∫ q, ‖cubicThetaSectionRepresentative F q‖^2 ∂cubicThetaQuotientMeasure := by
    apply integral_congr_ae
    filter_upwards [m.coeFn_toLp] with q hq
    rw [hq]
  have hd : (∫ q, ‖g.toLp (cubicThetaGradientRepresentative F) q‖^2 ∂cubicThetaQuotientMeasure)=
      ∫ q, ‖cubicThetaGradientRepresentative F q‖^2 ∂cubicThetaQuotientMeasure := by
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp] with q hq
    rw [hq]
  calc
    _ = ‖m.toLp (cubicThetaSectionRepresentative F)‖^2+
        ‖g.toLp (cubicThetaGradientRepresentative F)‖^2 :=
      WithLp.prod_norm_sq_eq_of_L2 _
    _ = (∫ q, ‖cubicThetaSectionRepresentative F q‖^2 ∂cubicThetaQuotientMeasure)+
        ∫ q, ‖cubicThetaGradientRepresentative F q‖^2 ∂cubicThetaQuotientMeasure := by
      rw [cubicTheta_l2_norm_sq_measure,cubicTheta_l2_norm_sq_measure,hv,hd]
    _ = _ := by
      rw [← integral_add hm hg]
      apply integral_congr_ae
      filter_upwards with q
      rw [cubicThetaSectionRepresentative_norm,cubicThetaC1Gradient_norm_sq F hF]

lemma cubicThetaC1EnergyData_smooth (F : cubicThetaSmoothTests) :
    cubicThetaC1EnergyData F (F.property.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) F.property.2=
      cubicThetaGlobalEnergyGraph F := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1EnergyLinear
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subtraction of actual compact C1 value-gradient data agrees with
subtraction in the Hilbert ambient space. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1EnergyData_congr {F G : CubicThetaSection} (he : F=G)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hcF : HasCompactSupport (cubicThetaSectionNorm F))
    (hcG : HasCompactSupport (cubicThetaSectionNorm G)) :
    cubicThetaC1EnergyData F hF hcF=cubicThetaC1EnergyData G hG hcG := by
  subst G
  rfl

lemma cubicThetaCompactSection_sub (F G : CubicThetaSection)
    (hF : HasCompactSupport (cubicThetaSectionNorm F))
    (hG : HasCompactSupport (cubicThetaSectionNorm G)) :
    HasCompactSupport (cubicThetaSectionNorm (F-G)) := by
  apply (hF.union hG).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hF.union hG).isClosed
  intro q hq
  by_contra h
  have hFq : cubicThetaSectionNorm F q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hFq => h (Or.inl hFq))
  have hGq : cubicThetaSectionNorm G q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hGq => h (Or.inr hGq))
  apply hq
  change ‖F.val (cubicThetaQuotientLift q)-G.val (cubicThetaQuotientLift q)‖=0
  rw [norm_eq_zero.mp hFq,norm_eq_zero.mp hGq,sub_self,norm_zero]

lemma cubicThetaC1Gradient_sub (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) (p : CubicThetaPoint) :
    cubicThetaSectionGradient (F-G) p=cubicThetaSectionGradient F p-cubicThetaSectionGradient G p := by
  have hdF := (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).differentiableAt (by norm_num)
  have hdG := (hG.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).differentiableAt (by norm_num)
  have he : cubicThetaSectionFunction (F-G)=cubicThetaSectionFunction F-cubicThetaSectionFunction G := rfl
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,he,fderiv_sub hdF hdG,
    ContinuousLinearMap.comp_apply,sub_apply,smul_sub]
  rfl

lemma cubicThetaC1EnergyData_sub (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hcF : HasCompactSupport (cubicThetaSectionNorm F))
    (hcG : HasCompactSupport (cubicThetaSectionNorm G)) :
    cubicThetaC1EnergyData (F-G) (hF.sub hG) (cubicThetaCompactSection_sub F G hcF hcG)=
      cubicThetaC1EnergyData F hF hcF-cubicThetaC1EnergyData G hG hcG := by
  have hcD := cubicThetaCompactSection_sub F G hcF hcG
  have hD : ContDiffOn ℝ 1 (cubicThetaSectionFunction (F-G)) {y : ℂ × ℝ | 0<y.2} := hF.sub hG
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).injective
  apply Prod.ext
  · change (cubicThetaCompactSection_memLp (F-G) hcD).toLp _=
      (cubicThetaCompactSection_memLp F hcF).toLp _-(cubicThetaCompactSection_memLp G hcG).toLp _
    apply Lp.ext
    filter_upwards [(cubicThetaCompactSection_memLp (F-G) hcD).coeFn_toLp,
      (cubicThetaCompactSection_memLp F hcF).coeFn_toLp,
      (cubicThetaCompactSection_memLp G hcG).coeFn_toLp,
      Lp.coeFn_sub ((cubicThetaCompactSection_memLp F hcF).toLp _)
        ((cubicThetaCompactSection_memLp G hcG).toLp _)] with q hD hFq hGq hs
    simp only [Pi.sub_apply] at hs
    rw [hD,hs,hFq,hGq]
    rfl
  · change (cubicThetaC1Gradient_memLp (F-G) hD hcD).toLp _=
      (cubicThetaC1Gradient_memLp F hF hcF).toLp _-(cubicThetaC1Gradient_memLp G hG hcG).toLp _
    apply Lp.ext
    filter_upwards [(cubicThetaC1Gradient_memLp (F-G) hD hcD).coeFn_toLp,
      (cubicThetaC1Gradient_memLp F hF hcF).coeFn_toLp,
      (cubicThetaC1Gradient_memLp G hG hcG).coeFn_toLp,
      Lp.coeFn_sub ((cubicThetaC1Gradient_memLp F hF hcF).toLp _)
        ((cubicThetaC1Gradient_memLp G hG hcG).toLp _)] with q hD hFq hGq hs
    simp only [Pi.sub_apply] at hs
    rw [hD,hs,hFq,hGq]
    exact cubicThetaC1Gradient_sub F G hF hG _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1GradientLinear
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise complex linearity of the actual differential on C1 sections. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaC1Gradient_add (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) (p : CubicThetaPoint) :
    cubicThetaSectionGradient (F+G) p=cubicThetaSectionGradient F p+cubicThetaSectionGradient G p := by
  have hp : {y : ℂ × ℝ | 0<y.2}∈nhds p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hdF := (hF.contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdG := (hG.contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : cubicThetaSectionFunction (F+G)=cubicThetaSectionFunction F+cubicThetaSectionFunction G := rfl
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,he,fderiv_add hdF hdG,
    ContinuousLinearMap.comp_apply,add_apply,smul_add]
  rfl

lemma cubicThetaC1Gradient_smul (c : ℂ) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) (p : CubicThetaPoint) :
    cubicThetaSectionGradient (c • F) p=c • cubicThetaSectionGradient F p := by
  have hp : {y : ℂ × ℝ | 0<y.2}∈nhds p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hdF := (hF.contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : cubicThetaSectionFunction (c • F)=c • cubicThetaSectionFunction F := rfl
  ext i
  simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,he,fderiv_const_smul hdF c,
    ContinuousLinearMap.comp_apply,smul_apply]
  exact smul_comm p.val.2 c (cubicThetaSectionDifferential F p (cubicThetaTangentBasis i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1EnergySums
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums of compact C1 sections preserve their actual
value-gradient data. This permits finite reconstruction from chart pieces. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCompactSection_add (F G : CubicThetaSection)
    (hF : HasCompactSupport (cubicThetaSectionNorm F))
    (hG : HasCompactSupport (cubicThetaSectionNorm G)) :
    HasCompactSupport (cubicThetaSectionNorm (F+G)) := by
  apply (hF.union hG).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hF.union hG).isClosed
  intro q hq
  by_contra h
  have hFq : cubicThetaSectionNorm F q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hFq => h (Or.inl hFq))
  have hGq : cubicThetaSectionNorm G q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hGq => h (Or.inr hGq))
  apply hq
  change ‖F.val (cubicThetaQuotientLift q)+G.val (cubicThetaQuotientLift q)‖=0
  rw [norm_eq_zero.mp hFq,norm_eq_zero.mp hGq,add_zero,norm_zero]

lemma cubicThetaC1EnergyData_add (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hcF : HasCompactSupport (cubicThetaSectionNorm F))
    (hcG : HasCompactSupport (cubicThetaSectionNorm G)) :
    cubicThetaC1EnergyData (F+G) (hF.add hG) (cubicThetaCompactSection_add F G hcF hcG)=
      cubicThetaC1EnergyData F hF hcF+cubicThetaC1EnergyData G hG hcG := by
  have h := cubicThetaC1EnergyData_sub (F+G) G (hF.add hG) hG
    (cubicThetaCompactSection_add F G hcF hcG) hcG
  have he : cubicThetaC1EnergyData F hF hcF=
      cubicThetaC1EnergyData (F+G) (hF.add hG) (cubicThetaCompactSection_add F G hcF hcG)-
        cubicThetaC1EnergyData G hG hcG := by
    have heq : F+G-G=F := add_sub_cancel_right F G
    exact (cubicThetaC1EnergyData_congr heq _ _ _ _).symm.trans h
  exact (eq_sub_iff_add_eq.mp he).symm

lemma cubicThetaSectionFunction_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection) :
    cubicThetaSectionFunction (∑ i∈A, F i)=fun y => ∑ i∈A, cubicThetaSectionFunction (F i) y := by
  funext y
  simp [cubicThetaSectionFunction]

lemma cubicThetaC1Section_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection)
    (hF : ∀ i, ContDiffOn ℝ 1 (cubicThetaSectionFunction (F i)) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (∑ i∈A, F i)) {y : ℂ × ℝ | 0<y.2} := by
  rw [cubicThetaSectionFunction_sum]
  exact ContDiffOn.sum (fun i _ => hF i)

lemma cubicThetaCompactSection_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection)
    (hc : ∀ i, HasCompactSupport (cubicThetaSectionNorm (F i))) :
    HasCompactSupport (cubicThetaSectionNorm (∑ i∈A, F i)) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)
      have hz : (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)=(0 : CubicThetaQuotient → ℝ) := by
        funext q
        exact norm_zero
      rw [hz]
      exact HasCompactSupport.zero
  | @insert i A hi ih =>
      simpa only [Finset.sum_insert hi] using cubicThetaCompactSection_add (F i) (∑ j∈A, F j) (hc i) ih

lemma cubicThetaC1EnergyData_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection)
    (hF : ∀ i, ContDiffOn ℝ 1 (cubicThetaSectionFunction (F i)) {y : ℂ × ℝ | 0<y.2})
    (hc : ∀ i, HasCompactSupport (cubicThetaSectionNorm (F i))) :
    cubicThetaC1EnergyData (∑ i∈A, F i) (cubicThetaC1Section_sum A F hF)
      (cubicThetaCompactSection_sum A F hc)=∑ i∈A, cubicThetaC1EnergyData (F i) (hF i) (hc i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact (cubicThetaC1EnergyData_smooth (0 : cubicThetaSmoothTests)).trans (map_zero _)
  | @insert i A hi ih =>
      simp only [Finset.sum_insert hi]
      rw [cubicThetaC1EnergyData_add (F i) (∑ j∈A, F j) (hF i)
        (cubicThetaC1Section_sum A F hF) (hc i) (cubicThetaCompactSection_sum A F hc)]
      rw [ih]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal reduction into the exact half-open cusp strip uses the
actual principal translations. It is compatible with every arithmetic
cusp through the proved conjugation in the level-three group. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspStrip_reduction {H : ℝ} (p : CubicThetaPoint)
    (hp : H < cubicThetaPointHeight p) :
    ∃ w : Eisenstein, cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip H := by
  let x := cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1
  let n : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let w := coordinatesEquiv n
  refine ⟨w,?_⟩
  constructor
  · rw [cubicThetaPrincipalTranslation_coordinates]
    exact hp
  · intro i
    rw [cubicThetaPrincipalTranslation_coordinates,cubicThetaPeriodCoordinates_translate]
    have h : (cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1+
        fun j => ((coordinatesEquiv.symm w) j:ℝ)) i=Int.fract (x i) := by
      simp only [w,LinearEquiv.symm_apply_apply,Pi.add_apply,n,Int.cast_neg]
      rfl
    rw [h]
    exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

def cubicThetaCuspNeighborhood (δ : SL(2,Eisenstein)) (H : ℝ) : Set CubicThetaQuotient :=
  cubicThetaQuotientMap '' cubicThetaTranslatedCuspStrip δ H

lemma cubicThetaCuspNeighborhood_mem_of_height (δ : SL(2,Eisenstein)) {H : ℝ}
    (p : CubicThetaPoint) (hp : H < cubicThetaPointHeight p) :
    cubicThetaQuotientMap (δ • p)∈cubicThetaCuspNeighborhood δ H := by
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hp
  let g := cubicThetaPrincipalTranslation w
  let k := cubicThetaPrincipalConjugate δ⁻¹ g
  have hk : k • (δ • p)=δ • (g • p) := by
    change ((δ⁻¹)⁻¹*g.val*δ⁻¹) • (δ • p)=δ • (g.val • p)
    rw [inv_inv,mul_smul,mul_smul,inv_smul_smul]
  refine ⟨δ • (g • p),⟨g • p,hw,rfl⟩,?_⟩
  rw [← hk,cubicThetaQuotient_covering.map_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspNeighborhoodCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite arithmetic core/cusp cover, with each unbounded
part replaced by its exact half-open period strip. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCuspNeighborhood_cover :
    ∃ S : Finset SL(2,Eisenstein), ∀ V : ℝ,
      cubicThetaQuotientCore S V ∪ (⋃ δ∈S, cubicThetaCuspNeighborhood δ⁻¹ V)=univ := by
  obtain ⟨S,hS⟩ := cubicThetaQuotientCore_cusps_cover
  refine ⟨S,fun V => Set.eq_univ_of_forall ?_⟩
  intro q
  have hq : q∈cubicThetaQuotientCore S V ∪ cubicThetaQuotientCusps S V := by
    rw [hS V]
    trivial
  rcases hq with hq | ⟨p,hp,hpq⟩
  · exact Or.inl hq
  · obtain ⟨δ,hδ⟩ := mem_iUnion.mp hp
    obtain ⟨hδS,y,hy,hyp⟩ := mem_iUnion.mp hδ
    let r : CubicThetaPoint := ⟨y,hy.1.1⟩
    have hr : δ⁻¹ • r=p := Subtype.ext hyp
    have hn := cubicThetaCuspNeighborhood_mem_of_height δ⁻¹ r hy.2
    rw [hr,hpq] at hn
    exact Or.inr (mem_iUnion.mpr ⟨δ,mem_iUnion.mpr ⟨hδS,hn⟩⟩)

theorem cubicThetaCuspTransition_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1 ≤ cubicThetaPointHeight p → cubicThetaPointHeight p≤2 →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S 2 := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y≤2 := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le hp₂
    apply (div_le_iff₀ (cubicThetaPointHeight_pos p)).mpr
    linarith
  have hyc : y.val∈cubicThetaSiegelCore 2 := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,?_⟩
  · change (k • q).val∈cubicThetaCompactCore S 2
    refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
    have he := congrArg cubicThetaPointCoordinates hpoint
    exact he
  · exact cubicThetaQuotient_covering.map_smul k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspDisjointness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Above height one, two arithmetic cusp neighborhoods are either
identical at every height or disjoint. This removes duplicate cusp
charts before summing the sharp exterior energy inequality. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_mem_iff (δ : SL(2,Eisenstein)) (H : ℝ)
    (q : CubicThetaQuotient) :
    q∈cubicThetaCuspNeighborhood δ H ↔ ∃ p : CubicThetaPoint,
      H < cubicThetaPointHeight p ∧ cubicThetaQuotientMap (δ • p)=q := by
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,he⟩
    exact ⟨p,hp.1,he⟩
  · rintro ⟨p,hp,rfl⟩
    exact cubicThetaCuspNeighborhood_mem_of_height δ p hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactInCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every compact subset of the actual arithmetic quotient lies in
one of the constructed compact cores. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompact_subset_core {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ (S : Finset SL(2,Eisenstein)) (V : ℝ), K⊆cubicThetaQuotientCore S V := by
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_all_cusp_height_bound hK
  refine ⟨S,C+1,?_⟩
  intro q hq
  have hcover : q∈cubicThetaQuotientCore S (C+1) ∪
      ⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ (C+1) := by rw [hS]; trivial
  rcases hcover with hcore | hcusp
  · exact hcore
  · obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hcusp
    obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ⁻¹ (C+1) q).mp hqδ
    have he : cubicThetaQuotientMap (δ⁻¹ • p)∈K := hpq ▸ hq
    have hh := hbound (δ⁻¹ • p) he δ
    rw [smul_inv_smul] at hh
    linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1Division
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divide a compact C1 section by a continuous invariant scalar
which is smooth and nonzero near its support. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_zero_eventually (F : CubicThetaSection)
    {y : ℂ × ℝ} (hy : 0<y.2)
    (hq : cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)∉tsupport (cubicThetaSectionNorm F)) :
    cubicThetaSectionFunction F=ᶠ[𝓝 y] (fun _ => (0:ℂ)) := by
  have ht : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  have hm := cubicThetaQuotientMap_open.continuous.continuousAt.comp
    (cubicThetaPointInclusion.symm.continuousAt ht)
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hq).comp_tendsto hm
  filter_upwards [hz] with z hz
  change cubicThetaSectionNorm F (cubicThetaQuotientMap (cubicThetaPointInclusion.symm z))=0 at hz
  rw [cubicThetaSectionNorm_apply] at hz
  exact norm_eq_zero.mp hz

def cubicThetaSectionDivide (F : CubicThetaSection) (D : CubicThetaQuotient → ℝ)
    (hD : Continuous D) (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0) :
    CubicThetaSection := by
  let f := fun p : CubicThetaPoint => F.val p/(D (cubicThetaQuotientMap p):ℂ)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hd : D (cubicThetaQuotientMap p)=0
    · have hout : cubicThetaQuotientMap p∉tsupport (cubicThetaSectionNorm F) :=
        fun h => hn _ h hd
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
        cubicThetaQuotientMap_open.continuous.continuousAt
      have hzf : f=ᶠ[𝓝 p] (fun _ => (0:ℂ)) := by
        filter_upwards [hz] with r hr
        change cubicThetaSectionNorm F (cubicThetaQuotientMap r)=0 at hr
        rw [cubicThetaSectionNorm_apply] at hr
        dsimp only [f]
        rw [norm_eq_zero.mp hr,zero_div]
      exact continuousAt_const.congr_of_eventuallyEq hzf
    · exact F.val.continuous.continuousAt.div
        (Complex.continuous_ofReal.comp (hD.comp cubicThetaQuotientMap_open.continuous)).continuousAt
        (by exact_mod_cast hd)
  exact ⟨⟨f,hf⟩,by
    intro g p
    change F.val (g • p)/(D (cubicThetaQuotientMap (g • p)):ℂ)=
      cubicThetaKubotaValue g*(F.val p/(D (cubicThetaQuotientMap p):ℂ))
    rw [cubicThetaQuotient_covering.map_smul,F.property g p]
    ring⟩

lemma cubicThetaSectionDivide_norm_support (F : CubicThetaSection) (D : CubicThetaQuotient → ℝ)
    (hD : Continuous D) (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0) :
    tsupport (cubicThetaSectionNorm (cubicThetaSectionDivide F D hD hn))⊆
      tsupport (cubicThetaSectionNorm F) := by
  apply closure_minimal _ isClosed_closure
  intro q hq
  by_contra h
  have hnorm : cubicThetaSectionNorm F q=0 := image_eq_zero_of_notMem_tsupport h
  have hz := norm_eq_zero.mp hnorm
  apply hq
  change ‖F.val (cubicThetaQuotientLift q)/(D (cubicThetaQuotientMap (cubicThetaQuotientLift q)):ℂ)‖=0
  rw [hz,zero_div,norm_zero]

lemma cubicThetaSectionDivide_regular (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (D : CubicThetaQuotient → ℝ) (hD : Continuous D)
    (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), D q≠0)
    (hDs : ContDiffOn ℝ 1 (fun y => D (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)))
      {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaSectionDivide F D hD hn))
      {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  by_cases hd : D (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=0
  · have hout : cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)∉tsupport (cubicThetaSectionNorm F) :=
      fun h => hn _ h hd
    have hhout : cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)∉
        tsupport (cubicThetaSectionNorm (cubicThetaSectionDivide F D hD hn)) :=
      fun h => hout (cubicThetaSectionDivide_norm_support F D hD hn h)
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ × ℝ => (0:ℂ)) y).congr_of_eventuallyEq
      (cubicThetaSectionFunction_zero_eventually _ hy hhout) |>.contDiffWithinAt
  · have hnb := (isOpen_lt continuous_const continuous_snd).mem_nhds hy
    have hfAt := hF.contDiffAt hnb
    have hdAt := Complex.ofRealCLM.contDiff.contDiffAt.comp y ((hDs.contDiffAt hnb).inv hd)
    change ContDiffWithinAt ℝ 1
      (fun z => cubicThetaSectionFunction F z /
        (D (cubicThetaQuotientMap (cubicThetaPointInclusion.symm z)):ℂ)) _ y
    simpa only [div_eq_mul_inv,Function.comp_apply,Pi.inv_apply,
      Complex.ofRealCLM_apply,Complex.ofReal_inv] using (hfAt.mul hdAt).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaChartRestrictedIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar integration in an injective quotient chart, for reconstruction
of the global core cutoff norm from its coordinate norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaChart_map_restrict
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap=
      cubicThetaQuotientMeasure.restrict (cubicThetaQuotientMap '' S) := by
  ext B hB
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable),
    ← cubicThetaQuotientMeasure_chart e he
      ((hB.preimage cubicThetaQuotientMap_open.continuous.measurable).inter hS)
      (fun _ hx => hSe hx.2),Set.image_preimage_inter,Measure.restrict_apply hB]

lemma cubicThetaChart_integral
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaChart_map_restrict e he hS hSe]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1ChartNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full energy norm of a compact C1 section supported in an
injective chart equals its literal integral over that covering sheet. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1EnergyData_chart_norm (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F))
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (hs : tsupport (cubicThetaSectionNorm F)⊆cubicThetaQuotientMap '' S) :
    ‖cubicThetaC1EnergyData F hF hc‖^2=
      ∫ p in S, ‖F.val p‖^2+cubicThetaSectionEnergy F p ∂cubicThetaPointMeasure := by
  rw [cubicThetaC1EnergyData_norm_sq]
  have hz : ∀ q, q∉cubicThetaQuotientMap '' S →
      cubicThetaSectionNorm F q^2+cubicThetaC1QuotientEnergy F q=0 := by
    intro q hq
    have hout : q∉tsupport (cubicThetaSectionNorm F) := fun h => hq (hs h)
    have hn := image_eq_zero_of_notMem_tsupport hout
    have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
      rwa [cubicThetaQuotientLift_map]
    have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
    simp only [hn,cubicThetaC1QuotientEnergy,cubicThetaSectionEnergy,hd,
      cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,add_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hcont : Continuous (fun q => cubicThetaSectionNorm F q^2+cubicThetaC1QuotientEnergy F q) :=
    ((cubicThetaSectionNorm_continuous F).pow 2).add (cubicThetaC1QuotientEnergy_continuous F hF)
  rw [cubicThetaChart_integral e he hS hSe _ hcont.stronglyMeasurable]
  apply setIntegral_congr_fun hS
  intro p hp
  dsimp only
  rw [cubicThetaSectionNorm_apply,cubicThetaC1QuotientEnergy_apply F hF]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact coordinate functions give actual automorphic sections.
Their C1 regularity follows from the locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported BigOperators ContDiff
namespace CubicFirstMoment

lemma cubicThetaPoincareSection_regular {n : ℕ∞} (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ n (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ n (cubicThetaSectionFunction (cubicThetaPoincareSection ψ))
      {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  have hy' : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  obtain ⟨s,hs⟩ := cubicTheta_locallyFinite_finsum _ (cubicThetaPoincareTerm_locallyFinite ψ)
    (cubicThetaPointInclusion.symm y)
  have he := hs.comp_tendsto (cubicThetaPointInclusion.symm.continuousAt hy')
  have hd : ContDiffAt ℝ n
      (fun x => ∑ g∈s, cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y :=
    ContDiffAt.sum (fun g _ => cubicThetaPoincareTerm_regular ψ hψ g hy)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

lemma cubicThetaCoordinateSection_regular {n : ℕ∞} {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ n g) (hc : HasCompactSupport g)
    (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ n (cubicThetaSectionFunction
      (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp)))
      {y : ℂ × ℝ | 0<y.2} := by
  apply cubicThetaPoincareSection_regular
  apply hg.contDiffOn.congr
  intro y hy
  exact cubicThetaCoordinateSeed_coordinates g hg.continuous hc hp hy

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSectionSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support and differential identities on an injective
covering sheet for periodized coordinate functions. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincareSection_norm_support (ψ : C_c(CubicThetaPoint,ℂ)) :
    tsupport (cubicThetaSectionNorm (cubicThetaPoincareSection ψ))⊆
      cubicThetaQuotientMap '' tsupport ψ := by
  have hc := ψ.hasCompactSupport.image cubicThetaQuotientMap_open.continuous
  apply closure_minimal _ hc.isClosed
  intro q hq
  let p := cubicThetaQuotientLift q
  have hn : (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)≠0 := by
    intro hz
    apply hq
    change ‖∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p‖=0
    simp [hz]
  have hex : ∃ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p≠0 := by
    by_contra! hn'
    exact hn (by simp [hn'])
  obtain ⟨g,hg⟩ := hex
  refine ⟨g • p,?_,?_⟩
  · apply subset_tsupport ψ
    intro hz
    exact hg (by simp [cubicThetaPoincareTerm,hz])
  · exact (cubicThetaQuotient_covering.map_smul g).trans (cubicThetaQuotientLift_map q)

lemma cubicThetaCoordinateSection_fderiv_on_sheet (g : ℂ × ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hs : Function.support (cubicThetaCoordinateSeed g hg hc hp)⊆e.source)
    {y : ℂ × ℝ} (hy : 0<y.2) (hye : cubicThetaPointInclusion.symm y∈e.source) :
    fderiv ℝ (cubicThetaSectionFunction
      (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg hc hp))) y=fderiv ℝ g y := by
  have ht : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  have hi := cubicThetaPointInclusion.symm.continuousAt ht
  have heq : cubicThetaSectionFunction
      (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg hc hp))=ᶠ[𝓝 y] g := by
    filter_upwards [hi.preimage_mem_nhds (e.open_source.mem_nhds hye),
      (isOpen_lt continuous_const continuous_snd).mem_nhds hy] with z hz hz0
    change (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg hc hp)).val
      (cubicThetaPointInclusion.symm z)=g z
    rw [cubicThetaPoincareSection_on_sheet _ e he hs hz]
    exact cubicThetaCoordinateSeed_coordinates g hg hc hp hz0
  exact heq.fderiv_eq

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSectionNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of a periodized C1 coordinate function is exactly its
local hyperbolic energy integral when its support lies in one chart. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace CubicFirstMoment

lemma cubicThetaCoordinateSection_norm_sq {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hpos : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let hp := hgs.trans hpos
    let F := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp)
    ‖cubicThetaC1EnergyData F (cubicThetaCoordinateSection_regular hg hc hp)
      (cubicThetaPoincareSection_compact _)‖^2=
      ∫ y in K, (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3 := by
  intro hp F
  let S := cubicThetaPointInclusion.symm '' K
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hS : IsCompact S := hK.image_of_continuousOn (hi.mono hpos)
  have hss : tsupport (cubicThetaCoordinateSeed g hg.continuous hc hp)⊆S :=
    (cubicThetaCoordinateSeed_support g hg.continuous hc hp).trans (image_mono hgs)
  have hnorm : tsupport (cubicThetaSectionNorm F)⊆cubicThetaQuotientMap '' S :=
    (cubicThetaPoincareSection_norm_support _).trans (image_mono hss)
  have hcoord : cubicThetaPointCoordinates '' S=K := by
    ext y
    constructor
    · rintro ⟨p,⟨z,hz,rfl⟩,rfl⟩
      have heq := cubicThetaPointInclusion.right_inv
        (show z∈cubicThetaPointInclusion.target by rw [cubicThetaPointInclusion_target]; exact hpos hz)
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)∈K
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)=z at heq
      rw [heq]
      exact hz
    · intro hy
      exact ⟨cubicThetaPointInclusion.symm y,⟨y,hy,rfl⟩,
        cubicThetaPointInclusion.right_inv (by rw [cubicThetaPointInclusion_target]; exact hpos hy)⟩
  rw [cubicThetaC1EnergyData_chart_norm F (cubicThetaCoordinateSection_regular hg hc hp)
    (cubicThetaPoincareSection_compact _) e he hS.measurableSet hKe hnorm]
  have hsupp : Function.support (cubicThetaCoordinateSeed g hg.continuous hc hp)⊆e.source :=
    subset_tsupport _ |>.trans (hss.trans hKe)
  have hpt (p : CubicThetaPoint) (hpS : p∈S) :
      ‖F.val p‖^2+cubicThetaSectionEnergy F p=
        ‖g (cubicThetaPointCoordinates p)‖^2+(cubicThetaPointCoordinates p).2^2*
          cubicThetaFunctionEnergy g (cubicThetaPointCoordinates p) := by
    have hp' : cubicThetaPointInclusion.symm p.val=p :=
      cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
    have hv : F.val p=g p.val := cubicThetaPoincareSection_on_sheet _ e he hsupp (hKe hpS)
    have hd := cubicThetaCoordinateSection_fderiv_on_sheet g hg.continuous hc hp e he hsupp
      p.property (by rw [hp']; exact hKe hpS)
    change fderiv ℝ (cubicThetaSectionFunction F) p.val=fderiv ℝ g p.val at hd
    rw [hv]
    unfold cubicThetaSectionEnergy cubicThetaSectionDifferential cubicThetaFunctionEnergy
    rw [hd]
    rfl
  rw [setIntegral_congr_fun hS.measurableSet hpt]
  simpa only [hcoord] using cubicThetaPointIntegral_density hS.measurableSet
    (fun y => ‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareLinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-support additivity of the actual periodization. -/
noncomputable section
open Set
open scoped BigOperators CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincareSection_sub (ψ φ : C_c(CubicThetaPoint,ℂ)) :
    cubicThetaPoincareSection (ψ-φ)=cubicThetaPoincareSection ψ-cubicThetaPoincareSection φ := by
  ext p
  change (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm (ψ-φ) g p)=
    (∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm ψ g p)-
      ∑ᶠ g : cubicThetaPrincipalGroup, cubicThetaPoincareTerm φ g p
  have h (g : cubicThetaPrincipalGroup) : cubicThetaPoincareTerm (ψ-φ) g p=
      cubicThetaPoincareTerm ψ g p-cubicThetaPoincareTerm φ g p := by
    change star (cubicThetaKubotaValue g)*(ψ (g • p)-φ (g • p))=_
    exact mul_sub _ _ _
  simp_rw [h]
  exact finsum_sub_distrib (cubicThetaPoincareTerm_locallyFinite ψ |>.point_finite p)
    (cubicThetaPoincareTerm_locallyFinite φ |>.point_finite p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateData
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual value-gradient data of periodized coordinate functions.
Smooth coordinate functions already lie in the defining energy graph. -/
noncomputable section
open Set
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaCoordinateData {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2}) :
    CubicThetaGlobalEnergyAmbient :=
  cubicThetaC1EnergyData (cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp))
    (cubicThetaCoordinateSection_regular hg hc hp) (cubicThetaPoincareSection_compact _)

lemma cubicThetaCoordinateData_sub {g h : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hcg : HasCompactSupport g) (hch : HasCompactSupport h)
    (hpg : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    (hph : tsupport h⊆{y : ℂ × ℝ | 0<y.2})
    (hpd : tsupport (g-h)⊆{y : ℂ × ℝ | 0<y.2}) :
    cubicThetaCoordinateData (hg.sub hh) (hcg.sub hch) hpd=
      cubicThetaCoordinateData hg hcg hpg-cubicThetaCoordinateData hh hch hph := by
  have hseed : cubicThetaCoordinateSeed (g-h) (hg.sub hh).continuous (hcg.sub hch) hpd=
      cubicThetaCoordinateSeed g hg.continuous hcg hpg-cubicThetaCoordinateSeed h hh.continuous hch hph := by
    ext p
    rfl
  have heq := (congrArg cubicThetaPoincareSection hseed).trans (cubicThetaPoincareSection_sub _ _)
  unfold cubicThetaCoordinateData
  let A := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hcg hpg)
  let B := cubicThetaPoincareSection (cubicThetaCoordinateSeed h hh.continuous hch hph)
  have hA := cubicThetaCoordinateSection_regular hg hcg hpg
  have hB := cubicThetaCoordinateSection_regular hh hch hph
  have hcA := cubicThetaPoincareSection_compact (cubicThetaCoordinateSeed g hg.continuous hcg hpg)
  have hcB := cubicThetaPoincareSection_compact (cubicThetaCoordinateSeed h hh.continuous hch hph)
  calc
    _ = cubicThetaC1EnergyData (A-B) (hA.sub hB)
        (cubicThetaCompactSection_sub A B hcA hcB) := by
      congr 1
    _ = _ := cubicThetaC1EnergyData_sub A B hA hB hcA hcB

lemma cubicThetaCoordinateData_norm_sq {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hpos : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    ‖cubicThetaCoordinateData hg hc (hgs.trans hpos)‖^2=
      ∫ y in K, (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3 :=
  cubicThetaCoordinateSection_norm_sq hg hc hK hpos hgs e he hKe

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateEnergyClosure
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact C1 coordinate function supported in one injective chart
belongs to the actual closed global energy graph, by explicit smoothing. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff
namespace CubicFirstMoment

theorem cubicThetaCoordinateData_mem_energy {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hs : cubicThetaPointInclusion.symm '' tsupport g⊆e.source) :
    cubicThetaCoordinateData hg hc hp∈cubicThetaGlobalEnergySpace := by
  let U := (e.symm.trans cubicThetaPointInclusion).target
  have hU : IsOpen U := (e.symm.trans cubicThetaPointInclusion).open_target
  have hgsU : tsupport g⊆U := by
    intro y hy
    change y∈cubicThetaPointInclusion.target ∧ cubicThetaPointInclusion.symm y∈e.source
    exact ⟨by rw [cubicThetaPointInclusion_target]; exact hp hy,hs ⟨y,hy,rfl⟩⟩
  obtain ⟨K,hK,hgK,hKU,happrox⟩ := cubicThetaSmoothing_compact_chart hg hc hU hgsU
  have hpos : K⊆{y : ℂ × ℝ | 0<y.2} := by
    intro y hy
    have h := (hKU hy).1
    rwa [cubicThetaPointInclusion_target] at h
  have hKe : cubicThetaPointInclusion.symm '' K⊆e.source := by
    rintro p ⟨y,hy,rfl⟩
    exact (hKU hy).2
  obtain ⟨C,hC,hbound⟩ := cubicThetaCoordinateEnergy_integral_bound hK hpos
  change cubicThetaCoordinateData hg hc hp∈closure (Set.range cubicThetaGlobalEnergyGraph)
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨f,hf,hfc,hfK,hv,hd⟩ := happrox δ hδ
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfp := hfK.trans hpos
  have hdK : tsupport (f-g)⊆K := (tsupport_sub f g).trans (union_subset hfK hgK)
  have hdp := hdK.trans hpos
  let F : cubicThetaSmoothTests :=
    ⟨cubicThetaPoincareSection (cubicThetaCoordinateSeed f hf.continuous hfc hfp),
      cubicThetaCoordinateSection_regular hf hfc hfp,cubicThetaPoincareSection_compact _⟩
  refine ⟨cubicThetaCoordinateData hf1 hfc hfp,⟨F,rfl⟩,?_⟩
  have hdb : ∀ y, ‖fderiv ℝ (f-g) y‖≤δ := by
    intro y
    rw [fderiv_sub (hf1.differentiable one_ne_zero y) (hg.differentiable one_ne_zero y)]
    exact hd y
  have hn : ‖cubicThetaCoordinateData hf1 hfc hfp-cubicThetaCoordinateData hg hc hp‖^2≤C*δ^2 := by
    rw [← cubicThetaCoordinateData_sub hf1 hg hfc hc hfp hp hdp,
      cubicThetaCoordinateData_norm_sq (hf1.sub hg) (hfc.sub hc) hK hpos hdK e he hKe]
    exact hbound (f-g) (hf1.sub hg) δ hδ.le hv hdb
  have heps : δ^2*(C+1)^2=ε^2 := by
    have h := div_mul_cancel₀ ε (show C+1≠0 by linarith)
    change δ*(C+1)=ε at h
    calc
      _ = (δ*(C+1))^2 := (mul_pow δ (C+1) 2).symm
      _ = _ := congrArg (fun x : ℝ => x^2) h
  have hstrict : C*δ^2<ε^2 := by
    rw [← heps,mul_comm (δ^2)]
    exact mul_lt_mul_of_pos_right (by nlinarith [sq_nonneg C]) (sq_pos_of_pos hδ)
  have hnorm : ‖cubicThetaCoordinateData hf1 hfc hfp-cubicThetaCoordinateData hg hc hp‖<ε := by
    nlinarith [_root_.norm_nonneg (cubicThetaCoordinateData hf1 hfc hfp-cubicThetaCoordinateData hg hc hp)]
  simpa only [dist_eq_norm,norm_sub_rev] using hnorm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite core cutoffs are norms of genuine compact smooth cubic
sections. Thus they supply actual local test sections, including at every
point of the compact core. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff Manifold MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCoreSeed_support (c : CubicThetaQuotient) :
    Function.support (cubicThetaCoreSeed c) ⊆
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)).source := by
  intro p hp
  change cubicThetaCoreProfile c p.val≠0 at hp
  have ht := cubicThetaCoreProfile_support_target c (subset_tsupport _ hp)
  change p.val∈cubicThetaPointInclusion.target ∧
    cubicThetaPointInclusion.symm p.val∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source at ht
  have hi : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  rw [hi] at ht
  exact ht.2

def cubicThetaCoreSection (c : CubicThetaQuotient) : cubicThetaSmoothTests :=
  ⟨cubicThetaPoincareSection (cubicThetaCoreSeed c),
    cubicThetaPoincareSection_contDiffOn _ (cubicThetaCoreSeed_contDiffOn c),
    cubicThetaPoincareSection_compact _⟩

lemma cubicThetaCoreSection_on_sheet (c : CubicThetaQuotient) {p : CubicThetaPoint}
    (hp : p∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source) :
    (cubicThetaCoreSection c).val.val p=cubicThetaCoreProfile c p.val :=
  cubicThetaPoincareSection_on_sheet _ _ (cubicThetaCoveringChart_coe _)
    (cubicThetaCoreSeed_support c) hp

lemma cubicThetaCoreSeed_eq_bump (c : CubicThetaQuotient) {p : CubicThetaPoint}
    (hp : p∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source) :
    cubicThetaCoreProfile c p.val=(cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ) := by
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  have hq : cubicThetaQuotientMap p∈(cubicThetaQuotientChart c).source := by
    refine ⟨?_,?_⟩
    · change cubicThetaQuotientMap p∈e.target
      rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
      exact e.map_source hp
    · rw [cubicThetaPointInclusion_source]
      trivial
  have hb := (cubicThetaCoreBump c).eqOn_source hq
  have he : cubicThetaQuotientChart c (cubicThetaQuotientMap p)=p.val := by
    change cubicThetaPointInclusion (e.symm (cubicThetaQuotientMap p))=p.val
    rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
    rw [e.left_inv hp]
    rfl
  simp only [extChartAt_coe,Function.comp_def,modelWithCornersSelf_coe,id_eq] at hb
  change cubicThetaCoreBump c (cubicThetaQuotientMap p)=
    (cubicThetaCoreBump c).toContDiffBump (cubicThetaQuotientChart c (cubicThetaQuotientMap p)) at hb
  rw [he] at hb
  exact congrArg (fun r : ℝ => (r:ℂ)) hb.symm

lemma cubicThetaCoreSection_norm (c q : CubicThetaQuotient) :
    cubicThetaSectionNorm (cubicThetaCoreSection c) q=cubicThetaCoreBump c q := by
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  by_cases hq : q∈e.target
  · let p := e.symm q
    have hp : p∈e.source := e.map_target hq
    have he : cubicThetaQuotientMap p=q := by
      rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
      exact e.right_inv hq
    rw [← he,cubicThetaSectionNorm_apply,cubicThetaCoreSection_on_sheet c hp,
      cubicThetaCoreSeed_eq_bump c hp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (cubicThetaCoreBump c).nonneg]
  · have hb : cubicThetaCoreBump c q=0 := by
      apply Function.notMem_support.mp
      intro h
      have hs := (cubicThetaCoreBump c).support_subset_source h
      exact hq hs.1
    rw [hb]
    unfold cubicThetaSectionNorm
    apply norm_eq_zero.mpr
    change (∑ᶠ g : cubicThetaPrincipalGroup,
      cubicThetaPoincareTerm (cubicThetaCoreSeed c) g (cubicThetaQuotientLift q))=0
    have hzero (g : cubicThetaPrincipalGroup) :
        cubicThetaPoincareTerm (cubicThetaCoreSeed c) g (cubicThetaQuotientLift q)=0 := by
      have hz : cubicThetaCoreSeed c (g • cubicThetaQuotientLift q)=0 := by
        by_contra hn
        have hp := cubicThetaCoreSeed_support c hn
        have he := e.map_source hp
        rw [cubicThetaCoveringChart_coe,cubicThetaQuotient_covering.map_smul,
          cubicThetaQuotientLift_map] at he
        exact hq he
      simp only [cubicThetaPoincareTerm,hz,mul_zero]
    simp only [hzero,finsum_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareLocalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A seed in one covering sheet periodizes to the corresponding
invariant cutoff of the original section, including its cubic multiplier. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoincare_localization_eq (ψ : C_c(CubicThetaPoint,ℂ))
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hψs : tsupport ψ⊆e.source) (F : CubicThetaSection) (b : C(CubicThetaQuotient,ℂ))
    (hb : Function.support b⊆e.target)
    (hψ : ∀ p∈e.source, ψ p=b (cubicThetaQuotientMap p)*F.val p) :
    cubicThetaPoincareSection ψ=cubicThetaSectionCutoff b F := by
  let T := cubicThetaPoincareSection ψ
  let G := cubicThetaSectionCutoff b F
  have hn (q : CubicThetaQuotient) : cubicThetaSectionNorm (T-G) q=0 := by
    by_cases hq : q∈e.target
    · let p := e.symm q
      have hp : p∈e.source := e.map_target hq
      have hqp : cubicThetaQuotientMap p=q := by rw [← he]; exact e.right_inv hq
      rw [← hqp,cubicThetaSectionNorm_apply]
      change ‖(cubicThetaPoincareSection ψ).val p-b (cubicThetaQuotientMap p)*F.val p‖=0
      rw [cubicThetaPoincareSection_on_sheet ψ e he (subset_tsupport ψ |>.trans hψs) hp,
        hψ p hp,sub_self,norm_zero]
    · have hout : q∉tsupport (cubicThetaSectionNorm T) := by
        intro h
        obtain ⟨p,hp,hpq⟩ := cubicThetaPoincareSection_norm_support ψ h
        have ht := e.map_source (hψs hp)
        rw [he,hpq] at ht
        exact hq ht
      have hz := image_eq_zero_of_notMem_tsupport hout
      have hb0 : b q=0 := Function.notMem_support.mp (fun h => hq (hb h))
      change ‖T.val (cubicThetaQuotientLift q)-
        b (cubicThetaQuotientMap (cubicThetaQuotientLift q))*F.val (cubicThetaQuotientLift q)‖=0
      rw [cubicThetaQuotientLift_map,hb0,zero_mul,sub_zero]
      exact hz
  ext p
  have h := hn (cubicThetaQuotientMap p)
  rw [cubicThetaSectionNorm_apply] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1Localization
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localize a C1 section by one actual arithmetic core profile.
The periodized result is its scalar bump cutoff and lies in the energy graph. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaC1Localization_regular {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiff ℝ 1 (cubicThetaTestLocalization φ F) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y.2
  · exact (hφ.contDiffOn.mul hF).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)
  · have hout : y∉tsupport (cubicThetaTestLocalization φ F) :=
      fun h => hy (hp (tsupport_mul_subset_left h))
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ × ℝ => (0:ℂ)) y).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

def cubicThetaC1CoreFunction (c : CubicThetaQuotient) (F : CubicThetaSection) (y : ℂ × ℝ) : ℂ :=
  cubicThetaCoreProfile c y*(cubicThetaCoreProfile c y*cubicThetaSectionFunction F y)

lemma cubicThetaC1CoreFunction_support (c : CubicThetaQuotient) (F : CubicThetaSection) :
    tsupport (cubicThetaC1CoreFunction c F)⊆tsupport (cubicThetaCoreProfile c) :=
  tsupport_mul_subset_left

lemma cubicThetaC1CoreFunction_compact (c : CubicThetaQuotient) (F : CubicThetaSection) :
    HasCompactSupport (cubicThetaC1CoreFunction c F) := (cubicThetaCoreProfile_compact c).mul_right

lemma cubicThetaC1CoreFunction_regular (c : CubicThetaQuotient) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiff ℝ 1 (cubicThetaC1CoreFunction c F) :=
  (cubicThetaCoreProfile_contDiff c).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mul
    (cubicThetaC1Localization_regular ((cubicThetaCoreProfile_contDiff c).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (cubicThetaCoreProfile_support_positive c) F hF)

def cubicThetaCoreSquare (c : CubicThetaQuotient) : C(CubicThetaQuotient,ℂ) :=
  ⟨fun q => (cubicThetaCoreBump c q:ℂ)^2,
    (Complex.continuous_ofReal.comp (cubicThetaCoreBump c).continuous).pow 2⟩

lemma cubicThetaC1CoreFunction_periodization (c : CubicThetaQuotient) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    let g := cubicThetaC1CoreFunction c F
    let hg := cubicThetaC1CoreFunction_regular c F hF
    let hc := cubicThetaC1CoreFunction_compact c F
    let hp := (cubicThetaC1CoreFunction_support c F).trans (cubicThetaCoreProfile_support_positive c)
    cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc hp)=
      cubicThetaSectionCutoff (cubicThetaCoreSquare c) F := by
  intro g hg hc hp
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  have hψs : tsupport (cubicThetaCoordinateSeed g hg.continuous hc hp)⊆e.source := by
    intro p hps
    obtain ⟨y,hy,rfl⟩ := cubicThetaCoordinateSeed_support g hg.continuous hc hp hps
    have ht := cubicThetaCoreProfile_support_target c (cubicThetaC1CoreFunction_support c F hy)
    exact ht.2
  have hb : Function.support (cubicThetaCoreSquare c)⊆e.target := by
    intro q hq
    have hb : cubicThetaCoreBump c q≠0 := by
      intro hz
      apply hq
      simp only [cubicThetaCoreSquare,ContinuousMap.coe_mk,hz,Complex.ofReal_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact ((cubicThetaCoreBump c).support_subset_source hb).1
  apply cubicThetaPoincare_localization_eq _ e (cubicThetaCoveringChart_coe _) hψs F (cubicThetaCoreSquare c) hb
  intro p hps
  change cubicThetaCoreProfile c p.val*(cubicThetaCoreProfile c p.val*cubicThetaSectionFunction F p.val)=_
  rw [cubicThetaCoreSeed_eq_bump c hps,cubicThetaSectionFunction_apply F p.property]
  change (cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)*
    ((cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)*F.val p)=_
  dsimp only [cubicThetaCoreSquare,ContinuousMap.coe_mk]
  ring

lemma cubicThetaC1CoreFunction_mem_energy (c : CubicThetaQuotient) (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaCoordinateData (cubicThetaC1CoreFunction_regular c F hF)
      (cubicThetaC1CoreFunction_compact c F)
      ((cubicThetaC1CoreFunction_support c F).trans (cubicThetaCoreProfile_support_positive c))∈
      cubicThetaGlobalEnergySpace := by
  apply cubicThetaCoordinateData_mem_energy _ _ _ (cubicThetaCoveringChart (cubicThetaQuotientLift c))
    (cubicThetaCoveringChart_coe _)
  rintro p ⟨y,hy,rfl⟩
  exact (cubicThetaCoreProfile_support_target c (cubicThetaC1CoreFunction_support c F hy)).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite sum of squared genuine core bumps is smooth upstairs
and bounded below by one on the arithmetic compact core. -/
noncomputable section
open Set
open scoped ContDiff BigOperators MatrixGroups
namespace CubicFirstMoment

def cubicThetaCoreDenominator (A : Finset CubicThetaQuotient) (q : CubicThetaQuotient) : ℝ :=
  ∑ c∈A, (cubicThetaCoreBump c q)^2

def cubicThetaCoreDenominatorFunction (A : Finset CubicThetaQuotient) (y : ℂ × ℝ) : ℝ :=
  ∑ c∈A, ((cubicThetaSectionFunction (cubicThetaCoreSection c) y).re^2+
    (cubicThetaSectionFunction (cubicThetaCoreSection c) y).im^2)

lemma cubicThetaCoreDenominator_continuous (A : Finset CubicThetaQuotient) :
    Continuous (cubicThetaCoreDenominator A) := by
  apply continuous_finsetSum
  intro c hc
  exact (cubicThetaCoreBump c).continuous.pow 2

lemma cubicThetaCoreDenominatorFunction_contDiff (A : Finset CubicThetaQuotient) :
    ContDiffOn ℝ ∞ (cubicThetaCoreDenominatorFunction A) {y : ℂ × ℝ | 0<y.2} := by
  apply ContDiffOn.sum
  intro c hc
  have h := (cubicThetaCoreSection c).property.1
  exact (Complex.reCLM.contDiff.comp_contDiffOn h).pow 2 |>.add
    ((Complex.imCLM.contDiff.comp_contDiffOn h).pow 2)

lemma cubicThetaCoreDenominatorFunction_apply (A : Finset CubicThetaQuotient) (p : CubicThetaPoint) :
    cubicThetaCoreDenominatorFunction A p.val=cubicThetaCoreDenominator A (cubicThetaQuotientMap p) := by
  apply Finset.sum_congr rfl
  intro c hc
  rw [cubicThetaSectionFunction_apply _ p.property]
  have he := cubicThetaSectionNorm_apply (cubicThetaCoreSection c) p
  rw [cubicThetaCoreSection_norm] at he
  change ((cubicThetaCoreSection c).val.val p).re^2+
    ((cubicThetaCoreSection c).val.val p).im^2=(cubicThetaCoreBump c (cubicThetaQuotientMap p))^2
  rw [he,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,pow_two]

lemma cubicThetaCoreDenominator_covers (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      1 ≤ cubicThetaCoreDenominator A q := cubicThetaCoreBump_sum_sq S V

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreDivision
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite core reconstruction after division by the positive
sum of squared core bumps. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCoreDenominator_pullback (A : Finset CubicThetaQuotient) :
    ContDiffOn ℝ 1 (fun y => cubicThetaCoreDenominator A
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} := by
  apply ((cubicThetaCoreDenominatorFunction_contDiff A).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).congr
  intro y hy
  have he := cubicThetaCoreDenominatorFunction_apply A (cubicThetaPointInclusion.symm y)
  have hi : (cubicThetaPointInclusion.symm y).val=y :=
    cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target])
  rw [hi] at he
  exact he.symm

lemma cubicThetaCoreDivision_reconstruction (A : Finset CubicThetaQuotient) (F : CubicThetaSection)
    (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), cubicThetaCoreDenominator A q≠0) :
    let H := cubicThetaSectionDivide F (cubicThetaCoreDenominator A)
      (cubicThetaCoreDenominator_continuous A) hn
    (∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H)=F := by
  intro H
  ext p
  simp only [AddSubmonoidClass.coe_finsetSum,ContinuousMap.sum_apply]
  change (∑ c∈A, (cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)^2*
    (F.val p/(cubicThetaCoreDenominator A (cubicThetaQuotientMap p):ℂ)))=F.val p
  rw [← Finset.sum_mul]
  have hs : (∑ c∈A, (cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)^2)=
      (cubicThetaCoreDenominator A (cubicThetaQuotientMap p):ℂ) := by
    simp only [cubicThetaCoreDenominator,Complex.ofReal_sum,Complex.ofReal_pow]
  rw [hs]
  by_cases hf : F.val p=0
  · simp only [hf,zero_div,mul_zero]
  · have hq : cubicThetaQuotientMap p∈tsupport (cubicThetaSectionNorm F) := by
      apply subset_tsupport
      rw [Function.mem_support,cubicThetaSectionNorm_apply]
      exact norm_ne_zero_iff.mpr hf
    have hd : (cubicThetaCoreDenominator A (cubicThetaQuotientMap p):ℂ)≠0 := by
      exact_mod_cast hn _ hq
    field_simp [hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactC1Energy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every compact C1 automorphic section belongs to the actual closed
energy graph, by finite reconstruction from smoothed coordinate pieces. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaCompactC1_mem_energy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaC1EnergyData F hF hc∈cubicThetaGlobalEnergySpace := by
  obtain ⟨S,V,hSV⟩ := cubicThetaCompact_subset_core hc
  obtain ⟨A,hA⟩ := cubicThetaCoreDenominator_covers S V
  have hn : ∀ q∈tsupport (cubicThetaSectionNorm F), cubicThetaCoreDenominator A q≠0 := by
    intro q hq
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hA q (hSV hq)))
  let D := cubicThetaCoreDenominator A
  let H := cubicThetaSectionDivide F D (cubicThetaCoreDenominator_continuous A) hn
  have hH : ContDiffOn ℝ 1 (cubicThetaSectionFunction H) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaSectionDivide_regular F hF D (cubicThetaCoreDenominator_continuous A) hn
      (cubicThetaCoreDenominator_pullback A)
  let P := fun c : CubicThetaQuotient => cubicThetaPoincareSection
    (cubicThetaCoordinateSeed (cubicThetaC1CoreFunction c H)
      (cubicThetaC1CoreFunction_regular c H hH).continuous
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c)))
  have hP (c : CubicThetaQuotient) :
      ContDiffOn ℝ 1 (cubicThetaSectionFunction (P c)) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaCoordinateSection_regular (cubicThetaC1CoreFunction_regular c H hH)
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c))
  have hcP (c : CubicThetaQuotient) : HasCompactSupport (cubicThetaSectionNorm (P c)) :=
    cubicThetaPoincareSection_compact _
  have hmP (c : CubicThetaQuotient) : cubicThetaC1EnergyData (P c) (hP c) (hcP c)∈
      cubicThetaGlobalEnergySpace := cubicThetaC1CoreFunction_mem_energy c H hH
  have hsum : (∑ c∈A, P c)=F := by
    calc
      _ = ∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H := by
        apply Finset.sum_congr rfl
        intro c hcA
        exact cubicThetaC1CoreFunction_periodization c H hH
      _ = F := cubicThetaCoreDivision_reconstruction A F hn
  have hm : cubicThetaC1EnergyData (∑ c∈A, P c) (cubicThetaC1Section_sum A P hP)
      (cubicThetaCompactSection_sum A P hcP)∈cubicThetaGlobalEnergySpace := by
    rw [cubicThetaC1EnergyData_sum A P hP hcP]
    exact Submodule.sum_mem _ (fun c hcA => hmP c)
  have he : cubicThetaC1EnergyData (∑ c∈A, P c) (cubicThetaC1Section_sum A P hP)
      (cubicThetaCompactSection_sum A P hcP)=cubicThetaC1EnergyData F hF hc := by
    congr 1
  exact he ▸ hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaled scalar cusp cutoffs descend to the actual quotient in
every arithmetic cusp, using normality of the principal group. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaScalarCuspAt_invariant (δ : SL(2,Eisenstein)) (N : ℝ)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaScalarCuspAt δ N (g • p)=cubicThetaScalarCuspAt δ N p := by
  have he : δ⁻¹ • (g • p)=cubicThetaPrincipalConjugate δ g • (δ⁻¹ • p) := by
    change δ⁻¹ • (g.val • p)=(δ⁻¹*g.val*δ) • (δ⁻¹ • p)
    simp only [mul_smul,smul_inv_smul]
  unfold cubicThetaScalarCuspAt
  rw [he]
  exact cubicThetaScalarCusp_invariant N (cubicThetaPrincipalConjugate δ g) (δ⁻¹ • p).property

def cubicThetaScalarCuspQuotient (δ : SL(2,Eisenstein)) (N : ℝ) (q : CubicThetaQuotient) : ℂ :=
  cubicThetaScalarCuspAt δ N (cubicThetaQuotientLift q)

lemma cubicThetaScalarCuspQuotient_apply (δ : SL(2,Eisenstein)) (N : ℝ) (p : CubicThetaPoint) :
    cubicThetaScalarCuspQuotient δ N (cubicThetaQuotientMap p)=cubicThetaScalarCuspAt δ N p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaScalarCuspQuotient
  rw [← hg,cubicThetaScalarCuspAt_invariant]

lemma cubicThetaScalarCuspQuotient_continuous (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N) :
    Continuous (cubicThetaScalarCuspQuotient δ N) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaScalarCuspQuotient δ N ∘ cubicThetaQuotientMap=cubicThetaScalarCuspAt δ N :=
    funext (cubicThetaScalarCuspQuotient_apply δ N)
  rw [he]
  have hc : Continuous (fun p : CubicThetaPoint => cubicThetaScalarCusp N p.val) :=
    (cubicThetaScalarCusp_smooth hN).continuousOn.comp_continuous continuous_subtype_val
      (fun p => p.property)
  exact hc.comp (continuous_const_smul δ⁻¹)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCuspCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite disjoint cusp cover gives smooth compact cutoffs on the
actual quotient by subtracting its scalar incoming cusp cutoffs. -/
noncomputable section
open Set
open scoped MatrixGroups ContDiff BigOperators
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_mono (δ : SL(2,Eisenstein)) {H K : ℝ} (h : H≤K) :
    cubicThetaCuspNeighborhood δ K⊆cubicThetaCuspNeighborhood δ H := by
  intro q hq
  obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ K q).mp hq
  exact (cubicThetaCuspNeighborhood_mem_iff δ H q).mpr ⟨p,h.trans_lt hp,hpq⟩

def cubicThetaCompactCuspCutoff (T : Finset SL(2,Eisenstein)) (N : ℝ)
    (q : CubicThetaQuotient) : ℂ :=
  1-∑ δ∈T,cubicThetaScalarCuspQuotient δ N q

lemma cubicThetaCompactCuspCutoff_continuous (T : Finset SL(2,Eisenstein))
    {N : ℝ} (hN : 1≤N) : Continuous (cubicThetaCompactCuspCutoff T N) :=
  continuous_const.sub (continuous_finsetSum T (fun δ _ => cubicThetaScalarCuspQuotient_continuous δ hN))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspExhaustion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite cusp family gives an explicit smooth exhaustion
which is eventually identically one in each quotient neighborhood. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaCuspExhaustion (T : Finset SL(2,Eisenstein)) (n : ℕ) : C(CubicThetaQuotient,ℂ) :=
  ⟨cubicThetaCompactCuspCutoff T ((n:ℝ)+2),
    cubicThetaCompactCuspCutoff_continuous T (by linarith [Nat.cast_nonneg (α:=ℝ) n])⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergySections
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual C1 sections of finite value and gradient energy form a
complex vector space. This retains their literal pointwise functions. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaFiniteEnergySections : Submodule ℂ CubicThetaSection where
  carrier := {F | ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2} ∧
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure ∧
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure}
  zero_mem' := ⟨(0 : cubicThetaSmoothTests).property.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    cubicThetaSectionRepresentative_memLp (0 : cubicThetaSmoothTests),
    cubicThetaGradientRepresentative_memLp (0 : cubicThetaSmoothTests)⟩
  add_mem' := by
    intro F G hF hG
    refine ⟨hF.1.add hG.1,hF.2.1.add hG.2.1,?_⟩
    have he : cubicThetaGradientRepresentative (F+G)=
        cubicThetaGradientRepresentative F+cubicThetaGradientRepresentative G := by
      funext q
      exact cubicThetaC1Gradient_add F G hF.1 hG.1 _
    rw [he]
    exact hF.2.2.add hG.2.2
  smul_mem' := by
    intro c F hF
    refine ⟨hF.1.const_smul c,hF.2.1.const_smul c,?_⟩
    have he : cubicThetaGradientRepresentative (c • F)=c • cubicThetaGradientRepresentative F := by
      funext q
      exact cubicThetaC1Gradient_smul c F hF.1 _
    rw [he]
    exact hF.2.2.const_smul c

def cubicThetaFiniteEnergyValue : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun F := F.property.2.1.toLp _
  map_add' F G := MemLp.toLp_add F.property.2.1 G.property.2.1
  map_smul' c F := MemLp.toLp_const_smul c F.property.2.1

def cubicThetaFiniteEnergyGradient : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaGradientL2 where
  toFun F := F.property.2.2.toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(F+G).property.2.2.coeFn_toLp,F.property.2.2.coeFn_toLp,
      G.property.2.2.coeFn_toLp,Lp.coeFn_add (F.property.2.2.toLp _) (G.property.2.2.toLp _)]
      with q hFG hF hG ha
    simp only [Pi.add_apply] at ha
    rw [hFG,ha,hF,hG]
    exact cubicThetaC1Gradient_add F G F.property.1 G.property.1 _
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(c • F).property.2.2.coeFn_toLp,F.property.2.2.coeFn_toLp,
      Lp.coeFn_smul c (F.property.2.2.toLp _)] with q hCF hF ha
    simp only [Pi.smul_apply,RingHom.id_apply] at ha ⊢
    rw [hCF,ha,hF]
    exact cubicThetaC1Gradient_smul c F F.property.1 _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction of actual finite-energy sections to the injective
height-two cusp strip is bounded in L2 by the global value norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteEnergy_norm_integrable (F : cubicThetaFiniteEnergySections) :
    Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
  simpa only [cubicThetaSectionRepresentative_norm] using
    F.property.2.1.integrable_norm_pow (by norm_num)

lemma cubicThetaFiniteEnergy_strip_memLp (F : cubicThetaFiniteEnergySections) :
    MemLp (fun p : CubicThetaPoint => F.val.val p) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  apply (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mpr
  have h := (cubicThetaFiniteEnergy_norm_integrable F).integrableOn
    (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip 2)
  unfold IntegrableOn at h
  rw [← cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num))] at h
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using hi

def cubicThetaFiniteCuspRestriction : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaStripL2 where
  toFun F := (cubicThetaFiniteEnergy_strip_memLp F).toLp _
  map_add' F G := MemLp.toLp_add (cubicThetaFiniteEnergy_strip_memLp F) (cubicThetaFiniteEnergy_strip_memLp G)
  map_smul' c F := MemLp.toLp_const_smul c (cubicThetaFiniteEnergy_strip_memLp F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual forcing is supported in one compact arithmetic core,
uniformly in the spectral parameter, and defines a compact smooth section. -/
noncomputable section
open Set
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaForcingSeries_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (s : ℂ) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 2 →
        cubicThetaForcingSeries p.val s=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspTransition_core
  refine ⟨S,fun s p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaForcingTerm r p.val s=0 by
    simp only [cubicThetaForcingSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val<1 ∨ 2 < r.height p.val
  · exact mul_eq_zero_of_right _ (cubicThetaIncomingForcing_zero s hh)
  · have hlo : 1 ≤ r.height p.val := le_of_not_gt (fun h => hh (Or.inl h))
    have hup : r.height p.val≤2 := le_of_not_gt (fun h => hh (Or.inr h))
    have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
      change (cubicThetaBottomRow r.completion).height p.val=_
      rw [r.completion_row]
    have hq := hS 1 (r.completion • p) (by rwa [he]) (by rwa [he])
    rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
    exact False.elim (hp hq)

def cubicThetaForcingSection (s : ℂ) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaForcingSeries p.val s,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaForcingSeries_contDiffOn s).contDiffAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.continuousAt.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaForcingSeries_automorphy g p.property s⟩

lemma cubicThetaForcingSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaForcingSection s)) := by
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_core
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S 2)
  intro q hq
  by_contra h
  have hz := hS s (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaForcingSeries (cubicThetaQuotientLift q).val s‖=0
  rw [hz,norm_zero]

def cubicThetaForcingTest (s : ℂ) : cubicThetaSmoothTests :=
  ⟨cubicThetaForcingSection s,by
    refine ⟨?_,cubicThetaForcingSection_compact s⟩
    apply (cubicThetaForcingSeries_contDiffOn s).congr
    intro y hy
    change cubicThetaForcingSeries (cubicThetaPointInclusion.symm y).val s=
      cubicThetaForcingSeries y s
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaForcingSeries p s) he
  ⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact forcing is an entire global L2-valued family,
via the bounded transport from its fixed radial profile space. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaForcingL2 (s : ℂ) : CubicThetaGlobalL2 :=
  cubicThetaGlobalMass (cubicThetaForcingTest s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexLocalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact chart inclusion also respects the complex scalar action.
The extension is identified on the dense genuine smooth sections. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

local instance complexLocalization_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactEnergyCorrection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact corrections of the actual energy inclusion. The exterior
inequality gives a numerical-range bound with arbitrary coefficient
strictly larger than one half. -/
noncomputable section
open scoped MatrixGroups InnerProduct
namespace CubicFirstMoment

def cubicThetaEnergyMass : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaGlobalInclusion.adjoint.comp cubicThetaGlobalInclusion

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyPencilKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact correction makes every real exceptional energy space
below the threshold finite dimensional. The proof uses the actual
compact core operators, not a spectral finiteness assumption. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaEnergyPencil (z : ℂ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  1-z • cubicThetaEnergyMass

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExceptionalProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite exceptional eigenspace has an actual orthogonal
projection. Adding it to the self-adjoint real pencil removes its kernel. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

instance cubicThetaEnergyPencil_ker_complete (z : ℂ) :
    CompleteSpace (cubicThetaEnergyPencil z).ker :=
  (cubicThetaEnergyPencil z).isClosed_ker.isComplete.completeSpace_coe

def cubicThetaExceptionalProjection (z : ℂ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  (cubicThetaEnergyPencil z).ker.starProjection

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residue of the actual arithmetic continuation is an explicit
finite-dimensional spectral projection of its incoming forcing. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

def cubicThetaArithmeticResidueEnergy (σ : ℝ) : cubicThetaGlobalEnergySpace :=
  (cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
    cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ))
      (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaStripFiniteVolume
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual height-two cusp strip has finite hyperbolic volume.
The proof keeps the horizontal cell and v^-3 density explicit. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCuspStrip_constant_integrable :
    IntegrableOn (fun _ : CubicThetaPoint => (1:ℝ)) (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hh : IntegrableOn (fun _ : ℂ => (1:ℝ)) cubicThetaHorizontalCell :=
    integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(-3:ℝ)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  have hd : IntegrableOn (fun y : ℂ × ℝ => (1:ℝ)/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
    have he (v : ℝ) : v^(-3:ℝ)=(v^3)⁻¹ := by
      rw [show (-3:ℝ)=((-3:ℤ):ℝ) by norm_num,Real.rpow_intCast]
      simp only [zpow_neg]
      rfl
    change Integrable (fun y : ℂ × ℝ => (1:ℝ)/y.2^3)
      (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _)
    simpa only [one_mul,he,one_div] using hm
  apply (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)
    (fun _ => (1:ℝ))).mpr
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)]
  exact hd

instance cubicThetaStrip_finiteMeasure :
    IsFiniteMeasure (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ)≠0)).mp
    cubicThetaCuspStrip_constant_integrable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine weighted Fourier observations on the high arithmetic cusp.
They are bounded L2 functionals of the actual meromorphic continuation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCuspFourierWeight_memLp (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    MemLp (cubicThetaCuspFourierWeight h W) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  apply MemLp.of_bound (cubicThetaCuspFourierWeight_continuous h W).aestronglyMeasurable (max C 0)
  apply Filter.Eventually.of_forall
  intro p
  rw [cubicThetaCuspFourierWeight,norm_mul,Circle.norm_coe,mul_one]
  by_cases hp : p.val.2∈tsupport W
  · exact (hC p.val.2 hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp,norm_zero]
    exact le_max_right _ _

def cubicThetaCuspFourierTest (h : Eisenstein) (W : C_c(ℝ,ℂ)) : CubicThetaStripL2 :=
  (cubicThetaCuspFourierWeight_memLp h W).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeMassOperator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same cubed-prime correspondence on the actual automorphic mass
space. It agrees with the energy operator and is self-adjoint there. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeMass_finiteGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable cubic-root sections on the actual finite domain.
The finite translation action has exactly the original L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootFiniteSections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeCubeRootSections p) where
  carrier := {F | MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))}
  zero_mem' := MemLp.zero
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphicL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completion of the actual finite-mass sections on the root cover.
Its fractional translations extend isometrically to this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance cubeRootFiniteSections_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeCubeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded restriction from the actual completed cubic-root automorphic
space to the high cusp strip. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

local instance cubeRootCuspFinite_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeCubeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeRootLift_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationL2
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric cubic dilation of the actual global mass space
into the common arithmetic root cover. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeRootDilation_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric opposite-root action on the actual cubic-scale completion. -/
noncomputable section
namespace CubicFirstMoment

local instance cubeRootWeyl_finiteGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeCubeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the genuine primary-level theta transformation on a symmetric
height scale, before Mellin integration. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaLevelScale (q : Eisenstein) : ℝ := (Real.sqrt (norm q))⁻¹

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularFunctionalEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The functional equation for the actual continued additive angular Dirichlet series.
Gamma cancellation is required only on the dual side. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAngularUncompletion (q : Eisenstein) (k : ℕ) (s : ℂ) : ℂ :=
  4*(cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*
    (Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹

end CubicFirstMoment

end

end OAI
end


