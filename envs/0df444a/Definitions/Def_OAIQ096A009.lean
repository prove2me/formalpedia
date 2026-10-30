-- Prove2me | Definitions.Def_OAIQ096A009
-- name    : OAIQ096A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:37:16.03312+00:00
-- url     : https://prove2.me/theorems/710555c4-7827-493b-b5cf-d1b81fdc0a7b
-- title:
--   Definitions bundle OAIQ096A009 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 277 declarations of OpenAI's Lean: 73 definitions, 3 instances and 201 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaHighWindowSeries`, `OAI.CubicFirstMoment.cubicThetaHighWindowTerm`, `OAI.CubicFirstMoment.cubicThetaHorizontalCharacter`, `OAI.CubicFirstMoment.cubicThetaHorizontalFraction`, `OAI.CubicFirstMoment.cubicThetaHorizontalLatticeEquiv`, `OAI.CubicFirstMoment.cubicThetaHorizontalPeriodization`, `OAI.CubicFirstMoment.cubicThetaIdealDensity`, `OAI.CubicFirstMoment.cubicThetaIdealTotient`, `OAI.CubicFirstMoment.cubicThetaInvertedAdmissible`, `OAI.CubicFirstMoment.cubicThetaInvertedConstantDirichlet`, `OAI.CubicFirstMoment.cubicThetaInvertedConstantGauss`, `OAI.CubicFirstMoment.cubicThetaInvertedConstantMode`, `OAI.CubicFirstMoment.cubicThetaInvertedConstantWeight`, `OAI.CubicFirstMoment.cubicThetaInvertedFrequencyTerm`, `OAI.CubicFirstMoment.cubicThetaInvertedGaussCoefficient`, `OAI.CubicFirstMoment.cubicThetaInvertedGaussianRow`, `OAI.CubicFirstMoment.cubicThetaInvertedGridTerm`, `OAI.CubicFirstMoment.cubicThetaInvertedPairEquiv`, `OAI.CubicFirstMoment.cubicThetaInvertedRowEquiv`, `OAI.CubicFirstMoment.cubicThetaInvertedRowFourierCoefficient`, `OAI.CubicFirstMoment.cubicThetaInvertedRowSeries`, `OAI.CubicFirstMoment.cubicThetaLocalPrimePowerGauss`, `OAI.CubicFirstMoment.cubicThetaNormInverse`, `OAI.CubicFirstMoment.cubicThetaPeriodCell`, `OAI.CubicFirstMoment.cubicThetaPointC1Pullback`, `OAI.CubicFirstMoment.cubicThetaPoleRadialWeightIntegral`, `OAI.CubicFirstMoment.cubicThetaPrimeCharacterKernel`, `OAI.CubicFirstMoment.cubicThetaPrimeCriticalScale`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeBottomFunctionSum`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeBranchPoint`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeFiniteGauss`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeFirstPeriodization`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeFirstTerm`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeFunctionOperator`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeNineUnit`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeNonunitPart`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeReducedMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeReducedScale`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeReduction`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeReductionRow` and 33 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_PrimaryNormalization`, `CubicMoment_Estimates_IdealDivisorPower`, `CubicMoment_Estimates_IdealMoebiusBounds`, `CubicMoment_Estimates_PrimitiveResidueConductorKernel`, `CubicMoment_Estimates_PrimitiveResidueFourier`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Estimates_ShortMoebiusPolynomials`, `CubicMoment_Theta_CubicThetaAxisLineDerivative`, `CubicMoment_Theta_CubicThetaComplexDensity`, `CubicMoment_Theta_CubicThetaComplexIntegrability`, `CubicMoment_Theta_CubicThetaComplexPointMeasure`, `CubicMoment_Theta_CubicThetaConstantDirichlet`, `CubicMoment_Theta_CubicThetaCoordinateIntegrationByParts`, `CubicMoment_Theta_CubicThetaCubeConstant`, `CubicMoment_Theta_CubicThetaCubeCoordinates`, `CubicMoment_Theta_CubicThetaCubeRowWeight`, `CubicMoment_Theta_CubicThetaDensityLocal`, `CubicMoment_Theta_CubicThetaFiniteConductor`, `CubicMoment_Theta_CubicThetaFiniteCover`, `CubicMoment_Theta_CubicThetaFiniteCoverIntegral`, `CubicMoment_Theta_CubicThetaFiniteFourierParseval`, `CubicMoment_Theta_CubicThetaFiniteInflation`, `CubicMoment_Theta_CubicThetaFourierCRT`, `CubicMoment_Theta_CubicThetaHighWindowSeries`, `CubicMoment_Theta_CubicThetaHorizontalAffine`, `CubicMoment_Theta_CubicThetaHorizontalFourierCharacter`, `CubicMoment_Theta_CubicThetaHorizontalFourierIntegrability`, `CubicMoment_Theta_CubicThetaHorizontalFourierTranslation`, `CubicMoment_Theta_CubicThetaHorizontalFourierVanishing`, `CubicMoment_Theta_CubicThetaHorizontalLattice`, `CubicMoment_Theta_CubicThetaHorizontalPeriodization`, `CubicMoment_Theta_CubicThetaHorizontalSection`, `CubicMoment_Theta_CubicThetaInvertedDirichlet`, `CubicMoment_Theta_CubicThetaInvertedFiniteFourier`, `CubicMoment_Theta_CubicThetaInvertedFourier`, `CubicMoment_Theta_CubicThetaInvertedFrequencyBounds`, `CubicMoment_Theta_CubicThetaInvertedGaussian`, `CubicMoment_Theta_CubicThetaInvertedRowFourier`, `CubicMoment_Theta_CubicThetaInvertedRowMellin`, `CubicMoment_Theta_CubicThetaInvertedRows`, `CubicMoment_Theta_CubicThetaInvertedUnfold`, `CubicMoment_Theta_CubicThetaPointC1`, `CubicMoment_Theta_CubicThetaPointC1Pairing`, `CubicMoment_Theta_CubicThetaPoleRadialScaling`, `CubicMoment_Theta_CubicThetaPrimaryConstant`, `CubicMoment_Theta_CubicThetaPrimaryFourierTwist`, `CubicMoment_Theta_CubicThetaPrimaryResidueNine`, `CubicMoment_Theta_CubicThetaPrimeAtkinConjugation`, `CubicMoment_Theta_CubicThetaPrimeCriticalFactors`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkinIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkinPairing`, `CubicMoment_Theta_CubicThetaPrimeCubeBottomMean`, `CubicMoment_Theta_CubicThetaPrimeCubeBranchCoordinates`, `CubicMoment_Theta_CubicThetaPrimeCubeBranchPeriodicity`, `CubicMoment_Theta_CubicThetaPrimeCubeChartCover`, `CubicMoment_Theta_CubicThetaPrimeCubeCosets`, `CubicMoment_Theta_CubicThetaPrimeCubeDegree`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstBranchMean`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstCoefficient`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodMean`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodization`, `CubicMoment_Theta_CubicThetaPrimeCubeFourierKernel`, `CubicMoment_Theta_CubicThetaPrimeCubeFourierOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeGauss`, `CubicMoment_Theta_CubicThetaPrimeCubeHeightMultiplier`, `CubicMoment_Theta_CubicThetaPrimeCubeHorizontalContinuity`, `CubicMoment_Theta_CubicThetaPrimeCubeHorizontalMean`, `CubicMoment_Theta_CubicThetaPrimeCubeLowerValue`, `CubicMoment_Theta_CubicThetaPrimeCubeOppositeBranch`, `CubicMoment_Theta_CubicThetaPrimeCubeRadialPairing`, `CubicMoment_Theta_CubicThetaPrimeCubeRadialResidue`, `CubicMoment_Theta_CubicThetaPrimeCubeReductionPhase`, `CubicMoment_Theta_CubicThetaPrimeCubeReductionResidue`, `CubicMoment_Theta_CubicThetaPrimeCubeReductionRow`, `CubicMoment_Theta_CubicThetaPrimeCubeResidueComplement`, `CubicMoment_Theta_CubicThetaPrimeCubeResidueStep`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphism`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhat`, `CubicMoment_Theta_CubicThetaPrimeCubeRootMatrix`, `CubicMoment_Theta_CubicThetaPrimeCubeRootTranslation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeyl`, `CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchCoordinates`, `CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchMean`, `CubicMoment_Theta_CubicThetaPrimeCubeSections`, `CubicMoment_Theta_CubicThetaPrimeCubeTrace`, `CubicMoment_Theta_CubicThetaPrimeCubeTransversal`, `CubicMoment_Theta_CubicThetaPrimeCubeTriangular`, `CubicMoment_Theta_CubicThetaPrimeCubeTriangularCoordinates`, `CubicMoment_Theta_CubicThetaPrimeCubeUnitMean`, `CubicMoment_Theta_CubicThetaPrimeCubeUnitPermutation`, `CubicMoment_Theta_CubicThetaPrimeCubeUpperChart`, `CubicMoment_Theta_CubicThetaPrimeCubeValuationSum`, `CubicMoment_Theta_CubicThetaPrimeCubeZeroMode`, `CubicMoment_Theta_CubicThetaPrimeDeterminant`, `CubicMoment_Theta_CubicThetaPrimeDilationCoordinates`, `CubicMoment_Theta_CubicThetaPrimeEulerStep`, `CubicMoment_Theta_CubicThetaPrimeFourier`, `CubicMoment_Theta_CubicThetaPrimeIwahori`, `CubicMoment_Theta_CubicThetaPrimeLocalCases`, `CubicMoment_Theta_CubicThetaPrimePowerFourier`, `CubicMoment_Theta_CubicThetaPrimeRootSubgroup`, `CubicMoment_Theta_CubicThetaPrimeShiftRows`, `CubicMoment_Theta_CubicThetaRadialProfileEquation`, `CubicMoment_Theta_CubicThetaRadialProfileSeries`, `CubicMoment_Theta_CubicThetaRadialProfileSmooth`, `CubicMoment_Theta_CubicThetaRamifiedLowFactor`, `CubicMoment_Theta_CubicThetaRamifiedMissingClass`, `CubicMoment_Theta_CubicThetaRamifiedPhaseRows`, `CubicMoment_Theta_CubicThetaRamifiedTrace`, `CubicMoment_Theta_CubicThetaResidueCount`, `CubicMoment_Theta_CubicThetaResidueWhittaker`, `CubicMoment_Theta_CubicThetaRowFiniteFourier`, `CubicMoment_Theta_CubicThetaRowFourier`, `CubicMoment_Theta_CubicThetaRowFrequencyScaling`, `CubicMoment_Theta_CubicThetaRowGaussBounds`, `CubicMoment_Theta_CubicThetaTorusModes`, `CubicMoment_Theta_CubicThetaTotientConvolution`, `CubicMoment_Theta_CubicThetaTotientEuler`, `CubicMoment_Theta_CubicThetaTotientSeries`, `CubicMoment_Theta_CubicThetaUnitCount`, `CubicMoment_Theta_CubicThetaUnitLifting`, `CubicMoment_Theta_CubicThetaWeightedTest`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A004`, `OAIQ096A005` and `OAIQ096A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A012`, `OAIQ096A013`, `OAIQ096A014` and `OAIQ096A015`; the statements `OAI_CubicFirstMoment_LogarithmicWeightFamily_radial_model_low_power`, `OAI_CubicFirstMoment_ProfileControl_large_common_nonzero_power`, `OAI_CubicFirstMoment_ProfileControl_smallB_nonzero_variance_height_power`, `OAI_CubicFirstMoment_angular_distinguishedStoppedDyad_early_bound_actual`, `OAI_CubicFirstMoment_angular_distinguishedStoppedLate_bound`, `OAI_CubicFirstMoment_angular_largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_flat_high_bound`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI_CubicFirstMoment_angular_large_core_block_moment`, `OAI_CubicFirstMoment_angular_scaleFirstMiddleSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_scaleFirstOrdinaryLowTail_two_stage`, `OAI_CubicFirstMoment_angular_scaleFirstOrdinaryStoppedTail_isLittleO`, `OAI_CubicFirstMoment_angular_scaleFirstTailNoStopRow_finite_bound_proved`, `OAI_CubicFirstMoment_angular_stopped_norm_mellin_integral`, `OAI_CubicFirstMoment_angular_stopped_product_transfer`, `OAI_CubicFirstMoment_angular_stopped_reflected_arithmetic_mellin_integral`, `OAI_CubicFirstMoment_angular_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_angular_tailPrime_ordinary_tuple_bound`, `OAI_CubicFirstMoment_angular_typeI_low_proved`, `OAI_CubicFirstMoment_angular_upperLowTail_isLittleO_uniform_proved`, `OAI_CubicFirstMoment_angular_upperLowTail_stopping`, `OAI_CubicFirstMoment_angular_upperTailNoStopRow_finite_bound_proved`, `OAI_CubicFirstMoment_largePrimeTuplePiece_flat_high_bound`, `OAI_CubicFirstMoment_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI_CubicFirstMoment_largePrimeTuplePiece_ordinary_range`, `OAI_CubicFirstMoment_ordinary_sparse_centered_bilinear`, `OAI_CubicFirstMoment_primeGroupTail_common_row_height_power`, `OAI_CubicFirstMoment_primeGroupTail_core_block_sieve`, `OAI_CubicFirstMoment_rough_prime_corrected_bilinear_actual`, `OAI_CubicFirstMoment_smallB_core_block_sieve`, `OAI_CubicFirstMoment_stopped_norm_mellin_integral`, `OAI_CubicFirstMoment_stopped_product_bilinear_log_saving_actual` and `OAI_CubicFirstMoment_stopped_product_transfer`; the proofs of `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_large_power`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_small_power`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_smooth_bilinear_all_lengths`, `OAI_CubicFirstMoment_angular_height_all_frequency_cutoff_mass`, `OAI_CubicFirstMoment_angular_large_core_block_moment`, `OAI_CubicFirstMoment_angular_low_noncube_mass`, `OAI_CubicFirstMoment_angular_scaleFirstOrdinaryLowTail_two_stage`, `OAI_CubicFirstMoment_angular_scaleFirstTailNoStopRow_finite_bound_proved`, `OAI_CubicFirstMoment_angular_stoppedBeta_long_bins_log_saving`, `OAI_CubicFirstMoment_angular_stopped_distinguished_full_saving`, `OAI_CubicFirstMoment_angular_stopped_noncube_core_blocks`, `OAI_CubicFirstMoment_angular_stopped_product_transfer`, `OAI_CubicFirstMoment_angular_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_angular_stopped_selected_prime_row_saving`, `OAI_CubicFirstMoment_angular_stopped_twisted_cutoff_tail`, `OAI_CubicFirstMoment_angular_tailPrime_high_group_uniform`, `OAI_CubicFirstMoment_angular_tailPrime_low_group`, `OAI_CubicFirstMoment_angular_upperLowTail_stopping`, `OAI_CubicFirstMoment_angular_upperTailNoStopRow_finite_bound_proved`, `OAI_CubicFirstMoment_bounded_divisor_arithmetic_mellin_tail`, `OAI_CubicFirstMoment_height_all_frequency_cutoff_mass`, `OAI_CubicFirstMoment_height_signed_mellin_saving`, `OAI_CubicFirstMoment_largePrimeTuplePiece_ordinary_range`, `OAI_CubicFirstMoment_low_core_mellin_integral_all_exponents`, `OAI_CubicFirstMoment_low_noncube_mass`, `OAI_CubicFirstMoment_ordinary_sparse_centered_bilinear`, `OAI.CubicFirstMoment.primaryPrimePNT_proved`, `OAI_CubicFirstMoment_stoppedBeta_distinguished_log_saving_all`, `OAI_CubicFirstMoment_stoppedBeta_long_bins_log_saving`, `OAI_CubicFirstMoment_stopped_noncube_mass`, `OAI_CubicFirstMoment_stopped_product_transfer`, `OAI_CubicFirstMoment_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_stopped_twisted_cutoff_tail` and `OAI_CubicFirstMoment_tailPrime_high_group_uniform`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A004
import Definitions.Def_OAIQ096A005
import Definitions.Def_OAIQ096A006

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma normNat_primaryNormalize (z : Eisenstein) : normNat (primaryNormalize z) = normNat z :=
  (associated_normNat (primaryNormalize_associated z)).symm

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentNorm_single (p : EisensteinIdealPrime) (n : ℕ) :
    idealExponentNorm (Finsupp.single p n) =
      (normNat (idealPrimeRepresentative p) : ℝ) ^ n := by
  unfold idealExponentNorm idealExponentGenerator
  rw [Finsupp.prod_single_index (h := fun p k => idealPrimeRepresentative p ^ k) (pow_zero _)]
  have h := map_pow normNatHom (idealPrimeRepresentative p) n
  change normNat (idealPrimeRepresentative p ^ n) =
    normNat (idealPrimeRepresentative p) ^ n at h
  rw [h, Nat.cast_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma finiteIdealMoebius_coeff_outside (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) {q : EisensteinIdealPrime} (hq : q ∉ S)
    (hνq : ν q ≠ 0) :
    MvPowerSeries.coeff ν (finiteIdealMoebius S) = 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    have hν : ν ≠ 0 := by
      intro h
      exact hνq (congrArg (fun f : EisensteinIdealExponent => f q) h)
    simp [finiteIdealMoebius, MvPowerSeries.coeff_one, hν]
  | @insert p S hp ih =>
    have hqp : q ≠ p := fun h => hq (h ▸ Finset.mem_insert_self p S)
    have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X, ih ν hqS hνq]
    by_cases hn : 1 ≤ ν p
    · rw [ite_eq_left hn, ih _ hqS]
      · simp
      · simpa [Finsupp.tsub_apply, hqp] using hνq
    · simp [hn]

lemma finiteIdealMoebius_coeff_abs_le_one (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν (finiteIdealMoebius S)| ≤ 1 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => simp [finiteIdealMoebius, MvPowerSeries.coeff_one]; split_ifs <;> norm_num
  | @insert p S hp ih =>
    have he : finiteIdealMoebius (insert p S) =
        finiteIdealMoebius S * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X]
    by_cases hn : 1 ≤ ν p
    · rw [ite_eq_left hn, finiteIdealMoebius_coeff_outside S ν hp
        (Nat.ne_zero_of_lt hn), zero_sub, abs_neg]
      exact ih _
    · simpa [hn] using ih ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusPolynomials
attribute [-instance] _root_.instMeasurableSpace
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

lemma idealPrimaryGenerator_norm (ν : EisensteinIdealExponent) :
    norm (idealPrimaryGenerator ν) = idealExponentNorm ν := by
  rw [← normNat_cast]
  change (normNat (primaryNormalize (idealExponentGenerator ν)) : ℝ) =
    (normNat (idealExponentGenerator ν) : ℝ)
  rw [normNat_primaryNormalize]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-exponent ideal divisor bounds for the short-convolution
polynomials. No bound on the number of distinct prime bases is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentNorm_eq_prod (ν : EisensteinIdealExponent) :
    idealExponentNorm ν = ∏ p ∈ ν.support,
      (normNat (idealPrimeRepresentative p) : ℝ)^ν p := by
  change (normNatHom (∏ p ∈ ν.support, idealPrimeRepresentative p^ν p) : ℝ) = _
  rw [map_prod,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [map_pow,Nat.cast_pow]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- The integral dual of the trace lattice is the inverse different. -/
lemma residue_trace_dual_lattice (z : ℂ)
    (h : ∀ n : Eisenstein, ∃ k : ℤ,
      tracePair (n : ℂ) (z / traceLambda) = k) :
    ∃ a : Eisenstein, (a : ℂ) = z := by
  obtain ⟨n, hn⟩ := h 1
  obtain ⟨k, hk⟩ := h omegaE
  have htrace (w : ℂ) : w + star w = (2 * w.re : ℝ) := by
    apply Complex.ext <;> simp [two_mul]
  have hn' : z / traceLambda + star (z / traceLambda) = n := by
    rw [htrace]
    have hnR : 2 * (z / traceLambda).re = (n : ℝ) := by
      simpa only [tracePair, Subalgebra.coe_one, one_mul] using hn
    exact_mod_cast hnR
  have hk' : omega * (z / traceLambda) + star (omega * (z / traceLambda)) = k := by
    rw [htrace]
    have hkR : 2 * (omega * (z / traceLambda)).re = (k : ℝ) := by
      simpa only [tracePair, omegaE] using hk
    exact_mod_cast hkR
  have ht := trace_pair_lattice hn' hk'
  field_simp [traceLambda_ne_zero] at ht
  refine ⟨ofCoords (n + k) n, ?_⟩
  rw [ofCoords_coe]
  dsimp only [traceLambda] at ht
  push_cast at ht ⊢
  linear_combination -(1/3 : ℂ) * ht +
    ((2*(n:ℂ)+4*(k:ℂ))/3) * omega_quadratic

lemma residueFourierChar_isPrimitive (q : Eisenstein) (hq : q ≠ 0) :
    (residueFourierChar q hq).IsPrimitive := by
  intro a ha hshift
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hall (n : Eisenstein) :
      (Real.fourierChar (tracePair (n : ℂ) (((r : ℂ)/(q : ℂ))/traceLambda)) : ℂ) = 1 := by
    have he := congrArg (fun ψ : AddChar (Residues q) ℂ =>
      ψ (Ideal.Quotient.mk (modulus q) n)) hshift
    simp only [AddChar.mulShift_apply, ← map_mul, residueFourierChar_mk,
      AddChar.one_apply] at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    unfold tracePair
    congr 2
    push_cast
    ring
  obtain ⟨b, hb⟩ := residue_trace_dual_lattice ((r : ℂ)/(q : ℂ))
    (fun n => fourierChar_eq_one_integer.mp (hall n))
  have hqC : (q : ℂ) ≠ 0 := fun he => hq (Subtype.ext he)
  have hr : r = q*b := by
    apply Subtype.ext
    push_cast
    rw [hb]
    field_simp
  apply ha
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.mpr ⟨b, hr⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueConductorKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitivity detects the kernel of every proper residue reduction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma residueReduction_units_surjective {q d : Eisenstein} (hq : q ≠ 0) (hd : d ∣ q) :
    Function.Surjective (Units.map (residueReduction hd).toMonoidHom) := by
  let : Finite (Residues q) := finite_residues hq
  exact finite_ring_units_surjective _ (Ideal.Quotient.factor_surjective _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowGaussBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds and the exact norm of the fixed dual frequency. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaRowHeatScale_pos {h : Eisenstein} (hh : h ≠ 0) :
    0 < cubicThetaRowHeatScale h := by
  rw [cubicThetaRowHeatScale_eq]
  exact mul_pos (by positivity) (norm_pos_of_ne_zero hh)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The six units and the exact index of primary invertible residues. -/
noncomputable section
namespace CubicFirstMoment

lemma eisenstein_neg_omega_primitive : IsPrimitiveRoot (-omegaE) 6 := by
  have hm := IsPrimitiveRoot.neg_one (R:=Eisenstein) 0 (by norm_num : (0:ℕ) ≠ 2)
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hcop : (orderOf (-1:Eisenstein)).Coprime (orderOf omegaE) := by
    rw [←hm.eq_orderOf,←omegaE_primitive.eq_orderOf]
    decide
  rw [show -omegaE=(-1:Eisenstein)*omegaE by ring,
    (Commute.all (-1:Eisenstein) omegaE).orderOf_mul_eq_mul_orderOf_of_coprime hcop,
    ←hm.eq_orderOf,←omegaE_primitive.eq_orderOf]

def eisensteinUnitReductionThree : Eisensteinˣ →* (Residues (3:Eisenstein))ˣ :=
  Units.map (Ideal.Quotient.mk (modulus 3)).toMonoidHom

lemma eisensteinUnitReductionThree_bijective : Function.Bijective eisensteinUnitReductionThree := by
  constructor
  · intro u v huv
    have hq : Ideal.Quotient.mk (modulus 3) ((u:Eisenstein)*(↑v⁻¹:Eisenstein))=1 := by
      have he : Ideal.Quotient.mk (modulus 3) (u:Eisenstein)=
          Ideal.Quotient.mk (modulus 3) (v:Eisenstein) :=
        congrArg (fun x : (Residues (3:Eisenstein))ˣ => (x:Residues 3)) huv
      rw [map_mul,he,←map_mul]
      simp
    have hp := primary_unit_eq_one (u*v⁻¹).isUnit ((primary_iff_residue_one _).mpr hq)
    have he : u*v⁻¹=1 := Units.ext hp
    exact mul_inv_eq_one.mp he
  · intro x
    obtain ⟨u,hu,hp⟩ := unit_lift_mod_three
      (show IsUnit (Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 (x:Residues 3))) by
        rw [residueRepresentative_spec]; exact x.isUnit)
    refine ⟨hu.unit⁻¹,?_⟩
    apply Units.ext
    have he := (primary_iff_residue_one _).mp hp
    rw [map_mul,residueRepresentative_spec] at he
    have hq : Ideal.Quotient.mk (modulus 3) u =
        (eisensteinUnitReductionThree hu.unit : Residues 3) := by
      change _ = Ideal.Quotient.mk (modulus 3) (hu.unit:Eisenstein)
      rw [hu.unit_spec]
    rw [hq] at he
    have he' : x*eisensteinUnitReductionThree hu.unit=1 := Units.ext he
    have hx := eq_inv_of_mul_eq_one_left he'
    simpa only [map_inv] using congrArg (fun v : (Residues (3:Eisenstein))ˣ => (v:Residues 3)) hx.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary local cardinalities for the Eisenstein scattering factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_residueReduction_kernel_card {q d : Eisenstein}
    (hq : q≠0) (hd0 : d≠0) (hd : d∣q) :
    normNat q = normNat d * Nat.card (residueReduction hd).toAddMonoidHom.ker := by
  let f := (residueReduction hd).toAddMonoidHom
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr hd)
  have he := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    residues_card hq,residues_card hd0] at he
  exact he

lemma cubicTheta_residueReduction_primePower_card {p : Eisenstein} (hp : Prime p) (n : ℕ) :
    Nat.card (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n))).toAddMonoidHom.ker =
      normNat p^n := by
  have he := cubicTheta_residueReduction_kernel_card (pow_ne_zero _ hp.ne_zero)
    hp.ne_zero (dvd_pow_self p (Nat.succ_ne_zero n))
  have hn : normNat (p^(n+1))=normNat p^(n+1) := map_pow normNatHom p (n+1)
  rw [hn,pow_succ,mul_comm (normNat p^n)] at he
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (normNat_ne_zero hp.ne_zero)) he.symm

lemma cubicTheta_residueReduction_eq_zero_iff {q d : Eisenstein} (hd : d∣q)
    (x : Residues q) :
    residueReduction hd x=0 ↔ d∣residueRepresentative q x := by
  have he : residueReduction hd x=
      Ideal.Quotient.mk (modulus d) (residueRepresentative q x) := by
    exact (congrArg (residueReduction hd) (residueRepresentative_spec q x)).symm
  rw [he,Ideal.Quotient.eq_zero_iff_mem,modulus,Ideal.mem_span_singleton]

lemma cubicTheta_primePower_nonunit_iff {p : Eisenstein} (hp : Prime p) (n : ℕ)
    (x : Residues (p^(n+1))) :
    ¬IsUnit x ↔ residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x=0 := by
  rw [cubicTheta_residueReduction_eq_zero_iff]
  have hu : IsUnit x ↔ IsCoprime (p^(n+1)) (residueRepresentative (p^(n+1)) x) := by
    constructor
    · intro h
      exact isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
    · intro h
      have he := residue_isUnit_of_isCoprime h
      rwa [residueRepresentative_spec] at he
  rw [hu,IsCoprime.pow_left_iff (Nat.succ_pos n),hp.irreducible.coprime_iff_not_dvd,not_not]

lemma cubicTheta_primePower_units_card {p : Eisenstein} (hp : Prime p) (n : ℕ) :
    Nat.card (Residues (p^(n+1)))ˣ = normNat p^(n+1)-normNat p^n := by
  let : Finite (Residues (p^(n+1))) := finite_residues (pow_ne_zero _ hp.ne_zero)
  let : Fintype (Residues (p^(n+1))) := Fintype.ofFinite _
  let f := (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n))).toAddMonoidHom
  have hk : Nat.card {x : Residues (p^(n+1)) // ¬IsUnit x}=normNat p^n := by
    let e : {x : Residues (p^(n+1)) // ¬IsUnit x} ≃ f.ker :=
      Equiv.subtypeEquivRight (fun x => cubicTheta_primePower_nonunit_iff hp n x)
    rw [Nat.card_congr e]
    exact cubicTheta_residueReduction_primePower_card hp n
  rw [Nat.card_congr (cubicThetaUnitsEquivIsUnit (Residues (p^(n+1))))]
  have he := Fintype.card_subtype_compl (fun x : Residues (p^(n+1)) => ¬IsUnit x)
  simp only [not_not] at he
  rw [Nat.card_eq_fintype_card] at hk
  rw [Nat.card_eq_fintype_card,he,hk,←Nat.card_eq_fintype_card,
    residues_card (pow_ne_zero _ hp.ne_zero)]
  exact congrArg (·-normNat p^n) (map_pow normNatHom p (n+1))

lemma cubicTheta_coprime_units_card {a b : Eisenstein} (hab : IsCoprime a b) :
    Nat.card (Residues (a*b))ˣ = Nat.card (Residues a)ˣ*Nat.card (Residues b)ˣ := by
  let e : Residues (a*b) ≃+* Residues a × Residues b :=
    (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
      (Ideal.quotientMulEquivQuotientProd (modulus a) (modulus b)
        ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))
  rw [Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv,
    Nat.card_congr (MulEquiv.prodUnits : (Residues a × Residues b)ˣ ≃* _).toEquiv,
    Nat.card_prod]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitLifting
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit lifting through powers of an Eisenstein modulus. The cardinality
factor is obtained from the actual additive and multiplicative kernels. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_residue_mk_isUnit_iff (q z : Eisenstein) :
    IsUnit (Ideal.Quotient.mk (modulus q) z) ↔ IsCoprime q z :=
  ⟨isCoprime_of_residue_isUnit,residue_isUnit_of_isCoprime⟩

lemma cubicTheta_unit_card_lift {q d : Eisenstein} (hq : q≠0) (hd : d∣q)
    (hc : ∀ z : Eisenstein, IsCoprime q z ↔ IsCoprime d z) :
    Nat.card (Residues q)ˣ*normNat d=normNat q*Nat.card (Residues d)ˣ := by
  let : Finite (Residues q) := finite_residues hq
  have hr (x : Residues q) : IsUnit x ↔ IsUnit (residueReduction hd x) := by
    have hs := residueRepresentative_spec q x
    rw [←hs,residueReduction_mk,cubicTheta_residue_mk_isUnit_iff,
      cubicTheta_residue_mk_isUnit_iff]
    exact hc _
  have he := unit_card_mul_of_reflect (residueReduction hd)
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr hd)) hr
  have hd0 : d≠0 := by intro he; rw [he,zero_dvd_iff] at hd; exact hq hd
  rwa [residues_card hq,residues_card hd0] at he

lemma cubicTheta_power_units_card {q : Eisenstein} (hq : q≠0) (n : ℕ) :
    Nat.card (Residues (q^(n+1)))ˣ=normNat q^n*Nat.card (Residues q)ˣ := by
  have he := cubicTheta_unit_card_lift (pow_ne_zero _ hq)
    (dvd_pow_self q (Nat.succ_ne_zero n)) (fun _ => IsCoprime.pow_left_iff (Nat.succ_pos n))
  have hn : normNat (q^(n+1))=normNat q^(n+1) := map_pow normNatHom _ _
  rw [hn,pow_succ] at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (normNat_ne_zero hq))
  calc
    _ = (normNat q^n*normNat q)*Nat.card (Residues q)ˣ := he
    _ = _ := by ring

lemma cubicTheta_three_units_card {c : Eisenstein} (hc : c≠0) (h3 : (3:Eisenstein)∣c) :
    Nat.card (Residues (3*c))ˣ=9*Nat.card (Residues c)ˣ := by
  have he := cubicTheta_unit_card_lift (mul_ne_zero (by norm_num) hc) (dvd_mul_left c 3)
    (fun z => ⟨fun h => h.of_mul_left_right,
      fun h => (h.of_isCoprime_of_dvd_left h3).mul_left h⟩)
  have hnorm : normNat (3:Eisenstein)=9 := by
    change ⌊Complex.normSq (3:ℂ)⌋₊=9
    norm_num [Complex.normSq_apply]
  rw [normNat_mul,hnorm] at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (normNat_ne_zero hc))
  calc
    _ = (9*normNat c)*Nat.card (Residues c)ˣ := he
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact arithmetic coefficient of a cube row, with its ramified
factor and finite-ring Euler totient retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_cube_row_three_iff {j : Eisenstein} :
    (3:Eisenstein)∣j^3 ↔ lambdaE∣j := by
  constructor
  · intro h
    have hl3 : lambdaE∣(3:Eisenstein) := by
      refine ⟨-lambdaE,?_⟩
      rw [mul_neg,←pow_two,lambdaE_sq]
      ring
    exact lambdaE_prime.dvd_of_dvd_pow (hl3.trans h)
  · rintro ⟨a,rfl⟩
    refine ⟨-lambdaE*a^3,?_⟩
    rw [mul_pow,pow_succ,lambdaE_sq]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero cubic Eisenstein integer has exactly one ideal exponent
vector and one of two signs. This removes the cube-root multiplicity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaSignedCube (ε : Bool) (ν : EisensteinIdealExponent) : Eisenstein :=
  if ε then -(idealExponentGenerator ν)^3 else (idealExponentGenerator ν)^3

lemma cubicThetaSignedCube_is_cube (ε : Bool) (ν : EisensteinIdealExponent) :
    ∃ j : Eisenstein, j^3=cubicThetaSignedCube ε ν := by
  cases ε
  · exact ⟨idealExponentGenerator ν,rfl⟩
  · exact ⟨-idealExponentGenerator ν,by change (-idealExponentGenerator ν)^3=-(idealExponentGenerator ν)^3; ring⟩

lemma cubicThetaSignedCube_norm (ε : Bool) (ν : EisensteinIdealExponent) :
    norm (cubicThetaSignedCube ε ν)=idealExponentNorm ν^3 := by
  have hc : norm ((idealExponentGenerator ν)^3)=idealExponentNorm ν^3 := by
    rw [←normNat_cast,show normNat ((idealExponentGenerator ν)^3)=
      normNat (idealExponentGenerator ν)^3 from map_pow normNatHom _ _,Nat.cast_pow]
    rfl
  cases ε <;> simpa only [cubicThetaSignedCube,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    norm,Eisenstein.coe_neg,Complex.normSq_neg] using hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientEuler
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler factors for the actual residue-unit counts in the cubic
Eisenstein constant term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaIdealTotient (ν : EisensteinIdealExponent) : ℕ :=
  Nat.card (Residues (idealExponentGenerator ν))ˣ

lemma cubicTheta_units_one : Nat.card (Residues (1:Eisenstein))ˣ=1 := by
  have he : modulus (1:Eisenstein)=⊤ := Ideal.span_singleton_one
  let : Subsingleton (Residues (1:Eisenstein)) := by
    unfold Residues
    rw [he]
    infer_instance
  exact Nat.card_unique

lemma cubicThetaIdealTotient_zero : cubicThetaIdealTotient 0=1 := by
  unfold cubicThetaIdealTotient
  rw [show idealExponentGenerator 0=1 by simp [idealExponentGenerator]]
  exact cubicTheta_units_one

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized finite-ring totient as the actual ideal Möbius
convolution. This identifies its scattering Dirichlet series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaNormInverse : EisensteinArithmeticFunction →+* EisensteinArithmeticFunction :=
  MvPowerSeries.rescale (fun p => (normNat (idealPrimeRepresentative p):ℝ)⁻¹)

lemma cubicThetaNormInverse_coeff (A : EisensteinArithmeticFunction) (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (cubicThetaNormInverse A)=
      MvPowerSeries.coeff ν A/idealExponentNorm ν := by
  rw [cubicThetaNormInverse,MvPowerSeries.coeff_rescale]
  have he : ν.prod (fun p n => ((normNat (idealPrimeRepresentative p):ℝ)⁻¹)^n)=
      (idealExponentNorm ν)⁻¹ := by
    simp only [Finsupp.prod,inv_pow]
    rw [idealExponentNorm_eq_prod,Finset.prod_inv_distrib]
  rw [he]
  ring

lemma cubicThetaNormInverse_X (p : EisensteinIdealPrime) :
    cubicThetaNormInverse (MvPowerSeries.X p)=
      MvPowerSeries.monomial (Finsupp.single p 1) (normNat (idealPrimeRepresentative p):ℝ)⁻¹ := by
  ext ν
  rw [cubicThetaNormInverse_coeff,MvPowerSeries.X_def]
  by_cases hν : ν=Finsupp.single p 1
  · subst ν
    simp [idealExponentNorm_single]
  · simp [MvPowerSeries.coeff_monomial,hν]

lemma totient_finite_product (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse (finiteIdealMoebius S))=
      ∏ p ∈ S, if ν p=0 then 1 else 1-(normNat (idealPrimeRepresentative p):ℝ)⁻¹ := by
  induction S using Finset.induction_on generalizing ν with
  | empty => simp [finiteIdealMoebius,idealZeta,MvPowerSeries.coeff_apply]
  | @insert p S hp ih =>
    have he : idealZeta*cubicThetaNormInverse (finiteIdealMoebius (insert p S))=
        (idealZeta*cubicThetaNormInverse (finiteIdealMoebius S))*
          (1-MvPowerSeries.monomial (Finsupp.single p 1)
            (normNat (idealPrimeRepresentative p):ℝ)⁻¹) := by
      rw [finiteIdealMoebius,Finset.prod_insert hp,map_mul,map_sub,map_one,cubicThetaNormInverse_X]
      unfold finiteIdealMoebius
      ring
    rw [he,mul_sub,mul_one,map_sub,MvPowerSeries.coeff_mul_monomial,ih,ih]
    simp only [Finsupp.single_le_iff]
    rw [Finset.prod_insert hp]
    have ht : (∏ q ∈ S, if (ν-Finsupp.single p 1 : EisensteinIdealExponent) q=0 then 1 else
        1-(normNat (idealPrimeRepresentative q):ℝ)⁻¹)=
      ∏ q ∈ S, if ν q=0 then 1 else 1-(normNat (idealPrimeRepresentative q):ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro q hq
      simp [Finsupp.tsub_apply,ne_of_mem_of_not_mem hq hp]
    rw [ht]
    by_cases hn : ν p=0
    · simp [hn]
    · rw [ite_eq_left (Nat.one_le_iff_ne_zero.mpr hn),ite_eq_right hn]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact quotient of principal ideal zeta functions supplied by the
normalized residue-unit counts. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaIdealDensity (ν : EisensteinIdealExponent) : ℂ :=
  (cubicThetaIdealTotient ν:ℂ)/(idealExponentNorm ν:ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDensityLocal
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local prime factor of the actual normalized residue-unit density. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimeDensity (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) : ℂ :=
  if 0<ν p then cubicThetaIdealDensity ν else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeRowWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The value of either signed cube row in canonical ideal coordinates. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_residue_units_associated {a b : Eisenstein} (h : Associated a b) :
    Nat.card (Residues a)ˣ=Nat.card (Residues b)ˣ := by
  have he : modulus a=modulus b := Ideal.span_singleton_eq_span_singleton.mpr h
  exact Nat.card_congr (Units.mapEquiv (Ideal.quotEquivOfEq he).toMulEquiv).toEquiv

lemma cubicTheta_normNat_neg (a : Eisenstein) : normNat (-a)=normNat a := by
  apply Nat.cast_injective (R:=ℝ)
  rw [normNat_cast,normNat_cast]
  simp only [norm,Eisenstein.coe_neg,Complex.normSq_neg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of the Eisenstein constant coefficient Dirichlet
series by the two signed cubes of each nonzero ideal. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_signed_sum (g : EisensteinIdealExponent → ℂ)
    (hg : Summable (fun ν => ‖g ν‖)) :
    (∑' x : Bool × EisensteinIdealExponent, (3/2:ℂ)*g x.2)=3*(∑' ν, g ν) := by
  have hp : Summable (fun x : Bool × EisensteinIdealExponent => (3/2:ℂ)*g x.2) :=
    summable_mul_of_summable_norm (f:=fun _ : Bool => (3/2:ℂ)) (g:=g)
      (hasSum_fintype _).summable hg
  rw [hp.tsum_prod,tsum_fintype,Fintype.sum_bool]
  rw [tsum_mul_left]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Fourier expansion of each nonzero Eisenstein row,
with the Fourier/Mellin interchange justified by an inverse-square majorant. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRowHeat_factor {t : ℝ} (ht : 0 < t) (v : ℝ) (s : ℂ) (h : Eisenstein) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
      ((Real.pi/t:ℝ)*(Real.exp
        (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ)) =
      (Real.pi:ℂ)*cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t := by
  have hp : (t:ℂ)^(s-1)/(t:ℂ) = (t:ℂ)^(s-2) := by
    calc
      _ = (t:ℂ)^(s-1)/(t:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
        congr 1
        ring
  rw [Complex.ofReal_div]
  calc
    _ = (Real.pi:ℂ)*((t:ℂ)^(s-1)/(t:ℂ))*
        ((Real.exp (-v^2*t):ℂ)*
          (Real.exp (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℂ)) := by ring
    _ = _ := by
      rw [hp, ← Complex.ofReal_mul, ← Real.exp_add]
      unfold cubicThetaDualHeat cubicThetaRowHeatScale
      have he : -v^2*t + -4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h) =
          -v^2*t-(4*Real.pi^2*Complex.normSq (cubicThetaRowFrequency h))/t := by ring
      rw [he]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAxisLineDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pure coordinate second derivatives are derivatives along the
corresponding fixed real tangent direction. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAxisFirst_translate (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    (p : ℂ × ℝ) (t : ℝ) :
    cubicThetaAxisFirst k f (p+t • cubicThetaAxisVector k)=
      deriv (fun w => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 w))
        (cubicThetaCoordinateCenter k p.1.re p.1.im p.2+t) := by
  cases k <;> simp [cubicThetaAxisFirst,cubicThetaAxisVector,cubicThetaCoordinateCenter,
    cubicThetaCoordinateLine,cubicThetaCartesianPoint,Complex.real_smul]

lemma cubicThetaAxisFirst_hasLineDerivAt (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    (p : ℂ × ℝ)
    (hf : ContDiffAt ℝ 2 (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    HasLineDerivAt ℝ (cubicThetaAxisFirst k f) (cubicThetaAxisSecond k f p) p (cubicThetaAxisVector k) := by
  have hd := ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hi := (hasDerivAt_id (0:ℝ)).const_add (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)
  have h := hd.scomp_of_eq 0 hi (by simp)
  change HasDerivAt (fun t => cubicThetaAxisFirst k f (p+t • cubicThetaAxisVector k))
    (cubicThetaAxisSecond k f p) 0
  simpa only [cubicThetaAxisFirst_translate,one_smul,cubicThetaAxisSecond,Function.comp_def,id_eq] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex-valued coordinate integral has the same literal
hyperbolic density v^-3 as the real energy integral. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointIntegral_complex_coordinates {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℂ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y ∂cubicThetaHyperbolicMeasure := by
  rw [← cubicThetaPointCoordinates_map_restrict hS]
  exact (cubicThetaPointInclusion_measurableEmbedding.integral_map f).symm

lemma cubicThetaPointIntegral_complex_density {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℂ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y/(y.2:ℂ)^3 := by
  rw [cubicThetaPointIntegral_complex_coordinates hS]
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaHyperbolicMeasure,setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    cubicThetaHyperbolicDensity_measurable.aemeasurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hT]
  apply setIntegral_congr_fun hT
  rintro y ⟨p,hp,rfl⟩
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  simp only [cubicThetaHyperbolicDensity,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hv.le 3)),Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexIntegrability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integrability under the actual complex hyperbolic coordinate map. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointIntegrable_complex_density {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℂ) :
    IntegrableOn (fun p => f (cubicThetaPointCoordinates p)) S cubicThetaPointMeasure ↔
      IntegrableOn (fun y => f y/(y.2:ℂ)^3) (cubicThetaPointCoordinates '' S) := by
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  have hc := (cubicThetaPointInclusion_measurableEmbedding.integrable_map_iff
    (μ:=cubicThetaPointMeasure.restrict S) (g:=f)).symm
  rw [cubicThetaPointCoordinates_map_restrict hS] at hc
  change IntegrableOn (fun p => f (cubicThetaPointCoordinates p)) S cubicThetaPointMeasure ↔ _ at hc
  rw [hc]
  unfold IntegrableOn cubicThetaHyperbolicMeasure
  rw [restrict_withDensity hT,integrable_withDensity_iff_integrable_smul'
    cubicThetaHyperbolicDensity_measurable (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hT] with y hy
  obtain ⟨p,hp,rfl⟩ := hy
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  simp only [cubicThetaHyperbolicDensity,ENNReal.toReal_ofReal
    (inv_nonneg.mpr (pow_nonneg hv.le 3)),Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexPointMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The already computed hyperbolic Jacobian also applies to the
nonintegral prime normalizer on the same positive-height space. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaComplexPointMeasure_image (g : SL(2,ℂ)) {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    cubicThetaPointMeasure ((fun x => g • x) '' S)=cubicThetaPointMeasure S := by
  have hI : MeasurableSet ((fun x : CubicThetaPoint => g • x) '' S) :=
    (Homeomorph.smul g).measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaPointMeasure_apply hI,cubicThetaPointMeasure_apply hS]
  have he : cubicThetaPointCoordinates '' ((fun x : CubicThetaPoint => g • x) '' S)=
      cubicThetaMobius g '' (cubicThetaPointCoordinates '' S) := by
    rw [image_image,image_image]
    rfl
  rw [he]
  apply cubicThetaHyperbolicMeasure_image _
    (cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS)
  rintro x ⟨y,_,rfl⟩
  exact y.property

instance cubicThetaComplexPointMeasure_invariant :
    SMulInvariantMeasure SL(2,ℂ) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g S hS := by
    have he : (fun x : CubicThetaPoint => g • x) ⁻¹' S=(fun x => g⁻¹ • x) '' S := by
      ext x
      constructor
      · intro hx
        exact ⟨g • x,hx,inv_smul_smul g x⟩
      · rintro ⟨y,hy,rfl⟩
        change g • (g⁻¹ • y)∈S
        rwa [smul_inv_smul]
    rw [he]
    exact cubicThetaComplexPointMeasure_image g⁻¹ hS

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateIntegrationByParts
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the pure coordinate derivatives, with
compact positive-height tests and no assumption on mixed derivatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaAxisFirst_continuousOn (k : CubicThetaAxis) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2}) :
    ContinuousOn (cubicThetaAxisFirst k f) {p : ℂ × ℝ | 0<p.2} := by
  have hc := (hf.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_snd)
    (by norm_num)).clm_apply (continuousOn_const (c:=cubicThetaAxisVector k))
  apply hc.congr
  intro p hp
  exact cubicThetaAxisFirst_eq_fderiv k f
    ((hf.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem residueFourier_reduction_support {q d : Eisenstein} (hq : q≠0)
    [Fintype (Residues q)] (f : Residues q → ℂ) (h : Eisenstein)
    (hf : ∀ x b : Residues q,
      f (x+Ideal.Quotient.mk (modulus q) d*b)=f x)
    (hF : (∑ x : Residues q, f x * residueFourierChar q hq
      (Ideal.Quotient.mk (modulus q) h*x))≠0) : q ∣ d*h := by
  have he := finiteFourier_translation_support (residueFourierChar q hq)
    (residueFourierChar_isPrimitive q hq) f (Ideal.Quotient.mk (modulus q) h)
    (Ideal.Quotient.mk (modulus q) d) hf hF
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rwa [map_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-cover domains in the fixed arithmetic action.  This is
used to compare the three root levels without postulating equality of
integrals on different covers. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

variable (D : CubicThetaArithmeticCover) (K : Subgroup cubicThetaPrincipalGroup)
  (hle : K≤D.group) [K.FiniteIndex]

def cubicThetaRelativeSubgroup : Subgroup D.group := K.comap D.group.subtype

instance cubicThetaRelativeSubgroup_finiteIndex :
    (cubicThetaRelativeSubgroup D K).FiniteIndex := by
  unfold cubicThetaRelativeSubgroup
  exact Subgroup.instFiniteIndex_subgroupOf K D.group

def cubicThetaRelativeSubgroupEquiv : cubicThetaRelativeSubgroup D K ≃* K where
  toFun h := ⟨h.val.val,h.property⟩
  invFun h := ⟨⟨h.val,hle h.property⟩,h.property⟩
  left_inv _h := rfl
  right_inv _h := rfl
  map_mul' _h _k := rfl

def cubicThetaRelativeTransversal : Set D.group :=
  Classical.choose ((cubicThetaRelativeSubgroup D K).exists_isComplement_right 1)

omit [K.FiniteIndex] in
lemma cubicThetaRelativeTransversal_complement :
    Subgroup.IsComplement (cubicThetaRelativeSubgroup D K) (cubicThetaRelativeTransversal D K) :=
  (Classical.choose_spec ((cubicThetaRelativeSubgroup D K).exists_isComplement_right 1)).1

instance cubicThetaRelativeTransversal_finite : Finite (cubicThetaRelativeTransversal D K) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaRelativeTransversal_complement D K).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaRelativeDomain : Set CubicThetaPoint :=
  ⋃ t : cubicThetaRelativeTransversal D K, (fun x : CubicThetaPoint => t.val • x) '' D.domain

include hle in
omit [K.FiniteIndex] in
lemma cubicThetaRelativeDomain_unique (x : CubicThetaPoint) :
    ∃! g : K, g • x∈cubicThetaRelativeDomain D K := by
  obtain ⟨a,ha,hua⟩ := D.unique x
  obtain ⟨⟨h,t⟩,he,hu⟩ := (cubicThetaRelativeTransversal_complement D K).existsUnique a⁻¹
  have hmove : h.val⁻¹=t.val*a := by
    calc
      _ = h.val⁻¹*(a⁻¹*a) := by simp
      _ = h.val⁻¹*((h.val*t.val)*a) := by rw [he]
      _ = _ := by group
  have hraw : ∃! g : cubicThetaRelativeSubgroup D K, g • x∈cubicThetaRelativeDomain D K := by
    refine ⟨h⁻¹,?_,?_⟩
    · apply mem_iUnion.mpr
      refine ⟨t,a • x,ha,?_⟩
      change t.val • (a • x)=h.val⁻¹ • x
      rw [←mul_smul,hmove]
    · intro k hk
      obtain ⟨u,y,hy,hky⟩ := mem_iUnion.mp hk
      have hya : u.val⁻¹*k.val=a := by
        apply hua
        rw [mul_smul]
        change u.val⁻¹ • (k • x)∈D.domain
        rw [←hky,inv_smul_smul]
        exact hy
      have hpair : ((k⁻¹,u) : cubicThetaRelativeSubgroup D K × cubicThetaRelativeTransversal D K)=(h,t) := by
        apply hu
        change k.val⁻¹*u.val=a⁻¹
        rw [←hya]
        group
      have hh : k⁻¹=h := congrArg Prod.fst hpair
      simpa only [inv_inv] using congrArg Inv.inv hh
  obtain ⟨k,hk,huniq⟩ := hraw
  refine ⟨cubicThetaRelativeSubgroupEquiv D K hle k,hk,?_⟩
  intro g hg
  have he := huniq ((cubicThetaRelativeSubgroupEquiv D K hle).symm g) hg
  simpa only [MulEquiv.apply_symm_apply] using congrArg (cubicThetaRelativeSubgroupEquiv D K hle) he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCoverIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-index integral transport in the fixed arithmetic action,
including the nonintegrable case of the Bochner integral convention. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

variable (D : CubicThetaArithmeticCover) (K : Subgroup cubicThetaPrincipalGroup)
  (hle : K≤D.group) [K.FiniteIndex]

omit [K.FiniteIndex] in
lemma cubicThetaRelativeDomain_disjoint :
    Pairwise (fun t u : cubicThetaRelativeTransversal D K =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' D.domain)
        ((fun x : CubicThetaPoint => u.val • x) '' D.domain)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  dsimp only at hga hgb
  have hm : (u.val⁻¹*t.val) • a=b := by rw [mul_smul,hga,←hgb,inv_smul_smul]
  have he : u.val⁻¹*t.val=1 := (D.unique a).unique
    (by rwa [hm]) (by simpa using ha)
  exact htu (Subtype.ext (inv_mul_eq_one.mp he).symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteFourierParseval
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Fourier orthogonality and Parseval for the codifferent
pairing used by the Kloosterman row kernels. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaResidueFourier_norm (q : Eisenstein) (hq : q≠0) (x : Residues q) :
    ‖residueFourierChar q hq x‖=1 := by
  change ‖(Real.fourierChar _:ℂ)‖=1
  exact Circle.norm_coe _

lemma cubicThetaResidueFourier_star (q : Eisenstein) (hq : q≠0) (x : Residues q) :
    star (residueFourierChar q hq x)=residueFourierChar q hq (-x) := by
  rw [AddChar.map_neg_eq_inv,Complex.inv_eq_conj (cubicThetaResidueFourier_norm q hq x)]
  rfl

lemma cubicThetaResidueFourier_orthogonal (q : Eisenstein) (hq : q≠0)
    [Fintype (Residues q)] (x y : Residues q) :
    (∑ a : Residues q,residueFourierChar q hq (a*x)*star (residueFourierChar q hq (a*y)))=
      if x=y then (Fintype.card (Residues q):ℂ) else 0 := by
  classical
  have he (a : Residues q) : residueFourierChar q hq (a*x)*star (residueFourierChar q hq (a*y))=
      residueFourierChar q hq (a*(x-y)) := by
    rw [cubicThetaResidueFourier_star,←AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [AddChar.sum_mulShift (x-y) (residueFourierChar_isPrimitive q hq)]
  simp only [sub_eq_zero]
  split_ifs <;> simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteInflation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact multiplicity in a finite residue-ring inflation. The
surjective reduction is used directly, so no choice of residue representatives
enters the resulting sum identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem residue_sum_inflation {q d : Eisenstein} (hq : q≠0) (hd0 : d≠0)
    (hd : d ∣ q) (f : Residues d → ℂ) :
    (∑' x : Residues q, f (residueReduction hd x))=
      ((norm q/norm d:ℝ):ℂ)*∑' y : Residues d, f y := by
  let : Finite (Residues q) := finite_residues hq
  let : Finite (Residues d) := finite_residues hd0
  let : Fintype (Residues q) := Fintype.ofFinite _
  let : Fintype (Residues d) := Fintype.ofFinite _
  have he := finite_sum_surjective_addHom (residueReduction hd).toAddMonoidHom
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr hd)) f
  change (∑ x : Residues q, f (residueReduction hd x))=
    (Fintype.card (Residues q):ℂ)/(Fintype.card (Residues d):ℂ)*∑ y : Residues d, f y at he
  have hqcard : (Fintype.card (Residues q):ℂ)=(norm q:ℂ) := by
    rw [← Nat.card_eq_fintype_card,residues_card hq]
    exact_mod_cast (normNat_cast q)
  have hdcard : (Fintype.card (Residues d):ℂ)=(norm d:ℂ) := by
    rw [← Nat.card_eq_fintype_card,residues_card hd0]
    exact_mod_cast (normNat_cast d)
  simpa only [tsum_fintype,hqcard,hdcard,Complex.ofReal_div] using he

lemma residueFourierChar_mul_factor {d k : Eisenstein} (hd : d≠0) (hk : k≠0)
    (h a : Eisenstein) :
    residueFourierChar (d*k) (mul_ne_zero hd hk)
        (Ideal.Quotient.mk (modulus (d*k)) (k*h*a))=
      residueFourierChar d hd (Ideal.Quotient.mk (modulus d) (h*a)) := by
  rw [residueFourierChar_mk,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  have hdC : (d:ℂ)≠0 := fun he => hd (Subtype.ext he)
  have hkC : (k:ℂ)≠0 := fun he => hk (Subtype.ext he)
  push_cast
  field_simp [hdC,hkC,traceLambda_ne_zero]

theorem residueFourier_inflation {d k : Eisenstein} (hd : d≠0) (hk : k≠0)
    (f : Residues d → ℂ) (h : Eisenstein) :
    (∑' x : Residues (d*k), f (residueReduction (dvd_mul_right d k) x)*
      residueFourierChar (d*k) (mul_ne_zero hd hk)
        (Ideal.Quotient.mk (modulus (d*k)) (k*h)*x))=
      (norm k:ℂ)*∑' y : Residues d, f y*
        residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*y) := by
  have he (x : Residues (d*k)) :
      residueFourierChar (d*k) (mul_ne_zero hd hk)
          (Ideal.Quotient.mk (modulus (d*k)) (k*h)*x)=
        residueFourierChar d hd
          (Ideal.Quotient.mk (modulus d) h*residueReduction (dvd_mul_right d k) x) := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul,residueReduction_mk,← map_mul]
    exact residueFourierChar_mul_factor hd hk h a
  simp_rw [he]
  have hs := residue_sum_inflation (mul_ne_zero hd hk) hd (dvd_mul_right d k)
    (fun y => f y*residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*y))
  have hn : norm (d*k)/norm d=norm k := by
    rw [norm_mul_eq,mul_div_cancel_left₀ _ (ne_of_gt (norm_pos_of_ne_zero hd))]
  simpa only [hn] using hs

theorem residueFourier_inflation_of_eq {q d k : Eisenstein}
    (hq : q≠0) (hd : d≠0) (hk : k≠0) (hf : q=d*k) (hdq : d ∣ q)
    (f : Residues d → ℂ) (h : Eisenstein) :
    (∑' x : Residues q, f (residueReduction hdq x)*
      residueFourierChar q hq (Ideal.Quotient.mk (modulus q) (k*h)*x))=
      (norm k:ℂ)*∑' y : Residues d, f y*
        residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*y) := by
  subst q
  exact residueFourier_inflation hd hk f h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowFiniteFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Fourier forms of the literal row and cubic-symbol sums.
These expose the same perfect codifferent pairing for Chinese remainders. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSymbolFourier (c : Eisenstein) (hc : c≠0) (h : Eisenstein) : ℂ :=
  ∑' x : Residues c, cubicSymbol c (residueRepresentative c x)*
    residueFourierChar c hc (Ideal.Quotient.mk (modulus c) h*x)

lemma residueFourierChar_mk_mul (c : Eisenstein) (hc : c≠0) (h : Eisenstein)
    (x : Residues c) :
    residueFourierChar c hc (Ideal.Quotient.mk (modulus c) h*x)=
      (Real.fourierChar (tracePair (residueRepresentative c x:ℂ)
        ((h:ℂ)/((c:ℂ)*traceLambda))):ℂ) := by
  have he : Ideal.Quotient.mk (modulus c) h*x=
      Ideal.Quotient.mk (modulus c) (h*residueRepresentative c x) := by
    rw [map_mul,residueRepresentative_spec]
  rw [he,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierCRT
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chinese-remainder factorization of the perfect residue Fourier pairing. -/
noncomputable section
namespace CubicFirstMoment

lemma residueFourierChar_mix {a b : Eisenstein} (ha : a≠0) (hb : b≠0)
    (h : Eisenstein) (v : Residues a × Residues b) :
    residueFourierChar (a*b) (mul_ne_zero ha hb)
        (Ideal.Quotient.mk (modulus (a*b)) h*residueMix a b v)=
      residueFourierChar a ha (Ideal.Quotient.mk (modulus a) h*v.1)*
        residueFourierChar b hb (Ideal.Quotient.mk (modulus b) h*v.2) := by
  rw [residueMix,← map_mul,residueFourierChar_mk,
    residueFourierChar_mk_mul,residueFourierChar_mk_mul]
  have haC : (a:ℂ)≠0 := fun hz => ha (Subtype.ext hz)
  have hbC : (b:ℂ)≠0 := fun hz => hb (Subtype.ext hz)
  have he : ((h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2):Eisenstein):ℂ)*
      (1/(((a*b:Eisenstein):ℂ)*traceLambda))=
      (residueRepresentative a v.1:ℂ)*((h:ℂ)/((a:ℂ)*traceLambda))+
        (residueRepresentative b v.2:ℂ)*((h:ℂ)/((b:ℂ)*traceLambda)) := by
    push_cast
    field_simp [haC,hbC,traceLambda_ne_zero]
  have ht : tracePair ((h*(b*residueRepresentative a v.1+a*residueRepresentative b v.2):Eisenstein):ℂ)
      (1/(((a*b:Eisenstein):ℂ)*traceLambda))=
      tracePair (residueRepresentative a v.1:ℂ) ((h:ℂ)/((a:ℂ)*traceLambda))+
        tracePair (residueRepresentative b v.2:ℂ) ((h:ℂ)/((b:ℂ)*traceLambda)) := by
    unfold tracePair
    rw [he,Complex.add_re,mul_add]
  rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusModes
attribute [-instance] _root_.instMeasurableSpace
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

def cubicThetaPeriodCell (x : Fin 2 → ℝ) : ℂ := 3*eisensteinRealCoords x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaHighWindowTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  star r.phase*cubicThetaHighWindowForcing s (r.height p)

def cubicThetaHighWindowSeries (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaHighWindowTerm r p s

lemma cubicThetaHighWindowTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaHighWindowTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaHighWindowTerm (r.rightMul g) p s := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g)=1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaHighWindowTerm,cubicThetaHighWindowTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*cubicThetaHighWindowForcing s
          (r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p))) := by rw [hu,one_mul]
    _ = _ := by ring

theorem cubicThetaHighWindowSeries_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaHighWindowSeries (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaHighWindowSeries p s := by
  unfold cubicThetaHighWindowSeries
  simp_rw [cubicThetaHighWindowTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaHighWindowTerm r p s)

lemma cubicThetaHighWindowSeries_high {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaHighWindowSeries p s=cubicThetaHighWindowForcing s p.2 := by
  have he : cubicThetaHighWindowSeries p s=cubicThetaHighWindowTerm cubicThetaZeroRow p s := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hh : 1 < r.height p := by
      by_contra ht
      exact hn (mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s (by linarith)))
    have hc := r.high_height_c_zero hp hh
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he]
  simp [cubicThetaHighWindowTerm,CubicThetaBottomRow.height,CubicThetaBottomRow.phase,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimePowerFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaLocalPrimePowerGauss (p : Eisenstein) (hp : p≠0) (n : ℕ)
    (h : Eisenstein) : ℂ :=
  ∑' x : Residues (p^n), cubicSymbol (p^n) (residueRepresentative (p^n) x)*
    residueFourierChar (p^n) (pow_ne_zero n hp) (Ideal.Quotient.mk (modulus (p^n)) h*x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeFourier (p : Eisenstein) (hp : primaryPrime p) (n : ℕ)
    (h : Eisenstein) : ℂ :=
  ∑' y : Residues p, (cubicResidueChar p hp y)^n*
    residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y)

lemma cubicThetaPrimeFourier_gaussSum {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] {n : ℕ} (hn : n≠0) (h : Eisenstein) :
    cubicThetaPrimeFourier p hp n h=
      gaussSum (cubicResidueChar p hp ^ n)
        ((residueFourierChar p hp.2.ne_zero).mulShift (Ideal.Quotient.mk (modulus p) h)) := by
  simp only [cubicThetaPrimeFourier,tsum_fintype,gaussSum,MulChar.pow_apply' _ hn,
    AddChar.mulShift_apply]

theorem cubicThetaPrimeFourier_three {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaPrimeFourier p hp 3 h = if p ∣ h then (norm p:ℂ)-1 else -1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),cubicResidueChar_cube hp]
  let a := Ideal.Quotient.mk (modulus p) h
  have ha : a=0 ↔ p ∣ h := by
    change Ideal.Quotient.mk (modulus p) h=0 ↔ p ∣ h
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hf : gaussSum (1 : MulChar (Residues p) ℂ)
      ((residueFourierChar p hp.2.ne_zero).mulShift a)=
      (∑ y : Residues p, residueFourierChar p hp.2.ne_zero (a*y))-1 := by
    unfold gaussSum
    simp only [AddChar.mulShift_apply]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [MulChar.map_zero,mul_zero,mul_one,AddChar.map_zero_eq_one,add_zero]
    rw [eq_sub_iff_add_eq]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [mul_zero,AddChar.map_zero_eq_one]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (Finset.ne_of_mem_erase hy)),one_mul]
  change gaussSum (1 : MulChar (Residues p) ℂ)
    ((residueFourierChar p hp.2.ne_zero).mulShift a)=_
  rw [hf]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift a (residueFourierChar_isPrimitive p hp.2.ne_zero),ha]
  have hc : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [← Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  split_ifs <;> simp_all

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightedTest
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact tests with the hyperbolic first-derivative weight v^-1.
The support stays away from the singular boundary v=0. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaHeightInverse_axis (k : CubicThetaAxis) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisFirst k cubicThetaHeightInverse p=
      match k with
      | .x => 0
      | .y => 0
      | .height => -((p.2^2)⁻¹ : ℝ) := by
  cases k with
  | x => simp [cubicThetaAxisFirst,cubicThetaCoordinateLine,cubicThetaHeightInverse,cubicThetaCoordinateCenter,cubicThetaCartesianPoint]
  | y => simp [cubicThetaAxisFirst,cubicThetaCoordinateLine,cubicThetaHeightInverse,cubicThetaCoordinateCenter,cubicThetaCartesianPoint]
  | height =>
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt p.2 (hasDerivAt_inv hp.ne')
    simpa only [cubicThetaAxisFirst,cubicThetaCoordinateLine,cubicThetaHeightInverse,
      cubicThetaCoordinateCenter,cubicThetaCartesianPoint,ContinuousLinearMap.toSpanSingleton_apply,
      Complex.ofRealCLM_apply,Function.comp_def,Complex.ofReal_neg] using h.deriv

lemma cubicThetaWeightedTest_axis (k : CubicThetaAxis) {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p=
      star (cubicThetaAxisFirst k φ p)*cubicThetaHeightInverse p+
        star (φ p)*cubicThetaAxisFirst k cubicThetaHeightInverse p := by
  let c := cubicThetaCoordinateCenter k p.1.re p.1.im p.2
  let line := cubicThetaCoordinateLine k p.1.re p.1.im p.2
  have hl : DifferentiableAt ℝ line c := by
    cases k with
    | x =>
      change DifferentiableAt ℝ (fun t : ℝ => ((t:ℂ)+(p.1.im:ℂ)*Complex.I,p.2)) c
      fun_prop
    | y =>
      change DifferentiableAt ℝ (fun t : ℝ => ((p.1.re:ℂ)+(t:ℂ)*Complex.I,p.2)) c
      fun_prop
    | height =>
      change DifferentiableAt ℝ (fun t : ℝ => ((p.1.re:ℂ)+(p.1.im:ℂ)*Complex.I,t)) c
      fun_prop
  have he : line c=p := by
    dsimp [line,c]
    rw [cubicThetaCoordinateLine_center,cubicThetaCartesianPoint_self]
  have hdφ : DifferentiableAt ℝ (fun t => φ (line t)) c :=
    DifferentiableAt.fun_comp' (f:=line) c (hφ.differentiable one_ne_zero (line c)) hl
  have hdv : DifferentiableAt ℝ (fun t => cubicThetaHeightInverse (line t)) c := by
    have hr := (cubicThetaHeightInverse_regular.contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num)
    rw [← he] at hr
    exact DifferentiableAt.fun_comp' (f:=line) c hr hl
  have hstar := hdφ.hasDerivAt.star
  have h := hstar.mul hdv.hasDerivAt
  have hv := h.deriv
  change deriv (fun t => star (φ (line t))*cubicThetaHeightInverse (line t)) c=_ at hv
  change deriv (fun t => star (φ (line t))*cubicThetaHeightInverse (line t)) c=_
  rw [hv,he]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeEulerStep
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact first local Euler step for a frequency prime to p. The two
remaining series retain their actual cubic twists on the prime-free rows. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeFirstFactor (p : Eisenstein) (s : ℂ) (h : Eisenstein) : ℂ :=
  star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p*(norm p:ℂ)^(-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeLocalCases
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeFourier_one_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaPrimeFourier p hp 1 (p*h)=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),pow_one]
  have hz : Ideal.Quotient.mk (modulus p) (p*h)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right p h))
  rw [hz,AddChar.mulShift_zero]
  exact gaussSum_one_right (cubicResidueChar_ne_one hp)

lemma cubicThetaPrimeFourier_two_multiple {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaPrimeFourier p hp 2 (p*h)=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num)]
  have hz : Ideal.Quotient.mk (modulus p) (p*h)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right p h))
  rw [hz,AddChar.mulShift_zero]
  apply gaussSum_one_right
  intro he
  have hc := cubicResidueChar_cube hp
  rw [show (3:ℕ)=2+1 by omega,pow_succ,he,one_mul] at hc
  exact cubicResidueChar_ne_one hp hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeShiftRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeSecondFactor (p : Eisenstein) (s : ℂ) (h : Eisenstein) : ℂ :=
  (norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p)*((norm p:ℂ)^(-s))^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDeterminant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The determinant of the two local prime-free equations has no zeros
on the continued half-plane. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimaryPrime_norm_gt_one {p : Eisenstein} (hp : primaryPrime p) :
    1<norm p := by
  have hN := one_le_norm hp.2.ne_zero
  exact lt_of_le_of_ne hN (fun he => hp.2.not_isUnit (isUnit_of_norm_eq_one he.symm))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCriticalFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the critical finite Gauss factors with the exact Euler factors
of the constructed arithmetic Fourier family. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCriticalScale (p : Eisenstein) : ℂ :=
  (norm p:ℂ)^(-(1/3:ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeIwahori
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-index subgroup and cubic diagonal character needed
for the unramified local correspondence. All data come from reduction of
the principal arithmetic group; no local representation input is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeReduction (p : Eisenstein) :
    cubicThetaPrincipalGroup →* SL(2,Residues p) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus p))).comp
    cubicThetaPrincipalGroup.subtype

lemma cubicThetaPrimeReduction_ker_le (p : Eisenstein) :
    (cubicThetaPrimeReduction p).ker ≤ cubicThetaPrimeIwahori p := by
  intro g hg
  have he := congrArg (fun A : SL(2,Residues p) => A 1 0) hg
  change Ideal.Quotient.mk (modulus p) (g.val 1 0)=0 at he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)

theorem cubicThetaPrimeIwahori_finiteIndex {p : Eisenstein} (hp : p≠0) :
    (cubicThetaPrimeIwahori p).FiniteIndex := by
  let : Finite (Residues p) := finite_residues hp
  let : Finite (cubicThetaPrimeReduction p).range := inferInstance
  let : (cubicThetaPrimeReduction p).ker.FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (cubicThetaPrimeReduction_ker_le p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dilation by a cubed prime pulls an original section to a genuine
section on the integral cubed-prime subgroup, with the same multiplier. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeSections (p : Eisenstein) : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrimeIwahori (p^3), ∀ x : CubicThetaPoint,
    F (g.val • x)=cubicThetaKubotaValue g.val*F x}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g x
    change F (g.val • x)+G (g.val • x)=cubicThetaKubotaValue g.val*(F x+G x)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro c F hF g x
    change c*F (g.val • x)=cubicThetaKubotaValue g.val*(c*F x)
    rw [hF]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTransversal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite right cosets used by the cubed-prime Hecke trace. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeIwahori_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeIwahori (p^3)).FiniteIndex :=
  cubicThetaPrimeIwahori_finiteIndex (pow_ne_zero 3 hp.2.ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTrace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite cubed-prime trace, with its cubic multipliers.
Composing it with dilation gives the actual cubed-prime Hecke operator. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeTraceTerm (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) : ℂ :=
  star (cubicThetaKubotaValue g)*F.val (g • x)

lemma cubicThetaPrimeCubeTraceTerm_left (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (h : cubicThetaPrimeIwahori (p^3)) (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F (h.val*g) x=cubicThetaPrimeCubeTraceTerm p F g x := by
  have hu : star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  unfold cubicThetaPrimeCubeTraceTerm
  rw [mul_smul,F.property,cubicThetaKubotaValue_mul,star_mul]
  calc
    _ = (star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val)*
      (star (cubicThetaKubotaValue g)*F.val (g • x)) := by ring
    _ = _ := by rw [hu,one_mul]

lemma cubicThetaPrimeCubeTraceTerm_translate (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g h : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F g (h • x)=
      cubicThetaKubotaValue h*cubicThetaPrimeCubeTraceTerm p F (g*h) x := by
  have hu : cubicThetaKubotaValue h*star (cubicThetaKubotaValue h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (cubicThetaKubotaValue h*star (cubicThetaKubotaValue h))*
      cubicThetaPrimeCubeTraceTerm p F g (h • x) := by rw [hu,one_mul]
    _ = _ := by
      simp only [cubicThetaPrimeCubeTraceTerm,cubicThetaKubotaValue_mul,star_mul,mul_smul]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeCosets
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete bottom-row coordinates for the cubed-prime correspondence.
The first chart is represented by integral lower unipotents in level three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrincipalLower (m : Eisenstein) : cubicThetaPrincipalGroup :=
  let g : SL(2,Eisenstein) := ⟨!![1,0;3*m,1],by simp [Matrix.det_fin_two]⟩
  ⟨g,(cubicThetaPrincipalGroup_mem_iff g).mpr
    ⟨primary_one,dvd_zero _,⟨m,rfl⟩,primary_one⟩⟩

lemma cubicThetaPrincipalLower_value (m : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaPrincipalLower m)=1 := by
  rw [cubicThetaKubotaValue_eq_symbol]
  exact cubicSymbol_one_lower _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeUpperChart
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary chart of the cubed-prime correspondence. Its
parameters are the residue classes divisible by the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeUpperParameter (p : Eisenstein) :=
  {r : Residues (p^3) // p ∣ residueRepresentative (p^3) r}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeChartCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two integral charts are disjoint and cover the actual right
cosets. The proof uses the primitive bottom row and units modulo p^3. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRepresentative_dvd {p x : Eisenstein} (hx : p∣x) :
    p∣residueRepresentative (p^3) (Ideal.Quotient.mk (modulus (p^3)) x) := by
  have he := residueRepresentative_spec (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)
  have hd : p^3 ∣ residueRepresentative (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have ht := dvd_add ((dvd_pow_self p (by norm_num : (3:ℕ)≠0)).trans hd) hx
  simpa only [sub_add_cancel] using ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReductionRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows that triangularize the three nonzero valuation
branches of the cubed-prime lower chart. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReduction_primary {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) : primary (p^(3-k.val)) := by
  fin_cases k
  · exact cubicThetaPrimeCube_primary hp
  · change primary (p^2)
    simpa only [pow_two] using primary_mul hp.1 hp.1
  · simpa only [Nat.reduceSub,pow_one] using hp.1

def cubicThetaPrimeCubeReductionRow {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : CubicThetaBottomRow where
  c := -3*n
  d := p^(3-k.val)
  c_three := ⟨-n,by ring⟩
  d_primary := cubicThetaPrimeCubeReduction_primary hp k
  coprime := by
    simpa only [neg_mul] using
      ((primary_coprime_three (cubicThetaPrimeCubeReduction_primary hp k)).symm.mul_left
        ((hp.2.coprime_iff_not_dvd.mpr hn).symm.pow_right)).neg_left

def cubicThetaPrimeCubeReduction {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : cubicThetaPrincipalGroup :=
  (cubicThetaPrimeCubeReductionRow hp k n hn).completion

lemma cubicThetaPrimeCubeReduction_c {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    (cubicThetaPrimeCubeReduction hp k n hn).val 1 0= -3*n :=
  congrArg CubicThetaBottomRow.c (cubicThetaPrimeCubeReductionRow hp k n hn).completion_row

lemma cubicThetaPrimeCubeReduction_d {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    (cubicThetaPrimeCubeReduction hp k n hn).val 1 1=p^(3-k.val) :=
  congrArg CubicThetaBottomRow.d (cubicThetaPrimeCubeReductionRow hp k n hn).completion_row

lemma cubicThetaPrimeCubeReduction_determinant {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    (cubicThetaPrimeCubeReduction hp k n hn).val 0 0*p^(3-k.val)+
      3*n*(cubicThetaPrimeCubeReduction hp k n hn).val 0 1=1 := by
  have he := cubicThetaPrincipalGroup_det (cubicThetaPrimeCubeReduction hp k n hn)
  rw [cubicThetaPrimeCubeReduction_c,cubicThetaPrimeCubeReduction_d] at he
  linear_combination he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTriangular
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangularization of the nonzero valuation branches in the
cubed-prime trace. The matrices are the actual integral row completions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeReducedScale {p : Eisenstein} (_hp : primaryPrime p) (k : Fin 3) : ℂ :=
  (p:ℂ)^(3-k.val)/cubicThetaPrimeSquareRoot (p^3)

lemma cubicThetaPrimeCubeReducedScale_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) : cubicThetaPrimeCubeReducedScale hp k≠0 :=
  div_ne_zero (pow_ne_zero _ (fun hz => hp.2.ne_zero (Subtype.ext hz)))
    (cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero))

def cubicThetaPrimeCubeReducedMatrix {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : SL(2,ℂ) :=
  cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn)*
    cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*
    cubicThetaPrincipalComplex (cubicThetaPrincipalLower (p^k.val*n))

lemma cubicThetaPrimeCubeReducedMatrix_c {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 1 0=0 := by
  let q := cubicThetaPrimeSquareRoot (p^3)
  have hq : q≠0 := cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)
  have hs : q^2=(p:ℂ)^3 := by
    exact (cubicThetaPrimeSquareRoot_sq (p^3)).trans
      (map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3)
  have he : (p:ℂ)^(3-k.val)*(p:ℂ)^k.val=(p:ℂ)^3 := by
    rw [←pow_add]
    congr 1
    omega
  change (((cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrincipalComplex
    (cubicThetaPrincipalLower (p^k.val*n)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 0)=0
  simp only [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrincipalComplex_apply]
  change ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*q+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*0)*1+
    ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*0+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*q⁻¹)*
        ((3*(p^k.val*n):Eisenstein):ℂ)=0
  rw [cubicThetaPrimeCubeReduction_c,cubicThetaPrimeCubeReduction_d]
  push_cast
  rw [show ((3:Eisenstein):ℂ)=(3:ℂ) from
    map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
  simp only [mul_zero,zero_add,add_zero,mul_one]
  calc
    _ = (3*(n:ℂ)/q)*((p:ℂ)^(3-k.val)*(p:ℂ)^k.val-q^2) := by
      field_simp
      ring
    _ = 0 := by rw [he,hs,sub_self,mul_zero]

lemma cubicThetaPrimeCubeReducedMatrix_d {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 1 1=cubicThetaPrimeCubeReducedScale hp k := by
  change (((cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrincipalComplex
    (cubicThetaPrincipalLower (p^k.val*n)) : Matrix (Fin 2) (Fin 2) ℂ)) 1 1)=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrincipalComplex_apply]
  change ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*
      cubicThetaPrimeSquareRoot (p^3)+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*0)*0+
    ((((cubicThetaPrimeCubeReduction hp k n hn).val 1 0:Eisenstein):ℂ)*0+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 1 1:Eisenstein):ℂ)*
        (cubicThetaPrimeSquareRoot (p^3))⁻¹)*1=_
  rw [cubicThetaPrimeCubeReduction_d]
  push_cast
  simp [cubicThetaPrimeCubeReducedScale,div_eq_mul_inv]

lemma cubicThetaPrimeCubeReducedMatrix_b {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 0 1=
      (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/
        cubicThetaPrimeSquareRoot (p^3) := by
  change (((cubicThetaPrincipalComplex (cubicThetaPrimeCubeReduction hp k n hn) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :
    Matrix (Fin 2) (Fin 2) ℂ)*(cubicThetaPrincipalComplex
    (cubicThetaPrincipalLower (p^k.val*n)) : Matrix (Fin 2) (Fin 2) ℂ)) 0 1)=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrincipalComplex_apply]
  change ((((cubicThetaPrimeCubeReduction hp k n hn).val 0 0:Eisenstein):ℂ)*
      cubicThetaPrimeSquareRoot (p^3)+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)*0)*0+
    ((((cubicThetaPrimeCubeReduction hp k n hn).val 0 0:Eisenstein):ℂ)*0+
      (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)*
        (cubicThetaPrimeSquareRoot (p^3))⁻¹)*1=_
  simp [div_eq_mul_inv]

lemma cubicThetaPrimeCubeReducedMatrix_a {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    cubicThetaPrimeCubeReducedMatrix hp k n hn 0 0=(cubicThetaPrimeCubeReducedScale hp k)⁻¹ := by
  have he := (cubicThetaPrimeCubeReducedMatrix hp k n hn).property
  rw [Matrix.det_fin_two,cubicThetaPrimeCubeReducedMatrix_c,cubicThetaPrimeCubeReducedMatrix_d,
    mul_zero,sub_zero] at he
  exact eq_inv_of_mul_eq_one_left he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReductionPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic phase of each triangularized branch is the corresponding
power of the numerator character of its upper-right entry. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReduction_top_congruence {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    p∣3*n*(cubicThetaPrimeCubeReduction hp k n hn).val 0 1-1 := by
  have he := cubicThetaPrimeCubeReduction_determinant hp k n hn
  have hpw : p∣p^(3-k.val) := dvd_pow_self p (by have := k.isLt; omega)
  rw [show 3*n*(cubicThetaPrimeCubeReduction hp k n hn).val 0 1-1=
    -((cubicThetaPrimeCubeReduction hp k n hn).val 0 0*p^(3-k.val)) by
      linear_combination he]
  exact dvd_neg.mpr (dvd_mul_of_dvd_right hpw _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReductionResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The translation selected by the actual row completion is the inverse
of 9n modulo its prime power. Thus its choice agrees with finite Fourier
reindexing and with the original period-three lattice. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeReductionTranslation {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : Eisenstein :=
  (cubicThetaPrimeCubeReduction hp k n hn).val 0 1/3

lemma cubicThetaPrimeCubeReductionTranslation_three {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    3*cubicThetaPrimeCubeReductionTranslation hp k n hn=
      (cubicThetaPrimeCubeReduction hp k n hn).val 0 1 := by
  apply EuclideanDomain.mul_div_cancel' (by norm_num : (3:Eisenstein)≠0)
  exact (cubicThetaPrincipalGroup_offDiagonal (cubicThetaPrimeCubeReduction hp k n hn)).1

lemma cubicThetaPrimeCubeReductionTranslation_congruence {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    p^(3-k.val) ∣ 9*n*cubicThetaPrimeCubeReductionTranslation hp k n hn-1 := by
  have he := cubicThetaPrimeCubeReduction_determinant hp k n hn
  rw [←cubicThetaPrimeCubeReductionTranslation_three hp k n hn] at he
  refine ⟨-(cubicThetaPrimeCubeReduction hp k n hn).val 0 0,?_⟩
  linear_combination he

def cubicThetaPrimeCubeReductionTranslationUnit {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : (Residues (p^(3-k.val)))ˣ := by
  have h9 : IsCoprime (p^(3-k.val)) (9:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCubeReduction_primary hp k)).pow_right
      (n := 2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  exact (residue_isUnit_of_isCoprime
    (h9.mul_right ((hp.2.coprime_iff_not_dvd.mpr hn).pow_left))).unit

theorem cubicThetaPrimeCubeReductionTranslation_residue {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    Ideal.Quotient.mk (modulus (p^(3-k.val)))
      (cubicThetaPrimeCubeReductionTranslation hp k n hn)=
        ((cubicThetaPrimeCubeReductionTranslationUnit hp k n hn)⁻¹ :
          (Residues (p^(3-k.val)))ˣ) := by
  let u := cubicThetaPrimeCubeReductionTranslationUnit hp k n hn
  have hu : (u : Residues (p^(3-k.val)))=
      Ideal.Quotient.mk (modulus (p^(3-k.val))) (9*n) := IsUnit.unit_spec _
  apply u.eq_inv_of_mul_eq_one_left
  rw [hu,←map_mul]
  exact (residue_eq_of_dvd_sub
    (cubicThetaPrimeCubeReductionTranslation_congruence hp k n hn)).trans (map_one _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTriangularCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual hyperbolic coordinates of the triangularized cubed-prime
branches; the horizontal translation is retained exactly. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeReducedMatrix_mobius {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (z : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      ((cubicThetaPrimeCubeReducedScale hp k)⁻¹^2*z.1+
        ((((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/
          cubicThetaPrimeSquareRoot (p^3))/cubicThetaPrimeCubeReducedScale hp k,
        z.2/Complex.normSq (cubicThetaPrimeCubeReducedScale hp k)) := by
  let t := cubicThetaPrimeCubeReducedScale hp k
  let b := (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/
    cubicThetaPrimeSquareRoot (p^3)
  have ht : t≠0 := cubicThetaPrimeCubeReducedScale_ne_zero hp k
  have hts : star t≠0 := star_ne_zero.mpr ht
  have hden : cubicThetaMobiusDenominator (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      Complex.normSq t := by
    simp [cubicThetaMobiusDenominator,cubicThetaPrimeCubeReducedMatrix_c,
      cubicThetaPrimeCubeReducedMatrix_d,t]
  have hnum : cubicThetaMobiusNumerator (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      (t⁻¹*z.1+b)*star t := by
    simp [cubicThetaMobiusNumerator,cubicThetaPrimeCubeReducedMatrix_c,
      cubicThetaPrimeCubeReducedMatrix_d,cubicThetaPrimeCubeReducedMatrix_a,
      cubicThetaPrimeCubeReducedMatrix_b,t,b]
  apply Prod.ext
  · change cubicThetaMobiusNumerator _ z/(cubicThetaMobiusDenominator _ z:ℂ)=t⁻¹^2*z.1+b/t
    rw [hnum,hden,show (Complex.normSq t:ℂ)=t*star t from (Complex.mul_conj t).symm]
    field_simp
  · change z.2/cubicThetaMobiusDenominator _ z=z.2/Complex.normSq t
    rw [hden]

lemma cubicThetaPrimeCubeReducedScale_square {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) :
    (cubicThetaPrimeCubeReducedScale hp k)⁻¹^2=(p:ℂ)^k.val/(p:ℂ)^(3-k.val) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hs : (cubicThetaPrimeSquareRoot (p^3))^2=(p:ℂ)^3 :=
    (cubicThetaPrimeSquareRoot_sq (p^3)).trans
      (map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3)
  have he : (p:ℂ)^(3-k.val)*(p:ℂ)^k.val=(p:ℂ)^3 := by
    rw [←pow_add]
    congr 1
    omega
  unfold cubicThetaPrimeCubeReducedScale
  rw [inv_div,div_pow,hs,←he]
  field_simp

lemma cubicThetaPrimeCubeReducedScale_translation {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b : ℂ) :
    (b/cubicThetaPrimeSquareRoot (p^3))/cubicThetaPrimeCubeReducedScale hp k=
      b/(p:ℂ)^(3-k.val) := by
  have hq := cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  unfold cubicThetaPrimeCubeReducedScale
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBranchCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized prime-power coordinates of each nonzero valuation
branch in the actual cubed-prime trace. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReducedScale_normSq_inv {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) :
    (Complex.normSq (cubicThetaPrimeCubeReducedScale hp k))⁻¹=
      ‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val) := by
  calc
    _ = ‖(cubicThetaPrimeCubeReducedScale hp k)⁻¹^2‖ := by
      rw [norm_pow,norm_inv,Complex.normSq_eq_norm_sq,inv_pow]
    _ = _ := by
      rw [cubicThetaPrimeCubeReducedScale_square,norm_div,norm_pow,norm_pow]

theorem cubicThetaPrimeCubeReducedMatrix_coordinates {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (z : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*z.1+
        (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/(p:ℂ)^(3-k.val),
        (‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val))*z.2) := by
  rw [cubicThetaPrimeCubeReducedMatrix_mobius,cubicThetaPrimeCubeReducedScale_square,
    cubicThetaPrimeCubeReducedScale_translation]
  apply Prod.ext
  · rfl
  · change z.2*(Complex.normSq (cubicThetaPrimeCubeReducedScale hp k))⁻¹=_
    rw [cubicThetaPrimeCubeReducedScale_normSq_inv,mul_comm]

def cubicThetaPrimeCubeBranchPoint {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b : Eisenstein) (x : CubicThetaPoint) : CubicThetaPoint :=
  ⟨((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*x.val.1+((3*b:Eisenstein):ℂ)/(p:ℂ)^(3-k.val),
    (‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val))*x.val.2),
    mul_pos (div_pos (pow_pos (norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))) _)
      (pow_pos (norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))) _)) x.property⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBranchPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each triangular branch depends only on its residue parameter, with
the period-three automorphy and the cubic phase both retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeBranchPoint_translate {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b m : Eisenstein) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeBranchPoint hp k (b+p^(3-k.val)*m) x=
      cubicThetaPrincipalTranslation m • cubicThetaPrimeCubeBranchPoint hp k b x := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  apply Subtype.ext
  change _=cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation m)) _
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
  apply Prod.ext
  · change (p:ℂ)^k.val/(p:ℂ)^(3-k.val)*x.val.1+
      ((3*(b+p^(3-k.val)*m):Eisenstein):ℂ)/(p:ℂ)^(3-k.val)=
        ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*x.val.1+((3*b:Eisenstein):ℂ)/(p:ℂ)^(3-k.val))+
          ((3*m:Eisenstein):ℂ)
    push_cast
    field_simp
    ring
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalSection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous periodic horizontal slices of the actual automorphic
sections, with their genuine finite cell integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalPoint_continuous (v : ℝ) (hv : 0<v) :
    Continuous (cubicThetaHorizontalPoint v hv) := by
  apply Continuous.subtype_mk
  exact continuous_id.prodMk continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalAffine
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine translates have the same cell integral after an integral
nonzero Eisenstein dilation. This is used for the character branches. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontal_multiply_periodic (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (a : Eisenstein)
    (w : Eisenstein) (z : ℂ) :
    f ((a:ℂ)*(z+3*(w:ℂ)))=f ((a:ℂ)*z) := by
  have he : (a:ℂ)*(z+3*(w:ℂ))=(a:ℂ)*z+3*((a*w:Eisenstein):ℂ) := by
    push_cast
    ring
  rw [he,hf]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual horizontal additive character and its level-three period. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaHorizontalCharacter (h : Eisenstein) (z : ℂ) : ℂ :=
  Real.fourierChar (tracePair z (cubicThetaRowFrequency h))

lemma cubicThetaHorizontalCharacter_add (h : Eisenstein) (z w : ℂ) :
    cubicThetaHorizontalCharacter h (z+w)=
      cubicThetaHorizontalCharacter h z*cubicThetaHorizontalCharacter h w := by
  unfold cubicThetaHorizontalCharacter
  have he : tracePair (z+w) (cubicThetaRowFrequency h)=
      tracePair z (cubicThetaRowFrequency h)+tracePair w (cubicThetaRowFrequency h) := by
    simp only [tracePair,add_mul,Complex.add_re]
    ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma cubicThetaHorizontalCharacter_three (h w : Eisenstein) :
    cubicThetaHorizontalCharacter h (3*(w:ℂ))=1 := by
  have he : tracePair (3*(w:ℂ)) (cubicThetaRowFrequency h)=
      tracePair ((w*h:Eisenstein):ℂ) (1/traceLambda) := by
    unfold tracePair cubicThetaRowFrequency
    push_cast
    congr 2
    field_simp [traceLambda_ne_zero]
  change (Real.fourierChar (tracePair (3*(w:ℂ)) (cubicThetaRowFrequency h)):ℂ)=1
  rw [he,tracePhase_div_lambda_one]

lemma cubicThetaHorizontalCharacter_periodic (h w : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalCharacter h (z+3*(w:ℂ))=cubicThetaHorizontalCharacter h z := by
  rw [cubicThetaHorizontalCharacter_add,cubicThetaHorizontalCharacter_three,mul_one]

lemma cubicThetaHorizontalCharacter_unit (h : Eisenstein) (z : ℂ) :
    star (cubicThetaHorizontalCharacter h z)*cubicThetaHorizontalCharacter h z=1 := by
  rw [mul_comm,Complex.star_def,Complex.mul_conj']
  change (‖(Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)‖:ℂ)^2=1
  rw [Circle.norm_coe]
  simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue coordinates for the sublattice used by a horizontal
Hecke dilation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalLattice_bijective {a : Eisenstein} (ha : a≠0) :
    Function.Bijective (fun mr : Eisenstein × Residues a =>
      a*mr.1+residueRepresentative a mr.2) := by
  constructor
  · rintro ⟨m,r⟩ ⟨n,s⟩ he
    have hr : r=s := by
      have hd : a∣residueRepresentative a r-residueRepresentative a s := by
        refine ⟨n-m,?_⟩
        linear_combination he
      simpa only [residueRepresentative_spec] using residue_eq_of_dvd_sub hd
    subst s
    have hm : m=n := mul_left_cancel₀ ha (add_right_cancel he)
    subst n
    rfl
  · intro b
    let r := Ideal.Quotient.mk (modulus a) b
    have hd : a∣b-residueRepresentative a r := by
      apply dvd_sub_comm.mp
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec a r))
    obtain ⟨m,hm⟩ := hd
    refine ⟨(m,r),?_⟩
    dsimp
    linear_combination -hm

def cubicThetaHorizontalLatticeEquiv {a : Eisenstein} (ha : a≠0) :
    (Eisenstein × Residues a) ≃ Eisenstein :=
  Equiv.ofBijective _ (cubicThetaHorizontalLattice_bijective ha)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier observations on the literal half-open cell, under translation
and integral dilation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalFourier_integrand_periodic (h : Eisenstein) (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (w : Eisenstein) (z : ℂ) :
    star (cubicThetaHorizontalCharacter h (z+3*(w:ℂ)))*f (z+3*(w:ℂ))=
      star (cubicThetaHorizontalCharacter h z)*f z := by
  rw [cubicThetaHorizontalCharacter_periodic,hf]

lemma cubicThetaHorizontalCharacter_mul_index (a h : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalCharacter (a*h) z=cubicThetaHorizontalCharacter h ((a:ℂ)*z) := by
  unfold cubicThetaHorizontalCharacter cubicThetaRowFrequency
  congr 2
  unfold tracePair
  push_cast
  congr 2
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierIntegrability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integrability of the actual weighted cell coefficients. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_continuous (h : Eisenstein) :
    Continuous (cubicThetaHorizontalCharacter h) := by
  unfold cubicThetaHorizontalCharacter
  apply continuous_subtype_val.comp
  apply Real.continuous_fourierChar.comp
  unfold tracePair
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierVanishing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dilation kills precisely the horizontal frequencies outside the
corresponding principal ideal, by the primitive finite trace pairing. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_fraction (h q b : Eisenstein) (hq : q≠0) :
    cubicThetaHorizontalCharacter h (3*(b:ℂ)/(q:ℂ))=
      residueFourierChar q hq (Ideal.Quotient.mk (modulus q) (h*b)) := by
  rw [residueFourierChar_mk]
  unfold cubicThetaHorizontalCharacter
  congr 2
  unfold tracePair cubicThetaRowFrequency
  push_cast
  congr 2
  field_simp [traceLambda_ne_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalPeriodization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal periodization appearing in the bottom Hecke branch. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalFraction (a : Eisenstein) (f : ℂ → ℂ) (b : Eisenstein) (z : ℂ) : ℂ :=
  f ((z+3*(b:ℂ))/(a:ℂ))

def cubicThetaHorizontalPeriodization (a : Eisenstein) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' r : Residues a,cubicThetaHorizontalFraction a f (residueRepresentative a r) z

lemma cubicThetaHorizontalFraction_congr {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {b c : Eisenstein} (hbc : a∣b-c) (z : ℂ) :
    cubicThetaHorizontalFraction a f b z=cubicThetaHorizontalFraction a f c z := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  obtain ⟨m,hm⟩ := hbc
  have hb : b=c+a*m := by linear_combination hm
  have hx : (z+3*(b:ℂ))/(a:ℂ)=(z+3*(c:ℂ))/(a:ℂ)+3*(m:ℂ) := by
    rw [hb]
    push_cast
    field_simp [haC]
    ring
  unfold cubicThetaHorizontalFraction
  rw [hx,hf]

lemma cubicThetaHorizontalPeriodization_periodic {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (w : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalPeriodization a f (z+3*(w:ℂ))=cubicThetaHorizontalPeriodization a f z := by
  let e : Residues a ≃ Residues a := Equiv.addRight (Ideal.Quotient.mk (modulus a) w)
  unfold cubicThetaHorizontalPeriodization
  calc
    _ = ∑' r : Residues a,cubicThetaHorizontalFraction a f
        (residueRepresentative a (e r)) z := by
      apply tsum_congr
      intro r
      have he : cubicThetaHorizontalFraction a f (residueRepresentative a r) (z+3*(w:ℂ))=
          cubicThetaHorizontalFraction a f (residueRepresentative a r+w) z := by
        unfold cubicThetaHorizontalFraction
        congr 2
        push_cast
        ring
      rw [he]
      apply cubicThetaHorizontalFraction_congr ha f hf
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      change Ideal.Quotient.mk (modulus a) (residueRepresentative a r+w)=
        Ideal.Quotient.mk (modulus a) (residueRepresentative a (e r))
      rw [residueRepresentative_spec,map_add,residueRepresentative_spec]
      rfl
    _ = _ := e.tsum_eq (fun r : Residues a => cubicThetaHorizontalFraction a f (residueRepresentative a r) z)

lemma cubicThetaHorizontalPeriodization_continuous {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) : Continuous (cubicThetaHorizontalPeriodization a f) := by
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  unfold cubicThetaHorizontalPeriodization
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro r _
  unfold cubicThetaHorizontalFraction
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryResidueNine
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma primary_of_nine_congr {a b : Eisenstein} (ha : primary a)
    (hab : (9:Eisenstein) ∣ a-b) : primary b := by
  obtain ⟨k,hk⟩ := ha
  obtain ⟨t,ht⟩ := hab
  exact ⟨k-3*t,by linear_combination hk-ht⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryFourierTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem cubicThetaSymbolFourier_mul {c : Eisenstein} (hc : primary c)
    {r : Eisenstein} (hcr : IsCoprime c r) (h : Eisenstein) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) (h*r)=
      star (cubicSymbol c r)*cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  let : Finite (Residues c) := finite_residues (primary_ne_zero hc)
  let : Fintype (Residues c) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hcr
  let ψ := residueFourierChar c (primary_ne_zero hc)
  let f (x : Residues c) : ℂ := cubicSymbol c (residueRepresentative c x)*
    ψ (Ideal.Quotient.mk (modulus c) h*x)
  let g (x : Residues c) : ℂ := cubicSymbol c (residueRepresentative c x)*
    ψ (Ideal.Quotient.mk (modulus c) (h*r)*x)
  have hw (x : Residues c) :
      cubicSymbol c (residueRepresentative c (u.mulLeft x))=
        cubicSymbol c r*cubicSymbol c (residueRepresentative c x) := by
    have he : Ideal.Quotient.mk (modulus c) (residueRepresentative c (u.mulLeft x))=
        Ideal.Quotient.mk (modulus c) (r*residueRepresentative c x) := by
      rw [residueRepresentative_spec,map_mul,residueRepresentative_spec]
      change (u:Residues c)*x=Ideal.Quotient.mk (modulus c) r*x
      rw [hu]
    rw [cubicSymbol_congr he,cubicSymbol_mul_upper hc]
  have hp (x : Residues c) : f (u.mulLeft x)=cubicSymbol c r*g x := by
    dsimp only [f,g]
    rw [hw]
    have he : Ideal.Quotient.mk (modulus c) h*(u.mulLeft x)=
        Ideal.Quotient.mk (modulus c) (h*r)*x := by
      change Ideal.Quotient.mk (modulus c) h*((u:Residues c)*x)=_
      rw [hu,map_mul]
      ring
    rw [he]
    ring
  have hs : (∑ x : Residues c, f x)=cubicSymbol c r*∑ x : Residues c, g x := by
    rw [← Equiv.sum_comp u.mulLeft f]
    simp_rw [hp]
    rw [Finset.mul_sum]
  have hi : star (cubicSymbol c r)*cubicSymbol c r=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hc hcr]
    norm_num
  change (∑' x : Residues c, g x)=star (cubicSymbol c r)*∑' x : Residues c, f x
  rw [tsum_fintype,tsum_fintype,hs,← mul_assoc,hi,one_mul]

theorem cubicThetaSymbolFourier_lambda_cube {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) :
    cubicThetaSymbolFourier c (primary_ne_zero hc) (lambdaE^3*h)=
      cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  rw [mul_comm (lambdaE^3) h,
    cubicThetaSymbolFourier_mul hc (primary_coprime_lambda hc).pow_right,
    cubicSymbol_pow_upper hc,cubicSymbol_cube_of_isCoprime hc lambdaE
      (primary_coprime_lambda hc),star_one,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedConstantGauss (c : Eisenstein) : ℂ :=
  ∑' x : Residues c, cubicSymbol c (3*residueRepresentative c x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedConstantWeight (s : ℂ) (c : Eisenstein) : ℂ :=
  if primary c then cubicThetaInvertedConstantGauss c*(norm c:ℂ)^(-s) else 0

def cubicThetaInvertedConstantDirichlet (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, cubicThetaInvertedConstantWeight s c

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMissingClass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma lambda_dvd_three : lambdaE ∣ (3:Eisenstein) := by
  refine ⟨-lambdaE,?_⟩
  rw [mul_neg,← pow_two,lambdaE_sq]
  ring

lemma lambda_not_dvd_four : ¬lambdaE ∣ (4:Eisenstein) := by
  intro hd
  have hp : primary (4:Eisenstein) := ⟨1,by ring⟩
  exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hp).isRelPrime hd dvd_rfl)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedLowFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaRamifiedTrace (h : Eisenstein) : ℂ :=
  residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h)+
    residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (-h))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTrace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier trace in the ramified correction never vanishes.
It equals two on primary frequencies and on lambda cubes. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPhase_cube (h : Eisenstein) :
    (residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h))^3=1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  have hz : (3:ℕ) • Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0 := by
    rw [← map_nsmul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨h,by simp [nsmul_eq_mul]⟩
  rw [hz,AddChar.map_zero_eq_one]

theorem cubicThetaRamifiedTrace_ne_zero (h : Eisenstein) :
    cubicThetaRamifiedTrace h≠0 := by
  intro hz
  have hp := cubicThetaRamifiedPhase_cube h
  have hn := cubicThetaRamifiedPhase_cube (-h)
  unfold cubicThetaRamifiedTrace at hz
  have he := eq_neg_of_add_eq_zero_left hz
  rw [he] at hp
  rw [neg_pow,hn] at hp
  norm_num at hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFiniteFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedGaussCoefficient (c h : Eisenstein) : ℂ :=
  ∑' x : Residues c, cubicSymbol c (3*residueRepresentative c x)*
    (Real.fourierChar (tracePair (residueRepresentative c x:ℂ)
      ((h:ℂ)/((c:ℂ)*traceLambda))):ℂ)

lemma cubicThetaInvertedGaussCoefficient_factor {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) :
    cubicThetaInvertedGaussCoefficient c h=
      cubicSymbol c 3*cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  unfold cubicThetaInvertedGaussCoefficient cubicThetaSymbolFourier
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  rw [cubicSymbol_mul_upper hc,residueFourierChar_mk_mul]
  ring

lemma cubicThetaInvertedGaussCoefficient_zero (c : Eisenstein) :
    cubicThetaInvertedGaussCoefficient c 0=cubicThetaInvertedConstantGauss c := by
  simp [cubicThetaInvertedGaussCoefficient,cubicThetaInvertedConstantGauss,tracePair]

lemma cubicThetaSymbol_three {c : Eisenstein} (hc : primary c) :
    cubicSymbol c 3=(cubicSymbol c lambdaE)^2 := by
  have he := cubicSymbol_pow_upper hc lambdaE 2
  rw [lambdaE_sq,cubicSymbol_neg hc] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson summation for the actual inverted rows d=3a, with their
finite cubic character and the unchanged frequency lattice. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaInvertedGaussianRow (c : Eisenstein) (z : ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, cubicSymbol c (3*a)*
    (Real.exp (-t*‖z+3*(a:ℂ)/(c:ℂ)‖^2):ℂ)

lemma cubicThetaInvertedResidueWeight_mk {c : Eisenstein} (hc : primary c) (a : Eisenstein) :
    cubicSymbol c (3*residueRepresentative c (Ideal.Quotient.mk (modulus c) a))=
      cubicSymbol c (3*a) := by
  rw [cubicSymbol_mul_upper hc,cubicSymbol_mul_upper hc]
  congr 1
  exact cubicSymbol_congr (residueRepresentative_spec c _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedRowEquiv : CubicThetaBottomRow ≃ CubicThetaInvertedRow where
  toFun r := ⟨r.d,-r.c,r.d_primary,dvd_neg.mpr r.c_three,r.coprime.symm.neg_right⟩
  invFun r := ⟨-r.d,r.c,dvd_neg.mpr r.d_three,r.c_primary,r.coprime.neg_right.symm⟩
  left_inv r := by ext <;> simp
  right_inv r := by ext <;> simp

theorem cubicThetaBottomRow_height_full (r : CubicThetaBottomRow)
    (g : SL(2,Eisenstein)) {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height (cubicThetaMobius (cubicThetaFullComplex g) p)=
      p.2/(Complex.normSq ((((r.c*g 0 0+r.d*g 1 0):Eisenstein):ℂ)*p.1+
        ((r.c*g 0 1+r.d*g 1 1):Eisenstein))+
        norm (r.c*g 0 0+r.d*g 1 0)*p.2^2) := by
  have hc : r.completion.val 1 0=r.c := congrArg CubicThetaBottomRow.c r.completion_row
  have hd : r.completion.val 1 1=r.d := congrArg CubicThetaBottomRow.d r.completion_row
  have hmap : cubicThetaPrincipalComplex r.completion =
      cubicThetaFullComplex r.completion.val := by
    ext i j
    rfl
  calc
    _ = (cubicThetaMobius (cubicThetaFullComplex r.completion.val)
        (cubicThetaMobius (cubicThetaFullComplex g) p)).2 := by
      simpa only [r.completion_row,hmap] using cubicThetaBottomRow_height r.completion
        (cubicThetaMobius (cubicThetaFullComplex g) p)
    _ = (cubicThetaMobius (cubicThetaFullComplex (r.completion.val*g)) p).2 := by
      rw [map_mul,cubicThetaMobius_comp _ _ hp]
    _ = _ := by
      change p.2/(Complex.normSq ((((r.completion.val*g) 1 0:Eisenstein):ℂ)*p.1+
        (((r.completion.val*g) 1 1:Eisenstein):ℂ))+
        norm ((r.completion.val*g) 1 0)*p.2^2)=_
      simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hc,hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedAdmissible (cd : Eisenstein × Eisenstein) : Prop :=
  primary cd.1 ∧ (3:Eisenstein)∣cd.2 ∧ IsCoprime cd.1 cd.2

def cubicThetaInvertedPairEquiv :
    CubicThetaInvertedRow ≃ {cd // cubicThetaInvertedAdmissible cd} where
  toFun r := ⟨(r.c,r.d),r.c_primary,r.d_three,r.coprime⟩
  invFun cd := ⟨cd.val.1,cd.val.2,cd.property.1,cd.property.2.1,cd.property.2.2⟩
  left_inv r := by cases r; rfl
  right_inv cd := by apply Subtype.ext; rfl

def cubicThetaInvertedGridTerm (cd : Eisenstein × Eisenstein)
    (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if cubicThetaInvertedAdmissible cd then
    cubicSymbol cd.1 cd.2*
      ((p.2/(Complex.normSq ((cd.1:ℂ)*p.1+cd.2)+norm cd.1*p.2^2):ℝ):ℂ)^s
  else 0

lemma cubicThetaInvertedGridTerm_triple {c : Eisenstein} (hc : primary c)
    (a : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaInvertedGridTerm (c,3*a) p s=
      cubicSymbol c (3*a)*
        ((p.2/(Complex.normSq ((c:ℂ)*p.1+3*(a:ℂ))+norm c*p.2^2):ℝ):ℂ)^s := by
  by_cases hcop : IsCoprime c (3*a)
  · have h3 : ((3:Eisenstein):ℂ)=(3:ℂ) := rfl
    simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,hc,hcop,h3]
  · simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,hcop,
      cubicSymbol_eq_zero_of_not_isCoprime hc hcop]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedRowSeries (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' a : Eisenstein, cubicSymbol c (3*a)*
    ((p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2):ℝ):ℂ)^s

lemma cubicThetaInvertedGrid_row {c : Eisenstein} (hc : primary c)
    (p : ℂ × ℝ) (s : ℂ) :
    (∑' d : Eisenstein, cubicThetaInvertedGridTerm (c,d) p s)=cubicThetaInvertedRowSeries c p s := by
  have hi : Function.Injective (fun a : Eisenstein => 3*a) :=
    fun a b h => mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) h
  have hs : Function.support (fun d => cubicThetaInvertedGridTerm (c,d) p s) ⊆
      Set.range (fun a : Eisenstein => 3*a) := by
    intro d hd
    by_cases ht : (3:Eisenstein)∣d
    · obtain ⟨a,ha⟩ := ht
      exact ⟨a,ha.symm⟩
    · exact False.elim (hd (by simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,ht]))
  rw [←hi.tsum_eq hs]
  unfold cubicThetaInvertedRowSeries
  apply tsum_congr
  intro a
  exact cubicThetaInvertedGridTerm_triple hc a p s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedRowFourierCoefficient (c : Eisenstein) (z : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaInvertedGaussCoefficient c h*
    (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full actual inverted Eisenstein series and its zero-frequency
row term. The scalar continuation retains the exact archimedean factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaInverted_zero_row_factor {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1 < s.re)
    {c : Eisenstein} (hc : primary c) :
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaInvertedGaussCoefficient c 0*
        (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*
        (cubicThetaInvertedConstantGauss c*(norm c:ℂ)^(-s)) := by
  have hs0 : s-1≠0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have hg := Complex.Gamma_add_one (s-1) hs0
  rw [sub_add_cancel] at hg
  rw [cubicThetaDualHeat_zero_integral hv hs,hg,cubicThetaInvertedGaussCoefficient_zero]
  have hp := cubicTheta_zero_height_factor hv (norm_pos_of_ne_zero (primary_ne_zero hc)) s
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  calc
    _ = ((v/norm c:ℝ):ℂ)^s*((v^2:ℝ):ℂ)^(1-s)*
        (2*Real.pi/(9*Real.sqrt 3):ℂ)*cubicThetaInvertedConstantGauss c/(s-1) := by
      field_simp
    _ = _ := by rw [hp]; ring

def cubicThetaInvertedConstantMode (v : ℝ) (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, if primary c then
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaInvertedGaussCoefficient c 0*
        (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s else 0

theorem cubicThetaInvertedConstantMode_eq {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaInvertedConstantMode v s=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*cubicThetaInvertedConstantDirichlet s := by
  unfold cubicThetaInvertedConstantMode cubicThetaInvertedConstantDirichlet
  rw [←tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · simp only [cubicThetaInvertedConstantWeight,ite_eq_left hc]
    exact cubicThetaInverted_zero_row_factor hv hs hc
  · simp [hc,cubicThetaInvertedConstantWeight]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaInvertedFrequencyTerm (s : ℂ) (h c : Eisenstein) : ℂ :=
  if primary c then cubicThetaInvertedGaussCoefficient c h*(norm c:ℂ)^(-s) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C1 functions on the hyperbolic upper half-space, used only to
transport the actual gradients through the finite Hecke correspondence. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPointFunction_apply (F : C(CubicThetaPoint,ℂ))
    {y : ℂ × ℝ} (hy : 0<y.2) : cubicThetaPointFunction F y=F ⟨y,hy⟩ := by
  apply congrArg F
  apply Subtype.ext
  have hy' : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  exact cubicThetaPointInclusion.right_inv hy'

def cubicThetaPointC1Pullback (g : SL(2,ℂ)) : cubicThetaPointC1 →ₗ[ℂ] cubicThetaPointC1 where
  toFun F := ⟨⟨fun x => F.val (g • x),F.val.continuous.comp (continuous_const_smul g)⟩,by
    have hm : ContDiffOn ℝ 1 (cubicThetaMobius g) {y : ℂ × ℝ | 0<y.2} :=
      fun y hy => ((cubicThetaMobius_contDiffAt g hy).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffWithinAt
    apply (F.property.comp hm (fun y hy => cubicThetaMobius_height_pos g hy)).congr
    intro y hy
    rw [cubicThetaPointFunction_apply _ hy]
    change F.val (⟨cubicThetaMobius g y,cubicThetaMobius_height_pos g hy⟩:CubicThetaPoint)=
      cubicThetaPointFunction F.val (cubicThetaMobius g y)
    exact (cubicThetaPointFunction_apply F.val (cubicThetaMobius_height_pos g hy)).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cubicThetaPointC1Pullback_function (g : SL(2,ℂ)) (F : cubicThetaPointC1)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPointFunction (cubicThetaPointC1Pullback g F).val y=
      cubicThetaPointFunction F.val (cubicThetaMobius g y) := by
  rw [cubicThetaPointFunction_apply _ hy,
    cubicThetaPointFunction_apply _ (cubicThetaMobius_height_pos g hy)]
  rfl

lemma cubicThetaPointC1Pullback_gradient_norm (g : SL(2,ℂ))
    (F : cubicThetaPointC1) (x : CubicThetaPoint) :
    ‖cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback g F)‖=
      ‖cubicThetaPointC1Gradient (g • x) F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPointC1Gradient_norm_sq,cubicThetaPointC1Gradient_norm_sq]
  have he : cubicThetaPointFunction (cubicThetaPointC1Pullback g F).val=ᶠ[𝓝 x.val]
      (fun y => cubicThetaPointFunction F.val (cubicThetaMobius g y)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    exact cubicThetaPointC1Pullback_function g F hy
  have hder := he.fderiv_eq (𝕜:=ℝ)
  change x.val.2^2*cubicThetaFunctionEnergy _ x.val=
    (cubicThetaMobius g x.val).2^2*cubicThetaFunctionEnergy _ (cubicThetaMobius g x.val)
  unfold cubicThetaFunctionEnergy
  rw [hder]
  exact cubicThetaFunctionEnergy_mobius _ g x.property
    (cubicThetaPointC1_differentiable F (cubicThetaMobius_height_pos g x.property))

theorem cubicThetaPointC1Pullback_gradient_pair (g : SL(2,ℂ))
    (F G : cubicThetaPointC1) (x : CubicThetaPoint) :
    inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback g F))
      (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback g G))=
    inner ℂ (cubicThetaPointC1Gradient (g • x) F) (cubicThetaPointC1Gradient (g • x) G) := by
  let : AddCommGroup cubicThetaPointC1 := Module.addCommMonoidToAddCommGroup ℂ
  let L : cubicThetaPointC1 →ₗ[ℂ] CubicThetaGradient :=
    (cubicThetaPointC1Gradient x).comp (cubicThetaPointC1Pullback g)
  let M : cubicThetaPointC1 →ₗ[ℂ] CubicThetaGradient := cubicThetaPointC1Gradient (g • x)
  have hn (F : cubicThetaPointC1) : ‖L F‖=‖M F‖ :=
    cubicThetaPointC1Pullback_gradient_norm g F x
  change inner ℂ (L F) (L G)=inner ℂ (M F) (M G)
  exact cubicThetaLinear_inner_of_norm_eq L M hn F G

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDilationCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinates and the exact smaller cusp period of the
prime-dilated arithmetic Eisenstein family. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaMobius_primeDilation {p : Eisenstein} (hp : p≠0) (z : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaPrimeDilation hp) z=
      ((p:ℂ)*z.1,‖(p:ℂ)‖*z.2) := by
  let q := cubicThetaPrimeSquareRoot p
  have hq : q≠0 := cubicThetaPrimeSquareRoot_ne_zero hp
  have hs : q^2=(p:ℂ) := cubicThetaPrimeSquareRoot_sq p
  have hqs : star q≠0 := star_ne_zero.mpr hq
  have hn : Complex.normSq q=‖(p:ℂ)‖ := by
    rw [Complex.normSq_eq_norm_sq]
    simpa only [norm_pow] using congrArg (fun z : ℂ => ‖z‖) hs
  have hnc : (Complex.normSq q:ℂ)=q*star q := (Complex.mul_conj q).symm
  have hden : cubicThetaMobiusDenominator (cubicThetaPrimeDilation hp) z=
      (Complex.normSq q)⁻¹ := by
    simp [cubicThetaMobiusDenominator,cubicThetaPrimeDilation,q]
  have hnum : cubicThetaMobiusNumerator (cubicThetaPrimeDilation hp) z=
      q*z.1*star (q⁻¹) := by
    simp [cubicThetaMobiusNumerator,cubicThetaPrimeDilation,q]
  apply Prod.ext
  · change cubicThetaMobiusNumerator _ z/(cubicThetaMobiusDenominator _ z:ℂ)=(p:ℂ)*z.1
    rw [hnum,hden,Complex.ofReal_inv,hnc,star_inv₀,←hs]
    field_simp
  · change z.2/cubicThetaMobiusDenominator _ z=_
    rw [hden,div_inv_eq_mul,hn]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAtkinConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime Atkin involution on the actual arithmetic subgroup. Its
cubic twist disappears on the kernel of the diagonal character. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCharacterKernel {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup (cubicThetaPrimeIwahori p) := (cubicThetaPrimeIwahoriCharacter p hp).ker

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeOppositeBranch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary chart contributes the missing nonunit translations
in the lowest branch, with complete cancellation of its two multipliers. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeInverse_branchPoint {p : Eisenstein} (hp : primaryPrime p)
    (m : Eisenstein) (x : CubicThetaPoint) :
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
      (cubicThetaPrincipalTranslation m • x)=cubicThetaPrimeCubeBranchPoint hp 0 m x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  have hp3norm : ‖((p^3:Eisenstein):ℂ)‖=‖(p:ℂ)‖^3 := by
    rw [show ((p^3:Eisenstein):ℂ)=(p:ℂ)^3 from
      map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3,norm_pow]
  have he : D • cubicThetaPrimeCubeBranchPoint hp 0 m x=cubicThetaPrincipalTranslation m • x := by
    apply Subtype.ext
    change cubicThetaMobius D (cubicThetaPrimeCubeBranchPoint hp 0 m x).val=
      cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation m)) x.val
    rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
    change cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) _=_
    rw [cubicThetaMobius_primeDilation]
    apply Prod.ext
    · change ((p^3:Eisenstein):ℂ)*
        ((p:ℂ)^0/(p:ℂ)^(3-0)*x.val.1+((3*m:Eisenstein):ℂ)/(p:ℂ)^(3-0))=
          x.val.1+((3*m:Eisenstein):ℂ)
      push_cast
      field_simp
    · change ‖((p^3:Eisenstein):ℂ)‖*
        ((‖(p:ℂ)‖^0/‖(p:ℂ)‖^(3-0))*x.val.2)=x.val.2
      rw [hp3norm]
      simp [hn]
  have hi := congrArg (fun y : CubicThetaPoint => D⁻¹ • y) he
  simpa only [smul_smul,inv_mul_cancel,one_smul] using hi.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeUnitPermutation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite unit permutation produced by triangularization:
the residue of the new period-three translation is (9n)^{-1}. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeNineUnit {p : Eisenstein} (hp : primaryPrime p) (k : Fin 3) :
    (Residues (p^(3-k.val)))ˣ := by
  have h9 : IsCoprime (p^(3-k.val)) (9:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCubeReduction_primary hp k)).pow_right
      (n := 2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  exact (residue_isUnit_of_isCoprime h9).unit

lemma cubicThetaPrimeCubeNineUnit_value {p : Eisenstein} (hp : primaryPrime p) (k : Fin 3) :
    (cubicThetaPrimeCubeNineUnit hp k : Residues (p^(3-k.val)))=
      Ideal.Quotient.mk (modulus (p^(3-k.val))) 9 := IsUnit.unit_spec _

def cubicThetaPrimeCubeUnitPermutation {p : Eisenstein} (hp : primaryPrime p) (k : Fin 3) :
    (Residues (p^(3-k.val)))ˣ ≃ (Residues (p^(3-k.val)))ˣ where
  toFun u := (cubicThetaPrimeCubeNineUnit hp k*u)⁻¹
  invFun v := (cubicThetaPrimeCubeNineUnit hp k)⁻¹*v⁻¹
  left_inv u := by simp
  right_inv v := by simp

lemma cubicThetaPrimeCubeUnitRepresentative_not_dvd {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (u : (Residues (p^(3-k.val)))ˣ) :
    ¬p∣residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))) := by
  apply hp.2.coprime_iff_not_dvd.mp
  have hpu : IsCoprime (p^(3-k.val))
      (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) := by
    apply isCoprime_of_residue_isUnit
    rw [residueRepresentative_spec]
    exact u.isUnit
  exact hpu.of_isCoprime_of_dvd_left (dvd_pow_self p (by have := k.isLt; omega))

theorem cubicThetaPrimeCubeUnitTranslation_residue {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (u : (Residues (p^(3-k.val)))ˣ) :
    Ideal.Quotient.mk (modulus (p^(3-k.val)))
      (cubicThetaPrimeCubeReductionTranslation hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))))
        (cubicThetaPrimeCubeUnitRepresentative_not_dvd hp k u))=
      (cubicThetaPrimeCubeUnitPermutation hp k u : Residues (p^(3-k.val))) := by
  rw [cubicThetaPrimeCubeReductionTranslation_residue]
  have he : cubicThetaPrimeCubeReductionTranslationUnit hp k
      (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))))
      (cubicThetaPrimeCubeUnitRepresentative_not_dvd hp k u)=cubicThetaPrimeCubeNineUnit hp k*u := by
    apply Units.ext
    change Ideal.Quotient.mk (modulus (p^(3-k.val)))
      (9*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))))=_
    rw [map_mul,residueRepresentative_spec,Units.val_mul,cubicThetaPrimeCubeNineUnit_value]
  rw [he]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeResidueStep
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One step in the finite three-level valuation partition used by the
cubed-prime trace. Multiplication by p parametrizes the nonunits exactly. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeNonunitPart (p : Eisenstein) (j : Fin 3) :=
  {r : Residues (p^(j.val+1)) // p∣residueRepresentative (p^(j.val+1)) r}

lemma cubicThetaPrimeCubeResidueStep_divisible {p x : Eisenstein} (j : Fin 3) (hx : p∣x) :
    p∣residueRepresentative (p^(j.val+1)) (Ideal.Quotient.mk (modulus (p^(j.val+1))) x) := by
  have he := residueRepresentative_spec (p^(j.val+1)) (Ideal.Quotient.mk (modulus (p^(j.val+1))) x)
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have ht := dvd_add ((dvd_pow_self p (Nat.succ_ne_zero j.val)).trans hd) hx
  simpa only [sub_add_cancel] using ht

def cubicThetaPrimeCubeResidueStepMap (p : Eisenstein) (j : Fin 3)
    (r : Residues (p^j.val)) : cubicThetaPrimeCubeNonunitPart p j :=
  ⟨Ideal.Quotient.mk (modulus (p^(j.val+1))) (p*residueRepresentative (p^j.val) r),
    cubicThetaPrimeCubeResidueStep_divisible j (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeCubeResidueStepMap_injective {p : Eisenstein} (hp : p≠0) (j : Fin 3) :
    Function.Injective (cubicThetaPrimeCubeResidueStepMap p j) := by
  intro r s h
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (modulus (p^(j.val+1))) (p*residueRepresentative (p^j.val) r)=
    Ideal.Quotient.mk (modulus (p^(j.val+1))) (p*residueRepresentative (p^j.val) s) at he
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hd' : p*p^j.val ∣ p*(residueRepresentative (p^j.val) r-residueRepresentative (p^j.val) s) := by
    first | (convert hd using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hd.trans (le_of_eq (by ring)))
  rw [mul_dvd_mul_iff_left hp] at hd'
  simpa only [residueRepresentative_spec] using residue_eq_of_dvd_sub hd'

lemma cubicThetaPrimeCubeResidueStepMap_surjective (p : Eisenstein) (j : Fin 3) :
    Function.Surjective (cubicThetaPrimeCubeResidueStepMap p j) := by
  intro r
  obtain ⟨m,hm⟩ := r.property
  refine ⟨Ideal.Quotient.mk (modulus (p^j.val)) m,?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (modulus (p^(j.val+1)))
    (p*residueRepresentative (p^j.val) (Ideal.Quotient.mk (modulus (p^j.val)) m))=r.val
  have hd : p^j.val ∣ residueRepresentative (p^j.val) (Ideal.Quotient.mk (modulus (p^j.val)) m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
  have he : p^(j.val+1) ∣ p*residueRepresentative (p^j.val)
      (Ideal.Quotient.mk (modulus (p^j.val)) m)-p*m := by
    first | (convert mul_dvd_mul_left p hd using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_dvd_mul_left p hd).trans (le_of_eq (by ring)))
  exact (residue_eq_of_dvd_sub he).trans (by rw [←hm,residueRepresentative_spec])

def cubicThetaPrimeCubeResidueStepEquiv {p : Eisenstein} (hp : p≠0) (j : Fin 3) :
    Residues (p^j.val) ≃ cubicThetaPrimeCubeNonunitPart p j :=
  Equiv.ofBijective (cubicThetaPrimeCubeResidueStepMap p j)
    ⟨cubicThetaPrimeCubeResidueStepMap_injective hp j,
      cubicThetaPrimeCubeResidueStepMap_surjective p j⟩

def cubicThetaPrimeCubeResidueSplit {p : Eisenstein} (hp : primaryPrime p) (j : Fin 3) :
    ((Residues (p^(j.val+1)))ˣ ⊕ Residues (p^j.val)) ≃ Residues (p^(j.val+1)) := by
  classical
  let e : cubicThetaPrimeCubeNonunitPart p j ≃
      {r : Residues (p^(j.val+1)) // ¬IsUnit r} :=
    Equiv.subtypeEquivRight (fun r => ((cubicTheta_primePower_nonunit_iff hp.2 j.val r).trans
      (cubicTheta_residueReduction_eq_zero_iff _ r)).symm)
  exact (Equiv.sumCongr (cubicThetaUnitsEquivIsUnit _) ((cubicThetaPrimeCubeResidueStepEquiv hp.2.ne_zero j).trans e)).trans
    (Equiv.sumCompl IsUnit)

theorem cubicThetaPrimeCubeResidueSum_split {p : Eisenstein} (hp : primaryPrime p)
    (j : Fin 3) (f : Residues (p^(j.val+1)) → ℂ) :
    (∑' r, f r)=(∑' u : (Residues (p^(j.val+1)))ˣ, f u)+
      ∑' r : Residues (p^j.val), f (Ideal.Quotient.mk (modulus (p^(j.val+1)))
        (p*residueRepresentative (p^j.val) r)) := by
  let : Finite (Residues (p^j.val)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Finite (Residues (p^(j.val+1))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  rw [←(cubicThetaPrimeCubeResidueSplit hp j).tsum_eq,
    Summable.tsum_sum Summable.of_finite Summable.of_finite]
  rfl

lemma cubicThetaPrimeCubeResidueSum_three {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues (p^3) → ℂ) :
    (∑' r, f r)=(∑' u : (Residues (p^3))ˣ, f u)+
      ∑' r : Residues (p^2), f (Ideal.Quotient.mk (modulus (p^3))
        (p*residueRepresentative (p^2) r)) := by
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨2,by decide⟩ : Fin 3)
  simp only [Nat.reduceAdd] at hs
  exact hs f

lemma cubicThetaPrimeCubeResidueSum_two {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues (p^2) → ℂ) :
    (∑' r, f r)=(∑' u : (Residues (p^2))ˣ, f u)+
      ∑' r : Residues p, f (Ideal.Quotient.mk (modulus (p^2))
        (p*residueRepresentative p r)) := by
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨1,by decide⟩ : Fin 3)
  simp only [Nat.reduceAdd] at hs
  rw [show p^(1:ℕ)=p from pow_one p] at hs
  exact hs f

lemma cubicThetaPrimeCubeResidueSum_one {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues p → ℂ) :
    (∑' r, f r)=(∑' u : (Residues p)ˣ, f u)+
      ∑' r : Residues 1, f (Ideal.Quotient.mk (modulus p)
        (p*residueRepresentative 1 r)) := by
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨0,by decide⟩ : Fin 3)
  simp only [Nat.reduceAdd] at hs
  rw [show p^(1:ℕ)=p from pow_one p,show p^(0:ℕ)=1 from pow_zero p] at hs
  exact hs f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeResidueComplement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit and complementary chart parameters exhaust the residue
ring modulo p^3 without overlap or multiplicity. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeResidueComplement_sum {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues (p^3) → ℂ) :
    (∑' r : Residues (p^3), f r)=
      (∑' u : (Residues (p^3))ˣ, f u)+
      ∑' r : cubicThetaPrimeCubeUpperParameter p, f r.val := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Finite (cubicThetaPrimeCubeUpperParameter p) := by
    unfold cubicThetaPrimeCubeUpperParameter
    infer_instance
  let e : cubicThetaPrimeCubeUpperParameter p ≃ {r : Residues (p^3) // ¬IsUnit r} :=
    Equiv.subtypeEquivRight (fun r => ((cubicTheta_primePower_nonunit_iff hp.2 2 r).trans
      (cubicTheta_residueReduction_eq_zero_iff _ r)).symm)
  let E : ((Residues (p^3))ˣ ⊕ cubicThetaPrimeCubeUpperParameter p) ≃ Residues (p^3) :=
    (Equiv.sumCongr (cubicThetaUnitsEquivIsUnit _) e).trans (Equiv.sumCompl IsUnit)
  rw [←E.tsum_eq,Summable.tsum_sum Summable.of_finite Summable.of_finite]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeLowerValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower-chart value is a genuine function modulo p^3. Its scaled
versions descend to the smaller residue rings used in the valuation split. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrincipalLower_add (m n : Eisenstein) :
    cubicThetaPrincipalLower (m+n)=cubicThetaPrincipalLower m*cubicThetaPrincipalLower n := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1,0;3*(m+n),1] : Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,0;3*m,1]*!![1,0;3*n,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  ring

lemma cubicThetaPrincipalLower_zero : cubicThetaPrincipalLower 0=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1,0;3*0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)=1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeValuationSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal lower-chart sum split into its three exact prime
valuations and its zero class. All reductions preserve the sharp modulus. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaResiduesOne_tsum (c : ℂ) : (∑' _ : Residues 1,c)=c := by
  let : Finite (Residues (1:Eisenstein)) := finite_residues one_ne_zero
  let : Fintype (Residues (1:Eisenstein)) := Fintype.ofFinite _
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,
    residues_card one_ne_zero,normNat_one,one_nsmul]

lemma cubicThetaPrimeCubePeriodic_sum {p : Eisenstein} (hp : primaryPrime p)
    (G : Eisenstein → ℂ) (hG : ∀ m n, p^3∣m-n → G m=G n) :
    (∑' r : Residues (p^3), G (residueRepresentative (p^3) r))=
      G 0+
      (∑' u : (Residues (p^3))ˣ, G (residueRepresentative (p^3) (u : Residues (p^3))))+
      (∑' u : (Residues (p^2))ˣ, G (p*residueRepresentative (p^2) (u : Residues (p^2))))+
      (∑' u : (Residues p)ˣ, G (p^2*residueRepresentative p (u : Residues p))) := by
  have hc0 (m : Eisenstein) :
      G (residueRepresentative (p^3) (Ideal.Quotient.mk (modulus (p^3)) m))=G m := by
    apply hG
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
  have hc1 (m : Eisenstein) :
      G (p*residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m))=G (p*m) := by
    apply hG
    have hd : p^2∣residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m)-m :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
    first | (convert mul_dvd_mul_left p hd using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_dvd_mul_left p hd).trans (le_of_eq (by ring)))
  have hc2 (m : Eisenstein) :
      G (p^2*residueRepresentative p (Ideal.Quotient.mk (modulus p) m))=G (p^2*m) := by
    apply hG
    have hd : p∣residueRepresentative p (Ideal.Quotient.mk (modulus p) m)-m :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
    first | (convert mul_dvd_mul_left (p^2) hd using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_dvd_mul_left (p^2) hd).trans (le_of_eq (by ring)))
  have hz (m : Eisenstein) : G (p^3*m)=G 0 := by
    apply hG
    simp only [sub_zero]
    exact dvd_mul_right _ _
  have h3 := cubicThetaPrimeCubeResidueSum_three hp
    (fun r : Residues (p^3) => G (residueRepresentative (p^3) r))
  simp_rw [hc0] at h3
  have h2 := cubicThetaPrimeCubeResidueSum_two hp
    (fun r : Residues (p^2) => G (p*residueRepresentative (p^2) r))
  simp_rw [hc1] at h2
  have h2' : (∑' r : Residues (p^2),G (p*residueRepresentative (p^2) r))=
      (∑' u : (Residues (p^2))ˣ,G (p*residueRepresentative (p^2) (u : Residues (p^2))))+
      ∑' r : Residues p,G (p^2*residueRepresentative p r) := by
    simpa only [pow_one,pow_two,mul_assoc] using h2
  have h1 := cubicThetaPrimeCubeResidueSum_one hp
    (fun r : Residues p => G (p^2*residueRepresentative p r))
  simp_rw [hc2] at h1
  have h1' : (∑' r : Residues p,G (p^2*residueRepresentative p r))=
      (∑' u : (Residues p)ˣ,G (p^2*residueRepresentative p (u : Residues p)))+G 0 := by
    have he (m : Eisenstein) : G (p^2*(p*m))=G 0 := by
      rw [show p^2*(p*m)=p^3*m by ring]
      exact hz m
    simp_rw [he] at h1
    simpa only [pow_zero,cubicThetaResiduesOne_tsum] using h1
  rw [h3,h2',h1']
  ac_rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime Atkin involution preserves the actual integral norm
on its finite arithmetic covering, before passing to a completion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSection_norm_invariant (p : Eisenstein)
    (F : cubicThetaPrimeCubeSections p) (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
    ‖F.val (g • x)‖^2=‖F.val x‖^2 := by
  change ‖F.val (g.val • x)‖^2=‖F.val x‖^2
  rw [F.property,norm_mul,cubicThetaKubotaValue_norm,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeDegree
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact degree of the cubed-prime correspondence. The second chart
is explicitly identified with the residue ring modulo p^2. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeUpperParameterMap (p : Eisenstein) (r : Residues (p^2)) :
    cubicThetaPrimeCubeUpperParameter p :=
  ⟨Ideal.Quotient.mk (modulus (p^3)) (p*residueRepresentative (p^2) r),
    cubicThetaPrimeCubeRepresentative_dvd (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeCubeUpperParameterMap_injective {p : Eisenstein} (hp : p≠0) :
    Function.Injective (cubicThetaPrimeCubeUpperParameterMap p) := by
  intro r s h
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (modulus (p^3)) (p*residueRepresentative (p^2) r)=
    Ideal.Quotient.mk (modulus (p^3)) (p*residueRepresentative (p^2) s) at he
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hd' : p*p^2 ∣ p*(residueRepresentative (p^2) r-residueRepresentative (p^2) s) := by
    first | (convert hd using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hd.trans (le_of_eq (by ring)))
  rw [mul_dvd_mul_iff_left hp] at hd'
  simpa only [residueRepresentative_spec] using residue_eq_of_dvd_sub hd'

lemma cubicThetaPrimeCubeUpperParameterMap_surjective (p : Eisenstein) :
    Function.Surjective (cubicThetaPrimeCubeUpperParameterMap p) := by
  intro r
  obtain ⟨m,hm⟩ := r.property
  refine ⟨Ideal.Quotient.mk (modulus (p^2)) m,?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (modulus (p^3))
    (p*residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m))=r.val
  have hd : p^2 ∣ residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec _ _))
  have he : p^3 ∣ p*residueRepresentative (p^2) (Ideal.Quotient.mk (modulus (p^2)) m)-p*m := by
    first | (convert mul_dvd_mul_left p hd using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_dvd_mul_left p hd).trans (le_of_eq (by ring)))
  exact (residue_eq_of_dvd_sub he).trans (by rw [←hm,residueRepresentative_spec])

def cubicThetaPrimeCubeUpperParameterEquiv {p : Eisenstein} (hp : p≠0) :
    Residues (p^2) ≃ cubicThetaPrimeCubeUpperParameter p :=
  Equiv.ofBijective (cubicThetaPrimeCubeUpperParameterMap p)
    ⟨cubicThetaPrimeCubeUpperParameterMap_injective hp,
      cubicThetaPrimeCubeUpperParameterMap_surjective p⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkinPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime Atkin involution is self-adjoint for the actual
cover integral. No spectral or residue identity is assumed. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubePair_invariant {p : Eisenstein}
    (F G : cubicThetaPrimeCubeSections p) (g : cubicThetaPrimeIwahori (p^3))
    (x : CubicThetaPoint) :
    star (F.val (g • x))*G.val (g • x)=star (F.val x)*G.val x := by
  change star (F.val (g.val • x))*G.val (g.val • x)=_
  rw [F.property,G.property,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
      (star (F.val x)*G.val x) := by ring
    _ = _ := by rw [hk,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Pairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance of actual gradient pairings and the Atkin adjoint identity
on the finite cubed-prime cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1_covariance (F : cubicThetaPointC1)
    (g : cubicThetaPrincipalGroup)
    (hF : ∀ x,F.val (g • x)=cubicThetaKubotaValue g*F.val x) :
    cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) F=cubicThetaKubotaValue g • F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact hF

lemma cubicThetaPointC1Pair_covariance (F G : cubicThetaPointC1)
    (g : cubicThetaPrincipalGroup)
    (hF : ∀ x,F.val (g • x)=cubicThetaKubotaValue g*F.val x)
    (hG : ∀ x,G.val (g • x)=cubicThetaKubotaValue g*G.val x)
    (x : CubicThetaPoint) :
    inner ℂ (cubicThetaPointC1Gradient (g • x) G) (cubicThetaPointC1Gradient (g • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x F) := by
  have he := cubicThetaPointC1Pullback_gradient_pair (cubicThetaPrincipalComplex g) G F x
  rw [cubicThetaPointC1_covariance G g hG,cubicThetaPointC1_covariance F g hF,
    map_smul,map_smul,inner_smul_left,inner_smul_right] at he
  have hk : (starRingEnd ℂ) (cubicThetaKubotaValue g)*cubicThetaKubotaValue g=1 := by
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,cubicThetaKubotaValue_norm]
    norm_num
  rw [←mul_assoc,hk,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Fourier kernels of the cubed-prime branches.
Their additive support and exact multiplicity follow from finite inflation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubePrimeDivisor (p : Eisenstein) (k : Fin 3) : p∣p^(3-k.val) :=
  dvd_pow_self p (by have := k.isLt; omega)

def cubicThetaPrimeCubeFiniteGauss {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) : ℂ :=
  ∑' y : Residues (p^(3-k.val)),
    (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) y))^k.val*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*y)

theorem cubicThetaPrimeCubeFiniteGauss_reduction {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) :
    cubicThetaPrimeCubeFiniteGauss hp k (p^(2-k.val)*h)=
      (norm (p^(2-k.val)):ℂ)*cubicThetaPrimeFourier p hp k.val h := by
  have he : p^(3-k.val)=p*p^(2-k.val) := by
    rw [←pow_succ']
    congr 1
    have := k.isLt
    omega
  exact residueFourier_inflation_of_eq (pow_ne_zero _ hp.2.ne_zero) hp.2.ne_zero
    (pow_ne_zero (2-k.val) hp.2.ne_zero) he (cubicThetaPrimeCubePrimeDivisor p k)
    (fun y : Residues p => (cubicResidueChar p hp y)^k.val) h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFourierKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit-branch Fourier kernels, with their actual zero extension.
The passage from units to all residues is valid precisely for the two
positive cubic powers occurring in the Hecke correspondence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeCharacter_representative {p : Eisenstein}
    (hp : primaryPrime p) (k : Fin 3) (y : Residues (p^(3-k.val))) :
    cubicSymbol p (residueRepresentative (p^(3-k.val)) y)=
      cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) y) := by
  have he := congrArg (residueReduction (cubicThetaPrimeCubePrimeDivisor p k))
    (residueRepresentative_spec (p^(3-k.val)) y)
  rw [residueReduction_mk] at he
  rw [←he,cubicResidueChar_mk,cubicSymbol_prime hp]

lemma cubicThetaPrimeCubeCharacter_nonunit {p : Eisenstein}
    (hp : primaryPrime p) (k : Fin 3) (hk : k.val≠0)
    (m : Eisenstein) :
    (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k)
      (Ideal.Quotient.mk (modulus (p^(3-k.val))) (p*m))))^k.val=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [residueReduction_mk,map_mul]
  have hz : Ideal.Quotient.mk (modulus p) p=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl p))
  rw [hz,zero_mul,MulChar.map_zero,zero_pow hk]

lemma cubicThetaPrimeCubeGauss_units {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) :
    cubicThetaPrimeCubeFiniteGauss hp k h=
      ∑' u : (Residues (p^(3-k.val)))ˣ,
        (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) u))^k.val*
          residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
            (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*u) := by
  let f : Residues (p^(3-k.val)) → ℂ := fun y =>
    (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) y))^k.val*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*y)
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨2-k.val,by omega⟩ : Fin 3)
  have he : 2-k.val+1=3-k.val := by have := k.isLt; omega
  dsimp only at hs
  rw [he] at hs
  have ht := hs f
  have hz (r : Residues (p^(2-k.val))) :
      f (Ideal.Quotient.mk (modulus (p^(3-k.val)))
        (p*residueRepresentative (p^(2-k.val)) r))=0 := by
    dsimp only [f]
    rw [cubicThetaPrimeCubeCharacter_nonunit hp k hk,zero_mul]
  simp_rw [hz] at ht
  simpa only [f,cubicThetaPrimeCubeFiniteGauss,tsum_zero,add_zero] using ht

def cubicThetaPrimeCubeUnitFourier {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*u)

theorem cubicThetaPrimeCubeUnitFourier_eq {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) :
    cubicThetaPrimeCubeUnitFourier hp k h=
      (cubicSymbol p 3)^k.val*cubicThetaPrimeCubeFiniteGauss hp k h := by
  unfold cubicThetaPrimeCubeUnitFourier
  rw [cubicThetaPrimeCubeGauss_units hp k hk,←tsum_mul_left]
  apply tsum_congr
  intro u
  rw [cubicSymbol_mul_upper hp.1,mul_pow,cubicThetaPrimeCubeCharacter_representative hp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFourierOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit cubed-prime operator and its exact action on a single
horizontal mode. The formula keeps all frequency and height dilations. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeUnitFunctionSum {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      F (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) x)

def cubicThetaPrimeCubeBottomFunctionSum {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) : ℂ :=
  ∑' r : Residues (p^3),F (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r) x)

def cubicThetaPrimeCubeFunctionOperator {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) : ℂ :=
  F (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
    cubicThetaPrimeCubeBottomFunctionSum hp F x+
    cubicThetaPrimeCubeUnitFunctionSum hp 1 F x+
    cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩ : Fin 3) F x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeZeroMode
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the zero horizontal mode both nontrivial cubic characters cancel.
The remaining two height terms give the literal spherical multiplier. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeGauss_zeroFrequency {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) : cubicThetaPrimeCubeFiniteGauss hp k 0=0 := by
  have ht := cubicThetaPrimeCubeFiniteGauss_reduction hp k 0
  rw [mul_zero] at ht
  have hz : cubicThetaPrimeFourier p hp k.val 0=0 := by
    have he : k.val=1 ∨ k.val=2 := by have := k.isLt; omega
    rcases he with he | he
    · rw [he]
      simpa only [mul_zero] using cubicThetaPrimeFourier_one_multiple hp 0
    · rw [he]
      simpa only [mul_zero] using cubicThetaPrimeFourier_two_multiple hp 0
  rw [ht,hz,mul_zero]

lemma cubicThetaPrimeCubeUnitFourier_zeroFrequency {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) : cubicThetaPrimeCubeUnitFourier hp k 0=0 := by
  rw [cubicThetaPrimeCubeUnitFourier_eq hp k hk,cubicThetaPrimeCubeGauss_zeroFrequency hp k hk,
    mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeUnitMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second nontrivial character branch has zero constant mode for
any actual continuous periodic horizontal slice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeUnitFourier_zero_eq {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) : cubicThetaPrimeCubeUnitFourier hp k 0=
      ∑' u : (Residues (p^(3-k.val)))ˣ,
        (cubicSymbol p (3*residueRepresentative (p^(3-k.val))
          (u:Residues (p^(3-k.val)))))^k.val := by
  unfold cubicThetaPrimeCubeUnitFourier
  apply tsum_congr
  intro u
  rw [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one]

lemma cubicThetaPrimeCubeSquareCharacter_sum {p : Eisenstein} (hp : primaryPrime p) :
    (∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2)=0 := by
  have he := cubicThetaPrimeCubeUnitFourier_zeroFrequency hp (⟨2,by decide⟩:Fin 3) (by decide)
  rw [cubicThetaPrimeCubeUnitFourier_zero_eq] at he
  have hd : 3-(⟨2,by decide⟩:Fin 3).val=1 := rfl
  rw [hd,pow_one] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first character branch as an actual periodic finite sum. The
coefficient is extended by zero on nonunits before additive reindexing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeFirstTerm (p : Eisenstein) (f : ℂ → ℂ) (b : Eisenstein) (z : ℂ) : ℂ :=
  cubicSymbol p (3*b)*f (z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2)

def cubicThetaPrimeCubeFirstPeriodization (p : Eisenstein) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' r : Residues (p^2),cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2) r) z

lemma cubicThetaPrimeCubeFirstTerm_congr {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {b c : Eisenstein} (hbc : p^2∣b-c) (z : ℂ) :
    cubicThetaPrimeCubeFirstTerm p f b z=cubicThetaPrimeCubeFirstTerm p f c z := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hch : cubicSymbol p (3*b)=cubicSymbol p (3*c) := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    rw [←mul_sub]
    exact dvd_mul_of_dvd_right ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans hbc) 3
  obtain ⟨m,hm⟩ := hbc
  have hb : b=c+p^2*m := by linear_combination hm
  have hx : z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2=
      (z/(p:ℂ)+3*(c:ℂ)/(p:ℂ)^2)+3*(m:ℂ) := by
    rw [hb]
    push_cast
    field_simp [hpC]
    ring
  unfold cubicThetaPrimeCubeFirstTerm
  rw [hch,hx,hf]

lemma cubicThetaPrimeCubeFirstTerm_shift {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (b w : Eisenstein) (z : ℂ) :
    cubicThetaPrimeCubeFirstTerm p f b (z+3*(w:ℂ))=
      cubicThetaPrimeCubeFirstTerm p f (b+p*w) z := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hch : cubicSymbol p (3*(b+p*w))=cubicSymbol p (3*b) := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    refine ⟨3*w,?_⟩
    ring
  have hx : (z+3*(w:ℂ))/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2=
      z/(p:ℂ)+3*((b+p*w:Eisenstein):ℂ)/(p:ℂ)^2 := by
    push_cast
    field_simp [hpC]
    ring
  unfold cubicThetaPrimeCubeFirstTerm
  rw [hch,hx]

lemma cubicThetaPrimeCubeFirstPeriodization_periodic {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (w : Eisenstein) (z : ℂ) :
    cubicThetaPrimeCubeFirstPeriodization p f (z+3*(w:ℂ))=
      cubicThetaPrimeCubeFirstPeriodization p f z := by
  let e : Residues (p^2) ≃ Residues (p^2) := Equiv.addRight (Ideal.Quotient.mk (modulus (p^2)) (p*w))
  unfold cubicThetaPrimeCubeFirstPeriodization
  calc
    _ = ∑' r : Residues (p^2),cubicThetaPrimeCubeFirstTerm p f
        (residueRepresentative (p^2) (e r)) z := by
      apply tsum_congr
      intro r
      rw [cubicThetaPrimeCubeFirstTerm_shift hp]
      apply cubicThetaPrimeCubeFirstTerm_congr hp f hf
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      change Ideal.Quotient.mk (modulus (p^2))
        (residueRepresentative (p^2) r+p*w)=
        Ideal.Quotient.mk (modulus (p^2)) (residueRepresentative (p^2) (e r))
      rw [residueRepresentative_spec,map_add,residueRepresentative_spec]
      rfl
    _ = _ := e.tsum_eq (fun r : Residues (p^2) =>
      cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2) r) z)

lemma cubicThetaPrimeCubeFirstPeriodization_continuous {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) : Continuous (cubicThetaPrimeCubeFirstPeriodization p f) := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^2)) := Fintype.ofFinite _
  unfold cubicThetaPrimeCubeFirstPeriodization
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro r _
  unfold cubicThetaPrimeCubeFirstTerm
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero extension and the zero-frequency sum for the first character
branch, stated on its actual full residue ring. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstCoefficient_nonunit {p : Eisenstein} (hp : primaryPrime p)
    (m : Eisenstein) :
    cubicSymbol p (3*residueRepresentative (p^2)
      (Ideal.Quotient.mk (modulus (p^2)) (p*m)))=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  have hr : p∣residueRepresentative (p^2)
      (Ideal.Quotient.mk (modulus (p^2)) (p*m)) :=
    cubicThetaPrimeCubeResidueStep_divisible (⟨1,by decide⟩:Fin 3) (dvd_mul_right p m)
  have hz : Ideal.Quotient.mk (modulus p) (3*residueRepresentative (p^2)
      (Ideal.Quotient.mk (modulus (p^2)) (p*m)))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right hr 3))
  rw [cubicSymbol_prime hp,←cubicResidueChar_mk p hp,hz,MulChar.map_zero]

lemma cubicThetaPrimeCubeFirstCoefficient_sum {p : Eisenstein} (hp : primaryPrime p) :
    (∑' r : Residues (p^2),cubicSymbol p (3*residueRepresentative (p^2) r))=0 := by
  have hu := cubicThetaPrimeCubeUnitFourier_zeroFrequency hp 1 (by decide)
  rw [cubicThetaPrimeCubeUnitFourier_zero_eq] at hu
  have hu' : (∑' u : (Residues (p^2))ˣ,
      cubicSymbol p (3*residueRepresentative (p^2) (u:Residues (p^2))))=0 := by
    simpa only [Fin.val_one,Nat.reduceSub,pow_one] using hu
  rw [cubicThetaPrimeCubeResidueSum_two hp]
  simp_rw [cubicThetaPrimeCubeFirstCoefficient_nonunit hp]
  rw [hu',tsum_zero,add_zero]

lemma cubicThetaPrimeCubeFirstPeriodization_units {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (z : ℂ) :
    cubicThetaPrimeCubeFirstPeriodization p f z=
      ∑' u : (Residues (p^2))ˣ,
        cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2) (u:Residues (p^2))) z := by
  unfold cubicThetaPrimeCubeFirstPeriodization
  rw [cubicThetaPrimeCubeResidueSum_two hp]
  have hz (r : Residues p) :
      cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2)
        (Ideal.Quotient.mk (modulus (p^2)) (p*residueRepresentative p r))) z=0 := by
    unfold cubicThetaPrimeCubeFirstTerm
    rw [cubicThetaPrimeCubeFirstCoefficient_nonunit hp,zero_mul]
  simp_rw [hz]
  rw [tsum_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first character branch has zero horizontal mean. Integer dilation
turns each summand into a translate of the original slice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstPeriodization_dilate {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (b : Eisenstein) (z : ℂ) :
    cubicThetaPrimeCubeFirstTerm p f b ((p:ℂ)*z)=
      cubicSymbol p (3*b)*f (z+3*(b:ℂ)/(p:ℂ)^2) := by
  unfold cubicThetaPrimeCubeFirstTerm
  rw [mul_div_cancel_left₀ z (show (p:ℂ)≠0 from fun he => hp.2.ne_zero (Subtype.ext he))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second character branch is an integral horizontal dilation.
Its constant mode can therefore be reduced by the actual cell integral. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSecondBranch_point {p : Eisenstein} (hp : primaryPrime p)
    (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3) b (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPoint (‖(p:ℂ)‖*v)
        (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)
        ((p:ℂ)*z+3*(b:ℂ)/(p:ℂ)) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  apply Subtype.ext
  change ((p:ℂ)^2/(p:ℂ)^1*z+((3*b:Eisenstein):ℂ)/(p:ℂ)^1,
    (‖(p:ℂ)‖^2/‖(p:ℂ)‖^1)*v)=((p:ℂ)*z+3*(b:ℂ)/(p:ℂ),‖(p:ℂ)‖*v)
  apply Prod.ext
  · push_cast
    rw [show ((3:Eisenstein):ℂ)=3 from
      map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
    field_simp [hpC]
  · field_simp [hn]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstBranchMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first character branch, in the horizontal cell used for
arithmetic cusp coefficients. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstBranch_point {p : Eisenstein} (hp : primaryPrime p)
    (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBranchPoint hp 1 b (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPoint (v/‖(p:ℂ)‖)
        (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))
        (z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  apply Subtype.ext
  change ((p:ℂ)^1/(p:ℂ)^2*z+((3*b:Eisenstein):ℂ)/(p:ℂ)^2,
    (‖(p:ℂ)‖^1/‖(p:ℂ)‖^2)*v)=(z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2,v/‖(p:ℂ)‖)
  apply Prod.ext
  · push_cast
    rw [show ((3:Eisenstein):ℂ)=3 from
      map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
    field_simp [hpC]
  · field_simp [hn]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBottomMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bottom Hecke branch has the literal cubic residue degree as its
horizontal mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeBottomBranch_point {p : Eisenstein} (hp : primaryPrime p)
    (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBranchPoint hp 0 b (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPoint (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))
        ((z+3*(b:ℂ))/(p^3:Eisenstein)) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  apply Subtype.ext
  change ((p:ℂ)^0/(p:ℂ)^3*z+((3*b:Eisenstein):ℂ)/(p:ℂ)^3,
    (‖(p:ℂ)‖^0/‖(p:ℂ)‖^3)*v)=((z+3*(b:ℂ))/(p^3:Eisenstein),v/‖(p:ℂ)‖^3)
  apply Prod.ext
  · push_cast
    rw [show ((3:Eisenstein):ℂ)=3 from
      map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
    field_simp [hpC]
  · field_simp [hn]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHorizontalContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal slices of the literal Hecke summands are integrable on the
actual finite cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeBranch_horizontal_continuous {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b : Eisenstein) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicThetaPrimeCubeBranchPoint hp k b (cubicThetaHorizontalPoint v hv z)) := by
  unfold cubicThetaPrimeCubeBranchPoint cubicThetaHorizontalPoint
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual second character branch of the cubed-prime Hecke trace
has zero constant horizontal coefficient, at every positive height. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeUnitFunctionSum_two {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F x=
      ∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2*
        F (cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3)
          (residueRepresentative p (u:Residues p)) x) := by
  let g : Eisenstein → ℂ := fun q => ∑' u : (Residues q)ˣ,
    (cubicSymbol p (3*residueRepresentative q (u:Residues q)))^2*
      F (cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3)
        (residueRepresentative q (u:Residues q)) x)
  change g (p^(3-(⟨2,by decide⟩:Fin 3).val))=g p
  exact congrArg g (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHorizontalMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact constant horizontal coefficient of the actual cubed-prime
Hecke correspondence, with both character branches proved to vanish. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeDilation_horizontal_point {p : Eisenstein} (hp : primaryPrime p)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • cubicThetaHorizontalPoint v hv z=
      cubicThetaHorizontalPoint (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z) := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) (z,v)=_
  rw [cubicThetaMobius_primeDilation]
  simp only [Subalgebra.coe_pow,norm_pow]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueWhittaker
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPoleHeat_whittaker {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v) := by
  let A := cubicThetaRowHeatScale h
  let q := ‖cubicThetaRowFrequency h‖
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  have hq : 0<q := norm_pos_iff.mpr (by
    change (h:ℂ)/(3*traceLambda)≠0
    exact div_ne_zero (fun hz => hh (Subtype.ext hz)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  have hI : (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) A t)=
      ((A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ):ℝ):ℂ)*(cubicBesselKernel (A*v^2):ℂ) := by
    rw [← cubicTheta_cubicPole_heat hA hv]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    dsimp only [cubicThetaDualHeat]
    rw [show (4/3:ℂ)-2=((-2/3:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow ht.le]
  have hx : (2*Real.pi*(q*v))^2=A*v^2 := by
    dsimp [A,q,cubicThetaRowHeatScale]
    rw [Complex.normSq_eq_norm_sq]
    ring
  have hd : (A*v^2)^(1/6:ℝ)=A^(1/6:ℝ)*v^(1/3:ℝ) := by
    rw [Real.mul_rpow hA.le (sq_nonneg v),← Real.rpow_natCast v 2,← Real.rpow_mul hv.le]
    norm_num
  have ha : A^(1/3:ℝ)=A^(1/6:ℝ)*A^(1/6:ℝ) := by
    rw [← Real.rpow_add hA]
    norm_num
  have hpow : v^(4/3:ℝ)=v*v^(1/3:ℝ) := by
    rw [show (4/3:ℝ)=1+1/3 by norm_num,Real.rpow_add hv,Real.rpow_one]
  have hr : v^(4/3:ℝ)*(A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ))=
      (2*A^(1/6:ℝ)/q)*(q*v/2) := by
    rw [hd,ha,hpow]
    field_simp
  change (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) A t)=_
  rw [hI,show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow hv.le]
  change _=((2*A^(1/6:ℝ)/q:ℝ):ℂ)*cubicThetaWhittaker (q*v)
  rw [cubicThetaWhittaker,hx]
  rw [← mul_assoc, ← Complex.ofReal_mul, hr]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowFrequencyScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling of the literal Fourier frequency and cubic-pole radial factor. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRowFrequency_mul (a h : Eisenstein) :
    cubicThetaRowFrequency (a*h)=(a:ℂ)*cubicThetaRowFrequency h := by
  unfold cubicThetaRowFrequency
  push_cast
  ring

lemma cubicThetaRowFrequency_norm_mul (a h : Eisenstein) :
    ‖cubicThetaRowFrequency (a*h)‖=‖(a:ℂ)‖*‖cubicThetaRowFrequency h‖ := by
  rw [cubicThetaRowFrequency_mul,norm_mul]

lemma cubicThetaRowHeatScale_mul (a h : Eisenstein) :
    cubicThetaRowHeatScale (a*h)=‖(a:ℂ)‖^2*cubicThetaRowHeatScale h := by
  unfold cubicThetaRowHeatScale
  rw [cubicThetaRowFrequency_mul,Complex.normSq_mul,Complex.normSq_eq_norm_sq (a:ℂ)]
  ring

lemma cubicThetaPoleFactor_mul {a h : Eisenstein} (ha : a≠0) (hh : h≠0) :
    2*(cubicThetaRowHeatScale (a*h))^(1/6:ℝ)/‖cubicThetaRowFrequency (a*h)‖=
      ‖(a:ℂ)‖^(-(2/3:ℝ))*(2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖) := by
  have hr : 0<‖(a:ℂ)‖ := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hq : 0<‖cubicThetaRowFrequency h‖ := norm_pos_iff.mpr (by
    unfold cubicThetaRowFrequency
    exact div_ne_zero (fun he => hh (Subtype.ext he)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  have hp : (‖(a:ℂ)‖^2)^(1/6:ℝ)=‖(a:ℂ)‖^(1/3:ℝ) := by
    rw [←Real.rpow_natCast ‖(a:ℂ)‖ 2,←Real.rpow_mul hr.le]
    norm_num
  have he : ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖=‖(a:ℂ)‖^(1/3:ℝ) := by
    calc
      _ = ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = ‖(a:ℂ)‖^(-(2/3:ℝ)+1) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  rw [cubicThetaRowHeatScale_mul,cubicThetaRowFrequency_norm_mul,
    Real.mul_rpow (sq_nonneg _) (cubicThetaRowHeatScale_pos hh).le,hp]
  rw [←he]
  have halg (r q b A : ℝ) (hr : r≠0) (hq : q≠0) :
      2*(b*r*A)/(r*q)=b*(2*A/q) := by field_simp
  exact halg _ _ _ _ hr.ne' hq.ne'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoleRadialScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPoleRadialWeightIntegral (h : Eisenstein) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
    cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)

lemma cubicThetaPoleRadialWeightIntegral_scale {a : Eisenstein} (ha : a≠0)
    (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(a:ℂ)‖,W v=0) :
    cubicThetaPoleRadialWeightIntegral (a*h)
        (cubicThetaRadialWeightScale ‖(a:ℂ)‖
          (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)=
      (‖(a:ℂ)‖:ℂ)^2*cubicThetaPoleRadialWeightIntegral h W := by
  let r := ‖(a:ℂ)‖
  have hr0 : 0 < r := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hr : 1 ≤ r := by
    have hq := one_le_norm ha
    change 1≤Complex.normSq (a:ℂ) at hq
    rw [Complex.normSq_eq_norm_sq] at hq
    nlinarith
  let V := cubicThetaRadialWeightScale r hr0 W
  have hV : ∀ v≤(2:ℝ),V v=0 := by
    intro v hv
    change W (r*v)=0
    exact hW _ (by nlinarith)
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    exact hW _ (by linarith)
  unfold cubicThetaPoleRadialWeightIntegral
  rw [cubicThetaRadialIntegral_zero_extension V hV,
    cubicThetaRadialIntegral_zero_extension W hW2,cubicThetaRowFrequency_norm_mul]
  have he (v : ℝ) : cubicThetaWhittaker ((‖(a:ℂ)‖*‖cubicThetaRowFrequency h‖)*v)=
      cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*(r*v)) := by
    congr 1
    dsimp only [r]
    ring
  simp_rw [he]
  rw [cubicThetaRadialIntegral_dilate r hr0 V
    (fun v => cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  change star (W (r*(v/r)))/(v:ℂ)^3*_=star (W v)/(v:ℂ)^3*_
  rw [mul_div_cancel₀ v hr0.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeightMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical multiplier of the actual finite cubed-prime operator,
including its critical value on both height exponents 4/3 and 2/3. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_norm_power {p : Eisenstein} :
    norm (p^3)=‖(p:ℂ)‖^6 := by
  change Complex.normSq ((p^3:Eisenstein):ℂ)=_
  rw [Subalgebra.coe_pow,Complex.normSq_eq_norm_sq,norm_pow]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRadialPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact compact radial test duality for the actual Hecke operator,
first on finite-energy sections and then by density. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_height_ge_one {p : Eisenstein} (hp : primaryPrime p) :
    1≤‖(p:ℂ)‖^3 := by
  have hn := one_le_norm hp.2.ne_zero
  change 1≤Complex.normSq (p:ℂ) at hn
  rw [Complex.normSq_eq_norm_sq] at hn
  have hnorm := _root_.norm_nonneg (p:ℂ)
  have h1 : 1≤‖(p:ℂ)‖ := by nlinarith
  exact one_le_pow₀ h1

lemma cubicThetaPrimeCubeRadialWeight_low {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3, W v=0) :
    ∀ v≤(2:ℝ), cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3) (by
      have := cubicThetaPrimeCube_height_ge_one hp; linarith) W v=0 :=
  cubicThetaRadialHeckeWeight_low (cubicThetaPrimeCube_height_ge_one hp) (by norm_num) W hW

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRadialResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The known constant term of the arithmetic residue transforms by the
critical cubed-prime multiplier under every admissible compact radial test. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_mellin_multiplier {p : Eisenstein} (hp : primaryPrime p) :
    (((‖(p:ℂ)‖^3:ℝ):ℂ)^2*((‖(p:ℂ)‖^3)⁻¹:ℝ)^(4/3:ℂ)+
      ((‖(p:ℂ)‖^3:ℝ):ℂ)^(4/3:ℂ))=(norm p)^2+norm p := by
  let u := ‖(p:ℂ)‖
  have hu : 0<u := norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))
  have hpw : (u^3)^(4/3:ℝ)=u^4 := by
    rw [←Real.rpow_natCast u 3,←Real.rpow_mul hu.le]
    norm_num
  have hr : (u^3)^2*((u^3)⁻¹)^(4/3:ℝ)+(u^3)^(4/3:ℝ)=(norm p)^2+norm p := by
    rw [Real.inv_rpow (pow_nonneg hu.le 3),hpw]
    change (u^3)^2*(u^4)⁻¹+u^4=(Complex.normSq (p:ℂ))^2+Complex.normSq (p:ℂ)
    rw [Complex.normSq_eq_norm_sq]
    change (u^3)^2*(u^4)⁻¹+u^4=(u^2)^2+u^2
    field_simp
    ring
  change ((u^3:ℝ):ℂ)^2*((u^3)⁻¹:ℝ)^(4/3:ℂ)+((u^3:ℝ):ℂ)^(4/3:ℂ)=_
  have he : (4/3:ℂ)=((4/3:ℝ):ℂ) := by norm_num
  rw [he,←Complex.ofReal_cpow (inv_nonneg.mpr (pow_nonneg hu.le 3)),
    ←Complex.ofReal_cpow (pow_nonneg hu.le 3)]
  exact_mod_cast hr

lemma cubicThetaPrimeCube_zeroRadialTest {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    cubicThetaZeroRadialTest (cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3)
      (by have := cubicThetaPrimeCube_height_ge_one hp; linarith) W) (4/3)=
      ((norm p)^2+norm p:ℂ)*cubicThetaZeroRadialTest W (4/3) := by
  let r := ‖(p:ℂ)‖^3
  have hr1 : 1 ≤ r := cubicThetaPrimeCube_height_ge_one hp
  have hr : 0 < r := by linarith
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    apply hW
    change v≤2*r
    linarith
  have hA : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W v=0 := by
    intro v hv
    change W (r⁻¹*v)=0
    apply hW
    change r⁻¹*v≤2*r
    rw [mul_comm,←div_eq_mul_inv,div_le_iff₀ hr]
    have : 1 ≤ r*r := by nlinarith
    nlinarith
  have hB : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0 := by
    intro v hv
    change W (r*v)=0
    apply hW
    change r*v≤2*r
    nlinarith
  rw [cubicThetaZeroRadialTest_hecke r hr W hW2 hA hB,
    cubicThetaPrimeCube_mellin_multiplier hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSubgroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-index arithmetic subgroup on which the fractional upper-root
translations can act. The diagonal congruence is retained explicitly. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment


lemma cubicThetaPrimeRootSubgroup_ker_le (p : Eisenstein) :
    (cubicThetaPrimeReduction (p^2)).ker ≤ cubicThetaPrimeRootSubgroup p := by
  intro g hg
  refine ⟨cubicThetaPrimeReduction_ker_le (p^2) hg,?_⟩
  have ha := congrArg (fun A : SL(2,Residues (p^2)) => A 0 0) hg
  have hd := congrArg (fun A : SL(2,Residues (p^2)) => A 1 1) hg
  change Ideal.Quotient.mk (modulus (p^2)) (g.val 0 0)=1 at ha
  change Ideal.Quotient.mk (modulus (p^2)) (g.val 1 1)=1 at hd
  have hz : Ideal.Quotient.mk (modulus (p^2)) (g.val 0 0-g.val 1 1)=0 := by
    rw [map_sub,ha,hd,sub_self]
  exact (dvd_pow_self p (by decide : 2≠0)).trans
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))

theorem cubicThetaPrimeRootSubgroup_finiteIndex {p : Eisenstein} (hp : p≠0) :
    (cubicThetaPrimeRootSubgroup p).FiniteIndex := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero 2 hp)
  let : Finite (cubicThetaPrimeReduction (p^2)).range := inferInstance
  let : (cubicThetaPrimeReduction (p^2)).ker.FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (cubicThetaPrimeRootSubgroup_ker_le p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootMatrix
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact arithmetic subgroup for translations by 3x/p^3.
It is needed to compare the cubic Hecke correlation with finite Fourier classes. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootSubgroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootSubgroup p).FiniteIndex :=
  cubicThetaPrimeRootSubgroup_finiteIndex (pow_ne_zero 3 hp.2.ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-scale fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the cube modulus. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootElement_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (x+y)=
      cubicThetaPrimeCubeRootElement hp x*cubicThetaPrimeCubeRootElement hp y := by
  simp only [cubicThetaPrimeCubeRootElement_translation]
  apply Subtype.ext
  change (!![1,((3*(x+y):Eisenstein):ℂ)/((p^3:Eisenstein):ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)=
    !![1,((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ);0,1]*!![1,((3*y:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_add,add_div,add_comm]

lemma cubicThetaPrimeCubeRootElement_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (p^3*x)=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) := by
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrincipalTranslation_complex]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp [hpC]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphism
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootConjugate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootConjugate hp (x+y) g=
      cubicThetaPrimeCubeRootConjugate hp x (cubicThetaPrimeCubeRootConjugate hp y g) := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeCubeRootConjugate_complex,cubicThetaPrimeCubeRootElement_add,mul_inv_rev]
  group

def cubicThetaPrimeCubeRootAutomorphism {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeCubeRootSubgroup p ≃* cubicThetaPrimeCubeRootSubgroup p where
  toFun := cubicThetaPrimeCubeRootConjugate hp x
  invFun := cubicThetaPrimeCubeRootConjugate hp (-x)
  left_inv g := by
    rw [←cubicThetaPrimeCubeRootConjugate_add,neg_add_cancel,cubicThetaPrimeCubeRootConjugate_zero]
  right_inv g := by
    rw [←cubicThetaPrimeCubeRootConjugate_add,add_neg_cancel,cubicThetaPrimeCubeRootConjugate_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply cubicThetaPrincipalComplex_injective
    change cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x (g*h)).val=
      cubicThetaPrincipalComplex ((cubicThetaPrimeCubeRootConjugate hp x g).val*
        (cubicThetaPrimeCubeRootConjugate hp x h).val)
    simp only [cubicThetaPrimeCubeRootConjugate_complex,map_mul,Subgroup.coe_mul]
    group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeyl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual opposite-root involution at modulus p cubed. Both
integral conjugations preserve the original cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootDilationIwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeIwahori (p^3) :=
  ⟨cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) (cubicThetaPrimeCubeRootIwahori g),by
    change p^3∣g.val.val 1 0/p^3
    rw [cubicThetaPrimeCubeRoot_lower_single_division hp g]
    exact dvd_mul_right _ _⟩

lemma cubicThetaPrimeCubeRootDilationIwahori_entry00 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 0 0=g.val.val 0 0 := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry01 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 0 1=p^3*g.val.val 0 1 := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry10 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 1 0=g.val.val 1 0/p^3 := rfl

lemma cubicThetaPrimeCubeRootDilationIwahori_entry11 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    (cubicThetaPrimeCubeRootDilationIwahori hp g).val.val 1 1=g.val.val 1 1 := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal integral Bruhat identity for unit translations modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootBruhat_division {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    p^3*((1-9*x*y)/p^3)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaPrimeCubeRootBruhatMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![p^3,3*x;-3*y,(1-9*x*y)/p^3],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaPrimeCubeRootBruhat_division hp x y hxy⟩

lemma cubicThetaPrimeCubeRootBruhatMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaPrimeCubeRootBruhatMatrix hp x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (p^3) ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/p^3)
  refine ⟨(cubicThetaPrimeCube_primary hp),⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/p^3-1
  apply (primary_coprime_three (cubicThetaPrimeCube_primary hp)).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaPrimeCubeRootBruhat_division hp x y hxy]
  convert dvd_sub (dvd_neg.mpr (cubicThetaPrimeCube_primary hp)) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  all_goals try with_reducible_and_instances rfl
  ring

def cubicThetaPrimeCubeRootBruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeCubeRootBruhatMatrix hp x y hxy,cubicThetaPrimeCubeRootBruhatMatrix_mem hp x y hxy⟩

lemma cubicThetaPrimeCubeRootBruhat_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootBruhat hp x y hxy)=cubicSymbol (p^3) (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (p^3) (-3*y)=cubicSymbol (p^3) (3*y)
  rw [neg_mul,cubicSymbol_neg (cubicThetaPrimeCube_primary hp)]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial profiles give actual automorphic sections by a locally finite
Poincaré sum. No spectral input is used. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment


def cubicThetaRadialProfileTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  star r.phase*W (r.height p)

def cubicThetaRadialProfileSeries (p : ℂ × ℝ) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaRadialProfileTerm r p W

lemma cubicThetaRadialProfileTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaRadialProfileTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaRadialProfileTerm (r.rightMul g) p W := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g)=1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaRadialProfileTerm,cubicThetaRadialProfileTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*W
          (r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p))) := by rw [hu,one_mul]
    _ = _ := by ring

theorem cubicThetaRadialProfileSeries_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (W : C_c(ℝ,ℂ)) :
    cubicThetaRadialProfileSeries (cubicThetaMobius (cubicThetaPrincipalComplex g) p) W=
      cubicThetaKubotaValue g*cubicThetaRadialProfileSeries p W := by
  unfold cubicThetaRadialProfileSeries
  simp_rw [cubicThetaRadialProfileTerm_translate _ g hp W]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaRadialProfileTerm r p W)

lemma cubicThetaRadialProfileSeries_high (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) {p : ℂ × ℝ} (hp : 1<p.2) :
    cubicThetaRadialProfileSeries p W=W p.2 := by
  have he : cubicThetaRadialProfileSeries p W=cubicThetaRadialProfileTerm cubicThetaZeroRow p W := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hh : 1 < r.height p := by
      by_contra ht
      exact hn (mul_eq_zero_of_right _ (hW _ (le_of_not_gt ht)))
    have hc := r.high_height_c_zero hp hh
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he]
  simp [cubicThetaRadialProfileTerm,CubicThetaBottomRow.height,CubicThetaBottomRow.phase,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileSmooth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact radial profiles produce genuine compact smooth sections. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfileTerm_contDiffAt (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaRadialProfileTerm r q W) p :=
  contDiffAt_const.mul (hsm.contDiffAt.comp p (r.height_contDiffAt hp))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise Euler equation of a compact radial profile is preserved
by the actual locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma radial_coordinate_smooth (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (r : CubicThetaBottomRow)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint t y v) W) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x t v) W) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y t) W) v := by
  have hr := cubicThetaRadialProfileTerm_contDiffAt W hsm r (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  have ht : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(hr.comp x hx.contDiffAt).of_le (by norm_num),
    (hr.comp y hy.contDiffAt).of_le (by norm_num),
    (hr.comp v ht.contDiffAt).of_le (by norm_num)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPhaseRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact phase of each of the two nonzero middle ramified rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaLambda_dvd_three : lambdaE∣(3:Eisenstein) := by
  refine ⟨-lambdaE,?_⟩
  rw [mul_neg,←pow_two,lambdaE_sq]
  ring

end CubicFirstMoment

end

end OAI
end


