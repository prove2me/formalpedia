-- Prove2me | Definitions.Def_OAIQ096A007
-- name    : OAIQ096A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:35:45.790678+00:00
-- url     : https://prove2.me/theorems/b2aebd21-f0df-4d19-b372-4709f3cf7c0a
-- title:
--   Definitions bundle OAIQ096A007 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 347 declarations of OpenAI's Lean: 175 definitions, 5 inductive types or structures, 7 instances and 160 theorems. The definitions and types are `OAI.CubicFirstMoment.CubicThetaCommonIndex`, `OAI.CubicFirstMoment.CubicThetaCoordinates.amplitude`, `OAI.CubicFirstMoment.CubicThetaCoordinates.coefficient`, `OAI.CubicFirstMoment.CubicThetaCoordinates.conjugated`, `OAI.CubicFirstMoment.CubicThetaCoordinates.cuspCoefficient`, `OAI.CubicFirstMoment.CubicThetaCoordinates.mulLambdaCube`, `OAI.CubicFirstMoment.CubicThetaCoordinates.mulPrimaryCube`, `OAI.CubicFirstMoment.CubicThetaCoordinates.neg`, `OAI.CubicFirstMoment.CubicThetaCoordinates.removeLambdaCube`, `OAI.CubicFirstMoment.CubicThetaCoreIndex`, `OAI.CubicFirstMoment.CubicThetaCoreSupport`, `OAI.CubicFirstMoment.CubicThetaCoreValueFamily`, `OAI.CubicFirstMoment.CubicThetaDenominator`, `OAI.CubicFirstMoment.CubicThetaFreeArgument`, `OAI.CubicFirstMoment.CubicThetaFullRow`, `OAI.CubicFirstMoment.CubicThetaFullRow.height`, `OAI.CubicFirstMoment.CubicThetaFullRow.quadratic`, `OAI.CubicFirstMoment.CubicThetaGlobalEnergyAmbient`, `OAI.CubicFirstMoment.CubicThetaGlobalL2`, `OAI.CubicFirstMoment.CubicThetaGradientL2`, `OAI.CubicFirstMoment.CubicThetaInvertedRow.height`, `OAI.CubicFirstMoment.CubicThetaNonzeroCube`, `OAI.CubicFirstMoment.CubicThetaNonzeroFirstPrimitiveRow`, `OAI.CubicFirstMoment.CubicThetaNonzeroRow`, `OAI.CubicFirstMoment.CubicThetaPeriodGroup`, `OAI.CubicFirstMoment.CubicThetaPositiveStripL2`, `OAI.CubicFirstMoment.CubicThetaPrimaryCube`, `OAI.CubicFirstMoment.CubicThetaPrimaryNine`, `OAI.CubicFirstMoment.CubicThetaPrimaryPart`, `OAI.CubicFirstMoment.CubicThetaPrimaryResidue`, `OAI.CubicFirstMoment.CubicThetaPrimeCubeRootL2`, `OAI.CubicFirstMoment.CubicThetaPrimeFreeDenominator`, `OAI.CubicFirstMoment.CubicThetaPrimeRootCover`, `OAI.CubicFirstMoment.CubicThetaPrimeRootL2`, `OAI.CubicFirstMoment.CubicThetaPrimitiveRow.completion`, `OAI.CubicFirstMoment.CubicThetaPrimitiveRow.denominator`, `OAI.CubicFirstMoment.CubicThetaPrimitiveRow.height`, `OAI.CubicFirstMoment.CubicThetaPrimitiveRow.rightMul`, `OAI.CubicFirstMoment.CubicThetaPrimitiveRow.rightMulEquiv`, `OAI.CubicFirstMoment.CubicThetaQuotient` and 140 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_CommonFactors`, `CubicGram_LatticePoisson`, `CubicGram_MellinDecay`, `CubicGram_PeriodicPoisson`, `CubicGram_SquarefreeGauss`, `CubicMoment_Angular_AngularConductorPhase`, `CubicMoment_Angular_AngularDualTail`, `CubicMoment_Angular_AngularHeatLattice`, `CubicMoment_Angular_AngularHeckeCharacter`, `CubicMoment_Angular_AngularHeckeGrowth`, `CubicMoment_Angular_AngularHeightCoefficient`, `CubicMoment_Angular_AngularKummerAlgebra`, `CubicMoment_Angular_AngularModel`, `CubicMoment_Angular_AngularNumeratorCharacter`, `CubicMoment_Angular_AngularResidueLift`, `CubicMoment_Angular_AngularTwistedPrimitiveFamily`, `CubicMoment_Estimates_CubicNumeratorCharacter`, `CubicMoment_Estimates_FixedAngularHecke`, `CubicMoment_Estimates_FullPrimeConvolution`, `CubicMoment_Estimates_HeckeSmoothDual`, `CubicMoment_Estimates_HeckeStripGrowth`, `CubicMoment_Estimates_HuxleyLiftedPacking`, `CubicMoment_Estimates_HuxleyResiduePoints`, `CubicMoment_Estimates_IdealMellinSeries`, `CubicMoment_Estimates_IdealMoebiusBounds`, `CubicMoment_Estimates_MellinDualTail`, `CubicMoment_Estimates_ModelPartialSummation`, `CubicMoment_Estimates_NormDenominatorMellin`, `CubicMoment_Estimates_OrdinaryMixedSieve`, `CubicMoment_Estimates_PoissonProfileBudget`, `CubicMoment_Estimates_PrimaryProductCoefficients`, `CubicMoment_Estimates_PrimeCoordinateCollection`, `CubicMoment_Estimates_PrimitiveConductor`, `CubicMoment_Estimates_PublishedAdditiveSieve`, `CubicMoment_Estimates_PublishedAngularHecke`, `CubicMoment_Estimates_PublishedKummerPrime`, `CubicMoment_Estimates_PublishedPrimitiveHecke`, `CubicMoment_Estimates_ResidueIdealCharacters`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Estimates_ShortMoebiusPolynomials`, `CubicMoment_Estimates_ShortMoebiusProducts`, `CubicMoment_Estimates_StructuredMeanValue`, `CubicMoment_Estimates_TwistedPrimitiveFamily`, `CubicMoment_Estimates_WideGramDecay`, `CubicMoment_Estimates_WideGramMellin`, `CubicMoment_Theta_CubicThetaArithmetic`, `CubicMoment_Theta_CubicThetaArithmeticCubeScaling`, `CubicMoment_Theta_CubicThetaAutomorphicSections`, `CubicMoment_Theta_CubicThetaBorelSection`, `CubicMoment_Theta_CubicThetaCommonIndex`, `CubicMoment_Theta_CubicThetaCompactRowBounds`, `CubicMoment_Theta_CubicThetaCompactTransporters`, `CubicMoment_Theta_CubicThetaConjugateCoordinates`, `CubicMoment_Theta_CubicThetaConstantCount`, `CubicMoment_Theta_CubicThetaCoreCoefficient`, `CubicMoment_Theta_CubicThetaCoreMassFamily`, `CubicMoment_Theta_CubicThetaCubeCoordinates`, `CubicMoment_Theta_CubicThetaCuspCoefficients`, `CubicMoment_Theta_CubicThetaCuspStrip`, `CubicMoment_Theta_CubicThetaEven`, `CubicMoment_Theta_CubicThetaFactorUniqueness`, `CubicMoment_Theta_CubicThetaFiniteCuspRestriction`, `CubicMoment_Theta_CubicThetaFreeAction`, `CubicMoment_Theta_CubicThetaFreeCubeIndex`, `CubicMoment_Theta_CubicThetaFullGaussian`, `CubicMoment_Theta_CubicThetaFullLevelRows`, `CubicMoment_Theta_CubicThetaFullRows`, `CubicMoment_Theta_CubicThetaFundamentalDomain`, `CubicMoment_Theta_CubicThetaGaussConjugation`, `CubicMoment_Theta_CubicThetaGlobalEnergy`, `CubicMoment_Theta_CubicThetaGlobalGradient`, `CubicMoment_Theta_CubicThetaGlobalL2`, `CubicMoment_Theta_CubicThetaHorizontalDomain`, `CubicMoment_Theta_CubicThetaHorizontalLattice`, `CubicMoment_Theta_CubicThetaHyperbolicMeasure`, `CubicMoment_Theta_CubicThetaInversionCharacter`, `CubicMoment_Theta_CubicThetaInvertedRows`, `CubicMoment_Theta_CubicThetaLocalEnergyGraph`, `CubicMoment_Theta_CubicThetaLocalEnergyRellich`, `CubicMoment_Theta_CubicThetaLocalRellichValue`, `CubicMoment_Theta_CubicThetaLocalizationLinear`, `CubicMoment_Theta_CubicThetaLocalizationSobolevBound`, `CubicMoment_Theta_CubicThetaMassFactorization`, `CubicMoment_Theta_CubicThetaNonzeroRowHeat`, `CubicMoment_Theta_CubicThetaPositiveCuspRestriction`, `CubicMoment_Theta_CubicThetaPrimaryCubes`, `CubicMoment_Theta_CubicThetaPrimaryPowerCoordinates`, `CubicMoment_Theta_CubicThetaPrimaryResidueNine`, `CubicMoment_Theta_CubicThetaPrimeAtkinAction`, `CubicMoment_Theta_CubicThetaPrimeAtkinConjugation`, `CubicMoment_Theta_CubicThetaPrimeAtkinInvolution`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeCubeRootL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootPowerCharacter`, `CubicMoment_Theta_CubicThetaPrimeCubeRootSections`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootAction`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootAutomorphism`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootConjugation`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootMatrix`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootSections`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootTranslation`, `CubicMoment_Theta_CubicThetaPrimeIwahori`, `CubicMoment_Theta_CubicThetaPrimePowerFourier`, `CubicMoment_Theta_CubicThetaPrimeRootAction`, `CubicMoment_Theta_CubicThetaPrimeRootAutomorphism`, `CubicMoment_Theta_CubicThetaPrimeRootCharacter`, `CubicMoment_Theta_CubicThetaPrimeRootCoverAction`, `CubicMoment_Theta_CubicThetaPrimeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeRootDiagonal`, `CubicMoment_Theta_CubicThetaPrimeRootL2`, `CubicMoment_Theta_CubicThetaPrimeRootOperators`, `CubicMoment_Theta_CubicThetaPrimeRootResidues`, `CubicMoment_Theta_CubicThetaPrimeRootSectionNorm`, `CubicMoment_Theta_CubicThetaPrimeRootSections`, `CubicMoment_Theta_CubicThetaPrimeRootTranslation`, `CubicMoment_Theta_CubicThetaPrimeRootWeyl`, `CubicMoment_Theta_CubicThetaPrimeRootWeylCover`, `CubicMoment_Theta_CubicThetaPrimeRootWeylInvolution`, `CubicMoment_Theta_CubicThetaPrimeValuation`, `CubicMoment_Theta_CubicThetaPrimitiveAction`, `CubicMoment_Theta_CubicThetaPrimitiveHeatCusp`, `CubicMoment_Theta_CubicThetaPrimitiveZeroRows`, `CubicMoment_Theta_CubicThetaPrincipalTrace`, `CubicMoment_Theta_CubicThetaProperAction`, `CubicMoment_Theta_CubicThetaQuotient`, `CubicMoment_Theta_CubicThetaQuotientCharts`, `CubicMoment_Theta_CubicThetaRamifiedCoefficientScaling`, `CubicMoment_Theta_CubicThetaRamifiedCoefficientSupport`, `CubicMoment_Theta_CubicThetaRamifiedCoordinates`, `CubicMoment_Theta_CubicThetaRamifiedDenominator`, `CubicMoment_Theta_CubicThetaRamifiedIdeal`, `CubicMoment_Theta_CubicThetaRationalCusp`, `CubicMoment_Theta_CubicThetaRowCompletionTranslation`, `CubicMoment_Theta_CubicThetaRowTranslationEquiv`, `CubicMoment_Theta_CubicThetaSiegelReduction`, `CubicMoment_Theta_CubicThetaSmoothTests`, `CubicMoment_Theta_CubicThetaTranslatedCuspStrip`, `CubicMoment_Transform_MetaplecticCodeDyads`, `CubicMoment_Transform_MetaplecticCoefficientSeries`, `CubicMoment_Transform_MetaplecticRetainedSupport`, `CubicMoment_Transform_MetaplecticVoronoi`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A004` and `OAIQ096A005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A011`, `OAIQ096A012`, `OAIQ096A013`, `OAIQ096A014` and `OAIQ096A015`; the statements `OAI.CubicFirstMoment.ProfileControl.low_common_sum_height_log_saving`, `OAI_CubicFirstMoment_ProfileControl_low_coprime_height_real`, `OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power`, `OAI_CubicFirstMoment_ShortFactorFamily_first_rows_contradiction`, `OAI_CubicFirstMoment_angular_first_twisted_vonMangoldt_neighborhood`, `OAI.CubicFirstMoment.angular_stopped_corrected_dispersion_log_saving_actual`, `OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form`, `OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual`, `OAI.CubicFirstMoment.angular_stopped_sieved_model_log_saving`, `OAI_CubicFirstMoment_cubic_gram_large_value_count`, `OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds`, `OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood`, `OAI_CubicFirstMoment_first_common_coordinate_exponents`, `OAI.CubicFirstMoment.first_common_prime_exponents`, `OAI.CubicFirstMoment.first_weighted_tuple_neighborhood`, `OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound`, `OAI.CubicFirstMoment.full_smooth_twisted_primitive_cubic_bound`, `OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive`, `OAI.CubicFirstMoment.localized_integral_power_saving`, `OAI.CubicFirstMoment.low_localized_height_integral_bound`, `OAI.CubicFirstMoment.primaryPrimePNT_proved`, `OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power`, `OAI.CubicFirstMoment.primitiveAngularHeckeInput_proved`, `OAI.CubicFirstMoment.smallB_core_hybrid_sieve`, `OAI.CubicFirstMoment.small_conductor_frequency_sieve`, `OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual`, `OAI.CubicFirstMoment.stopped_noncube_radial_form` and `OAI.CubicFirstMoment.stopped_sieved_model_log_saving`; the proofs of `OAI.CubicFirstMoment.bounded_cubic_moment`, `OAI.CubicFirstMoment.bounded_large_common_nonzero`, `OAI.CubicFirstMoment.outer_core_block_sieve` and `OAI.CubicFirstMoment.primaryPrimePNT_proved`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A004
import Definitions.Def_OAIQ096A005

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma norm_gauss_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) : ‖gauss (∏ p ∈ s, p)‖ = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [gauss_one]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, gauss_mul_of_isCoprime hp'.1 hprimary hc,
      norm_mul, norm_mul, gauss_prime hp', norm_gaussAtPrime hp', ih hs,
      norm_mul, norm_cubicSymbol_of_isCoprime hp'.1 hc,
      norm_cubicSymbol_of_isCoprime hprimary hc.symm]
    norm_num

theorem norm_gauss_of_squarefree {b : Eisenstein} (hb : primary b) (hs : Squarefree b) :
    ‖gauss b‖ = 1 := by
  rw [← primaryPrimeFactors_prod hb hs]
  exact norm_gauss_prod_primaryPrimes _ (fun p hp => (primaryPrimeFactor_spec hb hp).1)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
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

@[simp] lemma complexMulEquiv_apply (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    complexMulEquiv q hq z = q * z := rfl

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic lattice Poisson summation and exact trace frequencies. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
open CubicPoisson

def traceFourierSchwartz (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Complex.conjCLE.trans (complexMulEquiv 2 (by norm_num))) (𝓕 f)

lemma traceFourierSchwartz_apply (f : 𝓢(ℂ, ℂ)) (w : ℂ) :
    traceFourierSchwartz f w = traceFourier f w := by
  change (𝓕 f) (2 * star w) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, traceFourier]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Circle.smul_def, smul_eq_mul]
  congr 2
  simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply, tracePair,
    Complex.star_def, RCLike.re_to_complex, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.re_ofNat, Complex.im_ofNat]
  congr 1
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moebius removal of common factors and coprime Gram decomposition. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma norm_cubicSymbol_le_one {a : Eisenstein} (ha : primary a) (b : Eisenstein) :
    ‖cubicSymbol a b‖ ≤ 1 := by
  by_cases hab : IsCoprime a b
  · rw [norm_cubicSymbol_of_isCoprime ha hab]
  · simp [cubicSymbol_eq_zero_of_not_isCoprime ha hab]

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
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

def normProfileFourierSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) : 𝓢(ℂ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) • traceFourierSchwartz (normProfileSchwartz W hW hW' 1
    (by norm_num))

lemma normProfileFourierSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (y : ℂ) :
    normProfileFourierSchwartz W hW hW' y = normProfileFourier W y := by
  simp only [normProfileFourierSchwartz, smul_apply,
    traceFourierSchwartz_apply, normProfileFourier]
  congr 2
  ext z
  simp

end CubicFirstMoment

namespace CubicFirstMoment

lemma gramLogKernel_smooth (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    ContDiff ℝ ∞ (gramLogKernel W ρ) := by
  have he : (normProfileFourierSchwartz W hW hW' : ℂ → ℂ) = normProfileFourier W :=
    funext (normProfileFourierSchwartz_apply W hW hW')
  have hF : ContDiff ℝ ∞ (normProfileFourier W) := by
    rw [← he]
    exact (normProfileFourierSchwartz W hW hW').smooth ⊤
  apply gramLogBump.contDiff.smul
  refine hF.comp ?_
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2)))

def gramLogSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  (gramLogKernel_compact W ρ).toSchwartzMap (gramLogKernel_smooth W hW hW' ρ)

@[simp] lemma gramLogSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    gramLogSchwartz W hW hW' ρ u = gramLogKernel W ρ u := rfl

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma annularLogSchwartz_apply (F : 𝓢(ℂ, ℂ)) (c u : ℝ) :
    annularLogSchwartz F c u = gramLogBump u • F (c • gramExp u) := rfl

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma idealExponentGenerator_add (ν κ : EisensteinIdealExponent) :
    idealExponentGenerator (ν + κ) = idealExponentGenerator ν * idealExponentGenerator κ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma idealExponentGenerator_of_multiset (s : Multiset EisensteinIdealPrime) :
    idealExponentGenerator s.toFinsupp = (s.map idealPrimeRepresentative).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [idealExponentGenerator]
  | @cons p s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, idealExponentGenerator_add, ih]
    simp [idealExponentGenerator]

lemma idealExponentOf_associated {a : Eisenstein} (ha : a ≠ 0) :
    Associated (idealExponentGenerator (idealExponentOf a)) a := by
  apply Associates.mk_eq_mk_iff_associated.mp
  rw [idealExponentOf, idealExponentGenerator_of_multiset]
  have hmap : (Associates.factors' a).map
      (fun p => Associates.mk (idealPrimeRepresentative p)) =
      (Associates.factors' a).map Subtype.val := by
    apply Multiset.map_congr rfl
    intro p hp
    exact Associates.quot_out p.val
  calc
    Associates.mk (((Associates.factors' a).map idealPrimeRepresentative).prod) =
        ((Associates.factors' a).map Subtype.val).prod := by
      change Associates.mkMonoidHom _ = _
      rw [map_multiset_prod, Multiset.map_map]
      change ((Associates.factors' a).map
        (fun p => Associates.mk (idealPrimeRepresentative p))).prod = _
      rw [hmap]
    _ = ((UniqueFactorizationMonoid.factors a).map Associates.mk).prod := by
      rw [Associates.map_subtype_coe_factors']
    _ = Associates.mk ((UniqueFactorizationMonoid.factors a).prod) := by
      exact (map_multiset_prod Associates.mkMonoidHom _).symm
    _ = Associates.mk a := Associates.mk_eq_mk_iff_associated.mpr
      (UniqueFactorizationMonoid.factors_prod ha)

lemma idealExponentOf_mul {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0) :
    idealExponentOf (a * b) = idealExponentOf a + idealExponentOf b := by
  have h := Associates.factors_mul (Associates.mk a) (Associates.mk b)
  rw [Associates.mk_mul_mk, Associates.factors_mk (a * b) (mul_ne_zero ha hb),
    Associates.factors_mk a ha, Associates.factors_mk b hb] at h
  have hs : Associates.factors' (a * b) = Associates.factors' a + Associates.factors' b :=
    WithTop.coe_inj.mp h
  simp only [idealExponentOf, hs, Multiset.toFinsupp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and Mellin inversion for the complete ideal
series. Prime-exponent vectors include all nonzero ideals, including
the ramified prime; no Euler factor is silently removed. -/

noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma idealExponentOf_one_aux : idealExponentOf 1 = 0 := by
  have h : Associates.factors' (1 : Eisenstein) = 0 := by
    apply WithTop.coe_inj.mp
    rw [← Associates.factors_mk _ one_ne_zero,Associates.mk_one,Associates.factors_one]
    rfl
  simp [idealExponentOf,h]

lemma idealExponentOf_pow {a : Eisenstein} (ha : a ≠ 0) (k : ℕ) :
    idealExponentOf (a^k) = k • idealExponentOf a := by
  induction k with
  | zero => simp [idealExponentOf_one_aux]
  | succ k ih => rw [pow_succ,idealExponentOf_mul (pow_ne_zero _ ha) ha,ih,add_nsmul,one_nsmul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinDualTail
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

/-- The tail is the tail of the full ideal series, with all Euler factors. -/
def idealDirichletTail (χ : EisensteinIdealExponent → ℂ) (J : ℝ) (s : ℂ) : ℂ :=
  ∑' ν : EisensteinIdealExponent,
    if J < idealExponentNorm ν then χ ν*(idealExponentNorm ν:ℂ)^(-s) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma idealExponentOf_squarefree_iff {a : Eisenstein} (ha : a ≠ 0) :
    (∀ p, idealExponentOf a p ≤ 1) ↔ Squarefree a := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha,
    ← idealPrimeFactors_normalized]
  have hinj : Function.Injective
      (fun p : EisensteinIdealPrime => p.val.out) :=
    Associates.out_injective.comp Subtype.val_injective
  rw [Multiset.nodup_map_iff_of_injective hinj, Multiset.nodup_iff_count_le_one]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusPolynomials
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma idealExponentGenerator_dvd_of_le {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentGenerator ν ∣ idealExponentGenerator κ := by
  refine ⟨idealExponentGenerator (κ-ν),?_⟩
  rw [← idealExponentGenerator_add,add_tsub_cancel_of_le h]

lemma idealPrimaryGenerator_primary {a : Eisenstein} (ha : primary a)
    {ν : EisensteinIdealExponent} (hν : ν ≤ idealExponentOf a) :
    primary (idealPrimaryGenerator ν) := by
  apply primaryNormalize_primary
  exact unit_residue_of_dvd_primary ha ((idealExponentGenerator_dvd_of_le hν).trans
    (idealExponentOf_associated (primary_ne_zero ha)).dvd)

lemma idealPrimaryGenerator_at_element {a : Eisenstein} (ha : primary a) :
    idealPrimaryGenerator (idealExponentOf a) = a := by
  exact primary_associated_eq (idealPrimaryGenerator_primary ha le_rfl) ha
    ((primaryNormalize_associated _).symm.trans (idealExponentOf_associated (primary_ne_zero ha)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From the ordinary analytic properties of a primitive Hecke series
to a truncated smooth dual sum. The smooth-duality conclusion follows from the contour shift. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

/-- The precise ordinary Hecke inputs needed for contour shifting:
right-half-plane series, entireness, the regular-point functional equation,
and polynomial growth in each of the required strips. See Watkins (2011)
§3.6 and Thorner--Zaman (2019) §2C. The strip-growth bound follows from the completed finite-order property and
weak reciprocal-Gamma growth by the Phragmén–Lindelöf theorem. -/
structure PrimitiveHeckeAnalyticData (χ χdual : EisensteinIdealExponent → ℂ)
    (A : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ L
  right_series : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s
  dual_right_series : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s
  functional_equation : HeckeFunctionalEquation A 0 ε L Ldual
  strip_growth : ∀ m : ℕ, ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧
    ∀ σ ∈ Icc (1/2-(m:ℝ)) 2, ∀ u : ℝ,
      ‖L (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeStripGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial strip-growth field used by the Mellin proof follows
from finite order, absolute convergence, and the functional equation.
No polynomial strip bound is assumed in the input structure here. -/

noncomputable section
open Set
namespace CubicFirstMoment

/-- Finite order is the weak growth statement supplied by the classical
completed Hecke-function theory. Its conversion from the completed
order-one bound is kept separate from the Phragmén–Lindelöf argument. -/
structure PrimitiveHeckeFiniteOrderData (χ χdual : EisensteinIdealExponent → ℂ)
    (A : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ L
  right_series : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s
  dual_right_series : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s
  functional_equation : HeckeFunctionalEquation A 0 ε L Ldual
  finite_order : ∀ m : ℕ, FiniteVerticalOrder L (1/2-(m:ℝ)) 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAdditiveSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published additive large-sieve input over the Eisenstein integers

M. N. Huxley, *The large sieve inequality for algebraic number fields*,
Mathematika 15 (1968), 178–187. The precise imaginary-quadratic form used
here is displayed in P. Gao and L. Zhao, *The large sieve with power moduli
in imaginary quadratic number fields*, IJNT 18 (2022), 1713–1733,
arXiv:2101.00811v2, equation (1.2).

This is an explicit hypothesis type. The primitive multiplicative
character inequality is to be derived by finite Gauss expansion and
orthogonality; it is not assumed here.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Gao–Zhao's additive character `e_K(nh/q)`, with `sqrt(D_K)=traceLambda`. -/
def huxleyPhase (q h n : Eisenstein) : ℂ :=
  let z : ℂ := (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ))
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*(z+star z))

def additiveSievePolynomial (N : Finset Eisenstein) (v : Eisenstein → ℂ)
    (q h : Eisenstein) : ℂ :=
  ∑ n ∈ N, v n*huxleyPhase q h n

def huxleyModulusMass (q : Eisenstein) (N : Finset Eisenstein)
    (v : Eisenstein → ℂ) : ℝ :=
  ∑' h : Residues q, if IsUnit h then
    ‖additiveSievePolynomial N v q (residueRepresentative q h)‖^2 else 0

def huxleySieveMass (Q Z : ℝ) (v : Eisenstein → ℂ) : ℝ :=
  ∑ q ∈ nonzeroNormBall Q, huxleyModulusMass q (nonzeroNormBall Z) v

/-- Exact `Q²+Z` input, with neither a conductor power loss nor an
invented multiplicative-character estimate hidden in the hypothesis. -/
def HuxleyAdditiveLargeSieve : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
    ∀ v : Eisenstein → ℂ,
      huxleySieveMass Q Z v ≤ C*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryMixedSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mixed cubic character sieve, derived from Huxley's additive
large sieve. The only extra loss is the proved arbitrarily small divisor power. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def PrimarySquarefreePair (p : Eisenstein × Eisenstein) : Prop :=
  primary p.1 ∧ primary p.2 ∧ Squarefree p.1 ∧ Squarefree p.2 ∧ IsCoprime p.1 p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

/-- Fixed-angle polynomial with arbitrary finite Eisenstein support. -/
def angularCoefficientPolynomial (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ b ∈ B, β b * theta ℓ b * mellinPhase (t + u) (norm b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary conductor reduction for the finite residue characters.
Minimality is measured by the positive ideal norm; the inducing character
and exact deleted Euler factors are not supplied as extra assumptions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Agreement of characters on ideals prime to the original modulus. -/
def ResidueCharacterInduces (q d : Eisenstein)
    (χ : MulChar (Residues q) ℂ) (ψ : MulChar (Residues d) ℂ) : Prop :=
  d ∣ q ∧ ∀ x : Eisenstein, IsCoprime q x →
    ψ (Ideal.Quotient.mk (modulus d) x) = χ (Ideal.Quotient.mk (modulus q) x)

/-- No inducing modulus has smaller norm. This is the usual primitivity
criterion for a finite ray character over a principal ideal domain. -/
def PrimitiveResidueCharacter (q : Eisenstein) (χ : MulChar (Residues q) ℂ) : Prop :=
  ∀ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
    ResidueCharacterInduces q d χ ψ → normNat q ≤ normNat d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν : EisensteinIdealExponent) : ℂ :=
  χ (Ideal.Quotient.mk (modulus q) (idealExponentGenerator ν))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedPrimitiveHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The classical primitive Hecke input on the actual finite residue
characters constructed here. Completion/functional equation: Watkins
(2011), §3.6, p.123; entire order-one completion: Thorner–Zaman (2019),
§2C, p.1049, Eq.(2-15). This is a conditional input, not an axiom.
No character sum estimate or new-paper conclusion is included. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def residueHeckeScale (q : Eisenstein) : ℝ := Real.sqrt (3*norm q)/(2*Real.pi)

/-- The standard analytic continuation and functional equation for a
primitive nonprincipal finite Hecke character with trivial infinity type.
The two Dirichlet series are literally those of the residue character
and its complex conjugate on the complete ideal exponent lattice. -/
def PrimitiveResidueHeckeInput : Prop :=
  ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → χ ≠ 1 →
    (∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1) →
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries (residueIdealChar q χ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries (residueIdealChar q (star χ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) 0 root L Ldual ∧
      CompletedHeckeFiniteOrder (residueHeckeScale q) L

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyLiftedPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local multiplicity of the reduced fractions and all their lattice translates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def HuxleyLift.frequency (i : HuxleyLift) : ℂ :=
  (i.numerator:ℂ)/(i.denominator:ℂ)+(i.shift:ℂ)

def HuxleyLift.reduced (Q : ℝ) (i : HuxleyLift) : Prop :=
  i.denominator ≠ 0 ∧ norm i.denominator ≤ Q ∧
    IsCoprime i.denominator i.numerator ∧
    residueRepresentative i.denominator (Ideal.Quotient.mk (modulus i.denominator) i.numerator) =
      i.numerator

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularConductorPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unit phase introduced by a harmonic Gaussian at the self-dual
Eisenstein conductor scale. -/
noncomputable section
namespace CubicFirstMoment

def angularConductorPhase (q : Eisenstein) : ℂ :=
  (-2*(Real.pi:ℂ)*Complex.I*(residueHeckeScale q:ℂ))/star ((q:ℂ)*traceLambda)

def angularConductorPhaseNeg (q : Eisenstein) : ℂ :=
  (-2*(Real.pi:ℂ)*Complex.I*(residueHeckeScale q:ℂ))/((q:ℂ)*traceLambda)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDualTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular far-left tail, with explicit natural dual length.
Only the constant changes with the angular shift; every power of the
length, conductor and height is retained from the full ideal series. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- The integrand of the omitted part of the functional-equation series
on the line `Re s = 1/2-m`. -/
def angularDualTailIntegrand (W : ℝ → ℂ) (χ : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A Z J k : ℝ) (m : ℕ) (t τ : ℝ) : ℂ :=
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
  let u : ℂ := s-(t:ℂ)*Complex.I
  mellin W s*(Z:ℂ)^s*ε*(A:ℂ)^(1-2*u)*
    (Complex.Gamma (1-u+(k:ℂ))/Complex.Gamma (u+(k:ℂ)))*idealDirichletTail χ J (1-u)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

/-- Full primitive coefficients, before removing any Euler factor. -/
def angularResidueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν : EisensteinIdealExponent) : ℂ :=
  residueIdealChar q χ ν*theta ℓ (idealExponentGenerator ν)

def primaryAngularMixedLift (ℓ : ℤ) (a b x : Eisenstein) : ℂ :=
  angularUnitCorrection ℓ x*primaryMixedLift a b x

lemma primaryAngularMixedLift_one (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) : primaryAngularMixedLift ℓ a b 1 = 1 := by
  rw [primaryAngularMixedLift, angularUnitCorrection_one, primaryMixedLift_one ha hb, mul_one]

lemma primaryAngularMixedLift_mul (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (x y : Eisenstein) :
    primaryAngularMixedLift ℓ a b (x*y) =
      primaryAngularMixedLift ℓ a b x*primaryAngularMixedLift ℓ a b y := by
  simp only [primaryAngularMixedLift, angularUnitCorrection_mul, primaryMixedLift_mul ha hb]
  ring

lemma primaryAngularMixedLift_congr (ℓ : ℤ) {a b x y : Eisenstein}
    (h : Ideal.Quotient.mk (modulus (3*(a*b))) x =
      Ideal.Quotient.mk (modulus (3*(a*b))) y) :
    primaryAngularMixedLift ℓ a b x = primaryAngularMixedLift ℓ a b y := by
  have hd : 3*(a*b) ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h3 : Ideal.Quotient.mk (modulus 3) x = Ideal.Quotient.mk (modulus 3) y :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ((dvd_mul_right 3 (a*b)).trans hd))
  rw [primaryAngularMixedLift, primaryAngularMixedLift,
    angularUnitCorrection_congr ℓ h3, primaryMixedLift_congr h]

/-- The actual finite part of `theta_l * mixedCubic a b`, with the
necessary unit compensation at 3. Its values on primary elements equal
the mixed cubic symbol, but its values on units depend on `ell`. -/
def primaryAngularMixedChar (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) : MulChar (Residues (3*(a*b))) ℂ where
  toFun v := primaryAngularMixedLift ℓ a b (residueRepresentative (3*(a*b)) v)
  map_one' := by
    rw [primaryAngularMixedLift_congr ℓ (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) 1) =
        Ideal.Quotient.mk (modulus (3*(a*b))) 1 by rw [residueRepresentative_spec, map_one])]
    exact primaryAngularMixedLift_one ℓ ha hb
  map_mul' v w := by
    rw [primaryAngularMixedLift_congr ℓ (show
      Ideal.Quotient.mk (modulus (3*(a*b))) (residueRepresentative (3*(a*b)) (v*w)) =
        Ideal.Quotient.mk (modulus (3*(a*b)))
          (residueRepresentative (3*(a*b)) v*residueRepresentative (3*(a*b)) w) by
            rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
              residueRepresentative_spec])]
    exact primaryAngularMixedLift_mul ℓ ha hb _ _
  map_nonunit' v hv := by
    rw [primaryAngularMixedLift,
      primaryMixedLift_nonunit ha hb (by rwa [residueRepresentative_spec]), mul_zero]

@[simp] lemma primaryAngularMixedChar_mk (ℓ : ℤ) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (x : Eisenstein) :
    primaryAngularMixedChar ℓ a b ha hb (Ideal.Quotient.mk (modulus (3*(a*b))) x) =
      primaryAngularMixedLift ℓ a b x :=
  primaryAngularMixedLift_congr ℓ (residueRepresentative_spec _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth for the shifted completion Gamma(s+k).
The input is the ordinary entire order-one completion, expressed by a
coarse quadratic exponential bound. All strip bounds are derived. -/
noncomputable section
open Set
namespace CubicFirstMoment

/-- Phragmen--Lindelof derives strip growth for the shifted completion
from its entire order-one bound. -/
structure ShiftedPrimitiveHeckeAnalyticData (χ χdual : EisensteinIdealExponent → ℂ)
    (A k : ℝ) (ε : ℂ) (L Ldual : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ L
  right_series : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s
  dual_right_series : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s
  functional_equation : HeckeFunctionalEquation A k ε L Ldual
  strip_growth : ∀ m : ℕ, ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧
    ∀ σ ∈ Icc (1/2-(m:ℝ)) 2, ∀ u : ℝ,
      ‖L (σ+(u:ℂ)*Complex.I)‖ ≤ C*(1+|u|)^n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeatLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular ideal/element theta reindexing, including all finite
Euler factors and the term at zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def angularLatticeHeat (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (A κ t : ℝ) : ℂ :=
  ∑' a : Eisenstein, (χ (Ideal.Quotient.mk (modulus q) a)*theta ℓ a)*
    ((norm a*t/A)^κ*Real.exp (-norm a*t/A):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedPrimitiveFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing the actual primitive characters for a finite family, with
uniform arithmetic conductor bounds. -/
noncomputable section
namespace CubicFirstMoment

def PrimitiveSmallTwistSpecification (a b r d : Eisenstein)
    (η : MulChar (Residues r) ℂ) (ψ : MulChar (Residues d) ℂ) : Prop :=
  d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
  (∀ v : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) v) = 1) ∧
  (∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) ∧
  (residueHeckeScale d)^2 ≤ 27*norm a*norm b*norm r/(2*Real.pi)^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short Möbius identity remains valid inside any fixed product of
prime-weight factors. This is the algebraic replacement before smoothing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def NormLocalEq (F : ℝ) (A B : EisensteinArithmeticFunction) : Prop :=
  ∀ ν, idealExponentNorm ν ≤ F → MvPowerSeries.coeff ν A = MvPowerSeries.coeff ν B

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryProductCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of ideal convolution coefficients with the finite
fibres of products of primary Eisenstein elements. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_eq_of_idealExponentOf_eq {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  rw [← idealPrimaryGenerator_at_element ha,← idealPrimaryGenerator_at_element hb,h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the original independently weighted prime tuples,
with the individual support and the global norm cutoff both retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateFactor (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (i : ι) (n : Eisenstein) : ℂ :=
  W i (norm n/X i)*η i (Ideal.Quotient.mk (modulus (q i)) n)*mellinPhase (t i) (norm n)

def coordinateSupport (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) (i : ι) : Finset Eisenstein :=
  (primaryElementBall (2*Y)).filter (fun n => W i (norm n/X i) ≠ 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedPrimitiveFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing the actual primitive characters for a finite family, with
uniform arithmetic conductor bounds and the exact angular unit condition. -/
noncomputable section
namespace CubicFirstMoment

def PrimitiveAngularSmallTwistSpecification (a b r d : Eisenstein)
    (η : MulChar (Residues r) ℂ) (ψ : MulChar (Residues d) ℂ) (ℓ : ℤ) : Prop :=
  d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
  AngularUnitCompatible d ψ ℓ ∧
  (∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) ∧
  (residueHeckeScale d)^2 ≤ 27*norm a*norm b*norm r/(2*Real.pi)^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular primitive input, and its first contour consequence.
Rajan, Acta Arith. 85 (1998), Section 1, pp.281--282, gives the completed
unitary Hecke equation and entire order-one completion. Here the field
has one complex place, discriminant 3, and no imaginary norm parameter.
The Gamma shift is therefore |ell|/2. No smooth-sum estimate is an input. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- Precise published continuation/functional equation for the actual
complete angular ideal coefficients. The dual has angle `-ell` and
conjugate finite character. The exceptional principal case is excluded. -/
def PrimitiveAngularHeckeInput : Prop :=
  ∀ (ℓ : ℤ) (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → AngularUnitCompatible q χ ℓ →
    (ℓ ≠ 0 ∨ χ ≠ 1) →
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar q χ ℓ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar q (star χ) (-ℓ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) (|(ℓ:ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) (|(ℓ:ℝ)|/2) L

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def cubicNumeratorLift (v x : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus 3) x) then
    cubicSymbol (primaryNormalize x) v else 0

lemma cubicNumeratorLift_congr (hpub : CubicSupplementaryPeriodicity)
    {v x y : Eisenstein} (hv : v ≠ 0)
    (h : Ideal.Quotient.mk (modulus (9*v)) x = Ideal.Quotient.mk (modulus (9*v)) y) :
    cubicNumeratorLift v x = cubicNumeratorLift v y := by
  have hd : 9*v ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h3d : (3:Eisenstein) ∣ 9*v := ⟨3*v,by ring⟩
  have h3 := residue_eq_of_dvd_sub (h3d.trans hd)
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hy : IsUnit (Ideal.Quotient.mk (modulus 3) y) := h3 ▸ hx
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hprim : primary (y*(u:Eisenstein)) := by
      apply (primary_iff_residue_one _).mpr
      rw [map_mul,← h3,← map_mul,hu]
      exact (primary_iff_residue_one _).mp (primaryNormalize_primary hx)
    have hnorm : primaryNormalize y = y*(u:Eisenstein) :=
      primary_associated_eq (primaryNormalize_primary hy) hprim
        ((primaryNormalize_associated y).symm.trans ⟨u,rfl⟩)
    simp only [cubicNumeratorLift,ite_eq_left hx,ite_eq_left hy]
    apply hpub v hv _ _ (primaryNormalize_primary hx) (primaryNormalize_primary hy)
    rw [hnorm,← hu,← sub_mul]
    exact dvd_mul_of_dvd_left hd _
  · have hy : ¬IsUnit (Ideal.Quotient.mk (modulus 3) y) := by simpa only [← h3] using hx
    simp only [cubicNumeratorLift,ite_eq_right hx,ite_eq_right hy]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularResidueLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor above three compensates the fixed infinity type.
It is one on every primary element, so it does not change the original sums. -/
noncomputable section
namespace CubicFirstMoment

def angularLiftResidueChar {q : Eisenstein} (η : MulChar (Residues q) ℂ) (ℓ : ℤ) :
    MulChar (Residues (q*3)) ℂ :=
  productResidueChar η (angularCorrectionChar ℓ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def fullPrimeSupport (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (i : ι) : Finset Eisenstein :=
  ((primaryElementBall (R*X i)).filter (fun n => W i (norm n/X i) ≠ 0)).filter Prime

def fullPrimeCoefficient (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (z : Eisenstein) : ℂ :=
  squarefreeConvolution (fullPrimeSupport R W X) (fun i n => W i (norm n/X i)) z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramMellin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation on the entire fixed norm range of a prime
convolution. The cutoff belongs to the transform, so no cutoff is inserted
into the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramLogKernel_smooth (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    ContDiff ℝ ∞ (wideGramLogKernel M hM W ρ) := by
  have he : (normProfileFourierSchwartz W hW hW' : ℂ → ℂ) = normProfileFourier W :=
    funext (normProfileFourierSchwartz_apply W hW hW')
  have hF : ContDiff ℝ ∞ (normProfileFourier W) := by
    rw [← he]
    exact (normProfileFourierSchwartz W hW hW').smooth ⊤
  apply (wideGramLogBump M hM).contDiff.smul
  exact hF.comp (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))))

def wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) : 𝓢(ℝ,ℂ) :=
  ((wideGramLogBump M hM).hasCompactSupport.smul_right (f' := fun u =>
    normProfileFourier W ((Real.sqrt ρ*Real.exp (u/2):ℝ):ℂ))).toSchwartzMap
      (wideGramLogKernel_smooth M hM W hW hW' ρ)

@[simp] lemma wideGramLogSchwartz_apply (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    wideGramLogSchwartz M hM W hW hW' ρ u = wideGramLogKernel M hM W ρ u := rfl

def wideGramMellinCoefficient (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ t : ℝ) : ℂ :=
  𝓕 (wideGramLogSchwartz M hM W hW hW' ρ) t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def wideAnnularLogSchwartz (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c : ℝ) : 𝓢(ℝ, ℂ) :=
  ((wideGramLogBump M hM).hasCompactSupport.smul_right (f' := fun u => F (c • gramExp u))).toSchwartzMap
    ((wideGramLogBump M hM).contDiff.smul ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)))

@[simp] lemma wideAnnularLogSchwartz_apply (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) :
    wideAnnularLogSchwartz M hM F c u = (wideGramLogBump M hM) u • F (c • gramExp u) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def normDenominatorMultiplier (M : ℝ) (hM : 0 < M) : 𝓢(ℝ,ℂ) :=
  ((wideGramLogBump (2*M) (by positivity)).hasCompactSupport.smul_right
    (f' := fun u => (Real.exp (u/2):ℂ))).toSchwartzMap
    ((wideGramLogBump (2*M) (by positivity)).contDiff.smul
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))))

def normDenominatorLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
    (wideGramLogSchwartz M hM W hW hW' ρ)

def normDenominatorMellinCoefficient (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ t : ℝ) : ℂ :=
  𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ) t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeightCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal angular prime coefficients and the two signed Mellin rows.
Only unit phases are removed; the angular index remains fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def angularHeightPrimeCoefficient (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (b : Eisenstein) : ℂ := fullPrimeCoefficient R W X b*theta ℓ b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

/-- The ordinary count of primary prime elements in the norm ball. -/
def primaryPrimeCount (X : ℝ) : ℝ := (primeCutoff X).card

/-- The ordinary prime ideal theorem, in the normalization used here.
The weighted first moment is proved below, rather than included in this input. -/
def PrimaryPrimePNT : Prop :=
  Tendsto (fun X => primaryPrimeCount X * Real.log X / X) atTop (𝓝 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedAngularHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fixed-angular Hecke prime estimates

The published input is the degree-two, nonexceptional specialization of
Kaneko--Thorner, *Highly uniform prime number theorems*, Ann. Inst. Fourier
75 (2025), Theorem 1.2, pp. 1904--1905 (restating Iwaniec--Kowalski,
Theorem 5.13), with the zero-free region and completion from Rajan (1998),
Proposition 1 and Section 1. The exponential conductor-dependent error
is retained. Arbitrary logarithmic savings are derived below; they are
not included among the published-input hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators

namespace CubicFirstMoment

/-- The actual fixed-angular character on the primary generators used by
this development. A nonzero angular index makes it nonprincipal. -/
def angularMixedCubic (ℓ : ℤ) (q₁ q₂ a : Eisenstein) : ℂ :=
  theta ℓ a * mixedCubic q₁ q₂ a

def angularAnalyticConductor (ℓ : ℤ) (q₁ q₂ : Eisenstein) : ℝ :=
  angularConductorFactor ℓ * norm (q₁ * q₂)

/-- Published fixed-type explicit prime estimate, before any logarithmic
saving is deduced. This is the degree-two, nonexceptional case of
Kaneko--Thorner Theorem 1.2 with Rajan's fixed-type zero-free region.
The displayed second term retains the cost of higher prime powers and
the omitted prime above three. It is an explicit input, not an axiom. -/
def FixedAngularPrimeExplicitEstimate : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → ∃ B c : ℝ, 0 < B ∧ 0 < c ∧
    ∀ q₁ q₂ : Eisenstein,
      primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ → IsCoprime q₁ q₂ →
      ∀ x : ℝ, 3 ≤ x →
        ‖primeChebyshev (angularMixedCubic ℓ q₁ q₂) x‖ ≤
          B * (heckeExponentialError c x (angularAnalyticConductor ℓ q₁ q₂) +
            Real.sqrt x * (Real.log x) ^ 2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularKummerAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular cubic character, with the argument order of the
cubic residue symbol. Only multiplicativity in the prime variable is used;
the fixed angular factor is not duplicated in the numerator variable. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def angularCubicSymbol (ℓ : ℤ) (a v : Eisenstein) : ℂ :=
  angularKummerCharacter ℓ v a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp fixed-angular prime model

The input is the explicit published Hecke prime estimate, not a weighted
prime-model asymptotic.  Partial summation with `x^(-1/6)/log x` derives
the required little-oh at the sharp first-moment scale.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

def angularChebyshevIntegrand (ℓ : ℤ) (t : ℝ) : ℝ :=
  |angularAbelDerivative t| * ‖primeChebyshev (theta ℓ) t‖

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularNumeratorCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction
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

def angularNumeratorLift (v : Eisenstein) (ℓ : ℤ) (x : Eisenstein) : ℂ :=
  cubicNumeratorLift v x*angularUnitCorrection ℓ x

lemma angularNumeratorLift_congr (hpub : CubicSupplementaryPeriodicity)
    {v x y : Eisenstein} (hv : v ≠ 0) (ℓ : ℤ)
    (h : Ideal.Quotient.mk (modulus (9*v)) x=Ideal.Quotient.mk (modulus (9*v)) y) :
    angularNumeratorLift v ℓ x=angularNumeratorLift v ℓ y := by
  have hd : 9*v ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h3 : (3:Eisenstein) ∣ x-y := (show (3:Eisenstein) ∣ 9*v from ⟨3*v,by ring⟩).trans hd
  rw [angularNumeratorLift,angularNumeratorLift,cubicNumeratorLift_congr hpub hv h,
    angularUnitCorrection_congr ℓ (residue_eq_of_dvd_sub h3)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyResiduePoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev HuxleyResidueIndex (Q : ℝ) :=
  Σ q : {q : Eisenstein // q ∈ nonzeroNormBall Q}, Residues q.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonProfileBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative profile budget is constructed from finitely many
Schwartz seminorms. It records only the two analytic costs used by the
Poisson argument; it is not an additional published input. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

structure PoissonProfileBudget where
  V : ℝ → ℂ
  compact : HasCompactSupport V
  smooth : ContDiff ℝ ∞ V
  cost : ℝ
  cost_pos : 0 < cost
  mellin : ∀ ρ : ℝ, 0 ≤ ρ →
    (1+ρ)^3*(∫ s : ℝ, ‖normDenominatorMellinCoefficient poissonProfileLogWidth
      poissonProfileLogWidth_pos V compact smooth ρ s‖) ≤ cost
  radial : ∀ t : ℝ, 0 ≤ t → (1+t)^47*‖radialDualProfile V t‖ ≤ cost
  wide : ∀ ρ : ℝ, 0 ≤ ρ →
    (1+ρ)^3*(∫ s : ℝ, ‖wideGramMellinCoefficient poissonProfileLogWidth
      poissonProfileLogWidth_pos V compact smooth ρ s‖) ≤ cost

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedKummerPrime
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite cubic prime input including the ramified part.

Thorner–Zaman, Algebra & Number Theory 13 (2019), Theorem 1.4, specialized
to the Kummer extension Q(ω, ∛v)/Q(ω). For v not a cube this is cyclic of
order three; weighting its three Frobenius classes by the cubic character
cancels the principal and possible real exceptional terms. The conductor
divides the modulus 9v supplied by cubic reciprocity (Dunn–Radziwiłł 2024,
§2, supplementary laws). Thus Nv bounded by a fixed log power suffices.
This is the same published finite-order prime input as PublishedHecke,
with units and primes above three retained, not a Gauss-sum conclusion.
Smooth weights, exclusions and convolution estimates are derived below.
-/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
namespace CubicFirstMoment

/-- The raw prime-sum specialization. Cubes and the zero numerator are
excluded explicitly; no smooth or structured-sum estimate is assumed. -/
def KummerPrimeSiegelWalfisz : Prop :=
  ∀ A D : ℝ, 0 < A → 0 < D → ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
    ∀ X : ℝ, X₀ ≤ X → ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log X)^A →
      ‖primeCutoffSum (fun p => cubicSymbol p v) X‖ ≤ C*X/(Real.log X)^D

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFactorUniqueness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the primary squarefree-times-cube coordinates in the
published cubic theta coefficient formulas. -/
noncomputable section
namespace CubicFirstMoment

/-- Primary normalization removes the cube-root unit ambiguity, and the
squarefree exponent is the residue modulo three of each prime valuation. -/
theorem primary_squarefree_cube_unique {c d c' d' : Eisenstein}
    (hc : primary c) (hd : primary d) (hc' : primary c') (hd' : primary d')
    (hcs : Squarefree c) (hcs' : Squarefree c') (he : c*d^3 = c'*d'^3) :
    c = c' ∧ d = d' := by
  have hce := (idealExponentOf_squarefree_iff (primary_ne_zero hc)).mpr hcs
  have hce' := (idealExponentOf_squarefree_iff (primary_ne_zero hc')).mpr hcs'
  have hexp := congrArg idealExponentOf he
  rw [idealExponentOf_mul (primary_ne_zero hc) (pow_ne_zero 3 (primary_ne_zero hd)),
    idealExponentOf_mul (primary_ne_zero hc') (pow_ne_zero 3 (primary_ne_zero hd')),
    idealExponentOf_pow (primary_ne_zero hd),idealExponentOf_pow (primary_ne_zero hd')] at hexp
  have hpoint (p : EisensteinIdealPrime) :
      idealExponentOf c p = idealExponentOf c' p ∧ idealExponentOf d p = idealExponentOf d' p := by
    have h := congrArg (fun f : EisensteinIdealExponent => f p) hexp
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul] at h
    have hc1 := hce p
    have hc2 := hce' p
    omega
  constructor
  · apply primary_eq_of_idealExponentOf_eq hc hc'
    ext p
    exact (hpoint p).1
  · apply primary_eq_of_idealExponentOf_eq hd hd'
    ext p
    exact (hpoint p).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness of the unit, ramified exponent and primary coordinates
needed to define the cubic theta coefficients without choices of associates. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_lambda_emultiplicity {a : Eisenstein} (ha : primary a) :
    emultiplicity lambdaE a = 0 := by
  apply emultiplicity_eq_zero.mpr
  intro hd
  exact lambdaE_prime.not_isUnit ((primary_coprime_lambda ha).isRelPrime hd dvd_rfl)

lemma unit_lambda_emultiplicity (u : Eisensteinˣ) :
    emultiplicity lambdaE (u:Eisenstein) = 0 := by
  apply emultiplicity_eq_zero.mpr
  intro hd
  exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd u.isUnit)

/-- The published decomposition is unique after imposing primarity. -/
theorem unit_ramified_primary_unique {u u' : Eisensteinˣ} {k k' : ℕ}
    {a a' : Eisenstein} (ha : primary a) (ha' : primary a')
    (he : (u:Eisenstein)*lambdaE^k*a = (u':Eisenstein)*lambdaE^k'*a') :
    u = u' ∧ k = k' ∧ a = a' := by
  have hm := congrArg (emultiplicity lambdaE) he
  simp only [emultiplicity_mul lambdaE_prime,emultiplicity_pow_self_of_prime lambdaE_prime,
    unit_lambda_emultiplicity,primary_lambda_emultiplicity ha,primary_lambda_emultiplicity ha',
    zero_add,add_zero] at hm
  have hk : k = k' := by exact_mod_cast hm
  subst k'
  have hc : (u:Eisenstein)*a = (u':Eisenstein)*a' := by
    apply mul_right_cancel₀ (pow_ne_zero k lambdaE_prime.ne_zero)
    calc
      _ = (u:Eisenstein)*lambdaE^k*a := by ring
      _ = (u':Eisenstein)*lambdaE^k*a' := he
      _ = _ := by ring
  have haa : a = a' := by
    apply primary_associated_eq ha ha'
    refine ⟨u*u'⁻¹,?_⟩
    rw [Units.val_mul]
    calc
      _ = ((u':Eisenstein)*a')*((u'⁻¹:Eisensteinˣ):Eisenstein) := by rw [←hc]; ring
      _ = _ := by simp [mul_assoc,mul_comm]
  have huu : u = u' := by
    apply Units.ext
    rw [←haa] at hc
    exact mul_right_cancel₀ (primary_ne_zero ha) hc
  exact ⟨huu,rfl,haa⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmetic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma CubicThetaCoordinates.ne_zero {n : Eisenstein} (R : CubicThetaCoordinates n) : n ≠ 0 := by
  rw [R.numerator_eq]
  exact mul_ne_zero (mul_ne_zero R.unit.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))
    (mul_ne_zero (primary_ne_zero R.squarefree_primary) (pow_ne_zero _ (primary_ne_zero R.cube_primary)))

lemma CubicThetaCoordinates.unique {n : Eisenstein} (R S : CubicThetaCoordinates n) : R = S := by
  have hpow (d : Eisenstein) (hd : primary d) : primary (d^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul hd (primary_mul hd hd)
  have hcpR := primary_mul R.squarefree_primary (hpow R.cubePart R.cube_primary)
  have hcpS := primary_mul S.squarefree_primary (hpow S.cubePart S.cube_primary)
  have h := unit_ramified_primary_unique hcpR hcpS (R.numerator_eq.symm.trans S.numerator_eq)
  have hc := primary_squarefree_cube_unique R.squarefree_primary R.cube_primary
    S.squarefree_primary S.cube_primary R.squarefree S.squarefree h.2.2
  exact CubicThetaCoordinates.ext h.1 h.2.1 hc.1 hc.2

/-- Unit phases in the first three cases of (5.7). Raising a sixth root
of unity to the fourth power removes its sign. -/
def cubicThetaUnitPhase (u : Eisensteinˣ) : ℂ :=
  if (u:Eisenstein)^4 = 1 then 1
  else if (u:Eisenstein)^4 = omegaE then (Real.fourierChar (-1/9) : ℂ)
  else (Real.fourierChar (1/9) : ℂ)

lemma cubicThetaUnitPhase_norm (u : Eisensteinˣ) : ‖cubicThetaUnitPhase u‖ = 1 := by
  unfold cubicThetaUnitPhase
  split_ifs <;> first | exact Circle.norm_coe _ | simp

/-- The normalized Gauss sum at an invertible additive frequency. -/
def cubicThetaTwistedGauss (c α : Eisenstein) : ℂ := star (cubicSymbol c α)*gauss c

lemma cubicThetaTwistedGauss_norm_le {c : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (α : Eisenstein) : ‖cubicThetaTwistedGauss c α‖ ≤ 1 := by
  rw [cubicThetaTwistedGauss,norm_mul,norm_star,norm_gauss_of_squarefree hc hs,mul_one]
  exact norm_cubicSymbol_le_one hc α

def CubicThetaCoordinates.amplitude {n : Eisenstein} (R : CubicThetaCoordinates n) : ℝ :=
  3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm R.cubePart)

lemma CubicThetaCoordinates.amplitude_nonneg {n : Eisenstein} (R : CubicThetaCoordinates n) :
    0 ≤ R.amplitude := by
  unfold amplitude
  exact div_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

lemma CubicThetaCoordinates.amplitude_le {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.amplitude ≤ 81 := by
  have hcs := one_le_norm (primary_ne_zero R.squarefree_primary)
  have hd := one_le_norm (primary_ne_zero R.cube_primary)
  have hc : 1 ≤ Real.sqrt (norm R.squarefreePart) := by
    simpa using Real.sqrt_le_sqrt hcs
  have hden : 1 ≤ Real.sqrt (norm R.squarefreePart)*norm R.cubePart :=
    one_le_mul_of_one_le_of_one_le hc hd
  have hpow : (3:ℝ)^(4-((R.order/3:ℕ):ℝ)) ≤ 81 := by
    calc
      _ ≤ (3:ℝ)^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have h := Nat.cast_nonneg (R.order/3) (α := ℝ); linarith)
      _ = 81 := by norm_num
  exact (div_le_self (by positivity) hden).trans hpow

def CubicThetaCoordinates.coefficient {n : Eisenstein} (R : CubicThetaCoordinates n) : ℂ :=
  if R.order % 3 = 0 ∧ 3 ≤ R.order then
    (R.amplitude:ℂ)*cubicThetaUnitPhase R.unit*
      star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2))
  else if R.order % 3 = 1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein) = -1) then
    (R.amplitude:ℂ)*star (gauss R.squarefreePart)
  else 0

lemma CubicThetaCoordinates.coefficient_norm_le {n : Eisenstein} (R : CubicThetaCoordinates n) :
    ‖R.coefficient‖ ≤ 81 := by
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact (mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)).trans R.amplitude_le
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact R.amplitude_le
  · norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCubeScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube multiplication in the literal Patterson coefficient formula,
including its unit and ramified cases. -/
noncomputable section
namespace CubicFirstMoment

def CubicThetaCoordinates.mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) :
    CubicThetaCoordinates (n*e^3) where
  unit := R.unit
  order := R.order
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart*e
  squarefree_primary := R.squarefree_primary
  cube_primary := primary_mul R.cube_primary he
  squarefree := R.squarefree
  numerator_eq := by
    calc
      n*e^3 = ((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3))*e^3 :=
        congrArg (fun x => x*e^3) R.numerator_eq
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma cubicTheta_unit_norm (u : Eisensteinˣ) : ‖((u:Eisenstein):ℂ)‖ = 1 := by
  have h := norm_of_isUnit u.isUnit
  change Complex.normSq ((u:Eisenstein):ℂ) = 1 at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [_root_.norm_nonneg ((u:Eisenstein):ℂ)]

def CubicThetaCoordinates.cuspCoefficient {n : Eisenstein}
    (R : CubicThetaCoordinates n) (j : Fin 3) : ℂ :=
  if j = 0 then R.coefficient
  else if R.order = 0 ∧ ((j = 1 ∧ (R.unit:Eisenstein)^3 = 1) ∨
      (j = 2 ∧ (R.unit:Eisenstein)^3 = -1)) then
    (R.amplitude:ℂ)*omega^(j:ℕ)*((R.unit:Eisenstein):ℂ)^4*cubicThetaUnitPhase R.unit*
      star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2))
  else 0

lemma CubicThetaCoordinates.cuspCoefficient_norm_le {n : Eisenstein}
    (R : CubicThetaCoordinates n) (j : Fin 3) : ‖R.cuspCoefficient j‖ ≤ 81 := by
  unfold cuspCoefficient
  split_ifs
  · exact R.coefficient_norm_le
  · simp only [norm_mul,norm_pow,cubicTheta_unit_norm,cubicThetaUnitPhase_norm,
      one_pow,mul_one,norm_star]
    have hω : ‖omega‖ = 1 := by
      have h := cubicTheta_unit_norm (Units.mkOfMulEqOne omegaE (omegaE^2) (by
        rw [mul_comm,←pow_succ,omegaE_cube]))
      exact h
    rw [hω,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg R.amplitude_nonneg]
    exact (mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)).trans R.amplitude_le
  · norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEven
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The evenness of the cubic theta coefficients, derived directly from
all cases of the arithmetic formula, and the resulting horizontal symmetry. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def CubicThetaCoordinates.neg {n : Eisenstein} (R : CubicThetaCoordinates n) :
    CubicThetaCoordinates (-n) where
  unit := -R.unit
  order := R.order
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := R.cube_primary
  squarefree := R.squarefree
  numerator_eq := by
    calc
      _ = -((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3)) :=
        congrArg Neg.neg R.numerator_eq
      _ = _ := by simp

lemma CubicThetaCoordinates.neg_coefficient {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.neg.coefficient = R.coefficient := by
  have hu : ((-R.unit:Eisensteinˣ):Eisenstein)^4 = (R.unit:Eisenstein)^4 := by
    norm_num [Units.val_neg,neg_pow]
  have hs : ((-R.unit:Eisensteinˣ):Eisenstein) = 1 ∨
      ((-R.unit:Eisensteinˣ):Eisenstein) = -1 ↔
      (R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1 := by
    simp only [Units.val_neg,neg_eq_iff_eq_neg,neg_neg,or_comm]
  unfold coefficient cubicThetaUnitPhase
  simp only [neg,hu,hs,amplitude]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrincipalTrace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The level-three determinant identity forces the trace to be 2 modulo
9. Together with the elliptic trace bound, this isolates trace 2 without
an assumed torsion-freeness theorem. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrincipal_trace_mod_nine (g : cubicThetaPrincipalGroup) :
    (9:Eisenstein) ∣ g.val 0 0+g.val 1 1-2 := by
  obtain ⟨a,ha⟩ := (cubicThetaPrincipalGroup_diagonal_primary g).1
  obtain ⟨d,hd⟩ := (cubicThetaPrincipalGroup_diagonal_primary g).2
  obtain ⟨b,hb⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
  obtain ⟨c,hc⟩ := (cubicThetaPrincipalGroup_offDiagonal g).2
  have h00 : g.val 0 0=1+3*a := by linear_combination ha
  have h11 : g.val 1 1=1+3*d := by linear_combination hd
  have he := cubicThetaPrincipalGroup_det g
  rw [h00,h11,hb,hc] at he
  refine ⟨-(a*d-b*c),?_⟩
  rw [h00,h11]
  linear_combination he

lemma cubicThetaPrincipal_trace_eq_two_of_norm_le (g : cubicThetaPrincipalGroup)
    (h : ‖((g.val 0 0+g.val 1 1:Eisenstein):ℂ)‖ ≤ 2) :
    g.val 0 0+g.val 1 1=2 := by
  by_contra hn
  let w := g.val 0 0+g.val 1 1-2
  have hw : w≠0 := sub_ne_zero.mpr hn
  obtain ⟨t,ht⟩ := cubicThetaPrincipal_trace_mod_nine g
  have ht0 : t≠0 := by
    intro he
    apply hw
    change g.val 0 0+g.val 1 1-2=0
    rw [ht,he,mul_zero]
  have hlarge : 81 ≤ norm w := by
    change 81 ≤ norm (g.val 0 0+g.val 1 1-2)
    rw [ht]
    change 81 ≤ Complex.normSq (((9:Eisenstein):ℂ)*(t:ℂ))
    rw [Complex.normSq_mul]
    have hn9 : norm (9:Eisenstein)=81 := by
      change Complex.normSq (9:ℂ)=81
      norm_num [Complex.normSq_apply]
    change 81 ≤ norm (9:Eisenstein)*norm t
    rw [hn9]
    nlinarith [one_le_norm ht0]
  have hsmall : ‖(w:ℂ)‖ ≤ 4 := by
    change ‖((g.val 0 0+g.val 1 1:Eisenstein):ℂ)-(2:ℂ)‖ ≤ 4
    have h' : ‖((g.val 0 0+g.val 1 1:Eisenstein):ℂ)‖+‖(2:ℂ)‖ ≤ 4 := by
      have hn2 : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
      rw [hn2]
      linarith only [h]
    exact (norm_sub_le _ _).trans h'
  rw [norm,Complex.normSq_eq_norm_sq] at hlarge
  nlinarith [_root_.norm_nonneg (w:ℂ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def cubicThetaPrimitiveRow (g : SL(2,Eisenstein)) : CubicThetaPrimitiveRow :=
  ⟨g 1 0,g 1 1,⟨-g 0 1,g 0 0,by
    have h : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
    linear_combination h⟩⟩

lemma cubicThetaPrimitiveRow_surjective : Function.Surjective cubicThetaPrimitiveRow := by
  intro r
  obtain ⟨a,b,h⟩ := r.coprime
  let g : SL(2,Eisenstein) := ⟨!![b,-a;r.c,r.d],by
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩
  exact ⟨g,by ext <;> rfl⟩

def CubicThetaPrimitiveRow.denominator (r : CubicThetaPrimitiveRow) (p : ℂ × ℝ) : ℝ :=
  Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2

def CubicThetaPrimitiveRow.height (r : CubicThetaPrimitiveRow) (p : ℂ × ℝ) : ℝ :=
  p.2/r.denominator p

lemma CubicThetaPrimitiveRow.denominator_pos (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : 0 < r.denominator p := by
  rcases r.coprime.ne_zero_or_ne_zero with hc | hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hp))
  · by_cases hc : r.c=0
    · simpa [CubicThetaPrimitiveRow.denominator,hc,norm] using Complex.normSq_pos.mpr
        (show (r.d:ℂ)≠0 from fun h => hd (Subtype.ext h))
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
        (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hp))

lemma CubicThetaPrimitiveRow.height_pos (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : 0 < r.height p := div_pos hp (r.denominator_pos hp)

lemma CubicThetaPrimitiveRow.norm_sum_bound (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    norm r.c+norm r.d ≤ (2+(1+2*Complex.normSq p.1)/p.2^2)*r.denominator p := by
  let D := r.denominator p
  have hc : norm r.c ≤ D/p.2^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    dsimp [D,CubicThetaPrimitiveRow.denominator]
    linarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d)]
  have hd : norm r.d ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+2*norm r.c*Complex.normSq p.1 := by
    have h : Complex.normSq (((r.c:ℂ)*p.1+r.d)-(r.c:ℂ)*p.1) ≤
        2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+2*Complex.normSq ((r.c:ℂ)*p.1) := by
      simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
      nlinarith [sq_nonneg (((r.c:ℂ)*p.1+r.d).re+((r.c:ℂ)*p.1).re),
        sq_nonneg (((r.c:ℂ)*p.1+r.d).im+((r.c:ℂ)*p.1).im)]
    rw [add_sub_cancel_left,Complex.normSq_mul] at h
    simpa only [norm,mul_assoc] using h
  calc
    _ ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+(1+2*Complex.normSq p.1)*norm r.c := by linarith
    _ ≤ 2*D+(1+2*Complex.normSq p.1)*(D/p.2^2) := by
      apply add_le_add
      · dsimp [D,CubicThetaPrimitiveRow.denominator]
        linarith [mul_nonneg (norm_nonneg r.c) (sq_nonneg p.2)]
      · exact mul_le_mul_of_nonneg_left hc (by linarith [Complex.normSq_nonneg p.1])
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSiegelReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def cubicThetaFullInversion : SL(2,Eisenstein) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactRowBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform arithmetic row bounds for transformations between two
compact positive-height charts. These bounds give local finiteness of
the actual arithmetic action. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompact_bottomRow_bound {K L : Set (ℂ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKpos : ∀ p∈K, 0<p.2) (hLpos : ∀ p∈L, 0<p.2) :
    ∃ B : ℝ, ∀ g : SL(2,Eisenstein), ∀ p∈K,
      cubicThetaMobius (cubicThetaFullComplex g) p∈L → norm (g 1 0)+norm (g 1 1) ≤ B := by
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (heightControl_continuousOn hKpos)
  obtain ⟨B,hB⟩ := hL.exists_bound_of_continuousOn (inverseHeight_continuousOn hLpos)
  refine ⟨max A 0*max B 0,?_⟩
  intro g p hp hq
  let q := cubicThetaMobius (cubicThetaFullComplex g) p
  let r := cubicThetaPrimitiveRow g
  have hp0 := hKpos p hp
  have hq0 : 0<q.2 := hLpos q hq
  have he : r.denominator p=p.2/q.2 := by
    change r.denominator p=p.2/r.height p
    unfold CubicThetaPrimitiveRow.height
    field_simp [(r.denominator_pos hp0).ne',hp0.ne']
  have hrow := r.norm_sum_bound hp0
  have he' : (2+(1+2*Complex.normSq p.1)/p.2^2)*r.denominator p=
      heightControl p*(1/q.2) := by rw [he]; unfold heightControl; ring
  rw [he'] at hrow
  have hAp : heightControl p ≤ max A 0 :=
    (le_abs_self _).trans ((hA p hp).trans (le_max_left _ _))
  have hBq : 1/q.2 ≤ max B 0 :=
    (le_abs_self _).trans ((hB q hq).trans (le_max_left _ _))
  exact hrow.trans (mul_le_mul hAp hBq (by positivity) (le_max_right _ _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactTransporters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only finitely many Eisenstein matrices can carry one compact
positive-height chart into another. This proves the local finiteness
needed for the quotient construction. -/
noncomputable section
open Set
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFullInversion_bottomRow (g : SL(2,Eisenstein)) :
    (cubicThetaFullInversion*g) 1 0=g 0 0 ∧ (cubicThetaFullInversion*g) 1 1=g 0 1 := by
  change ((!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*(g:Matrix (Fin 2) (Fin 2) Eisenstein)) 1 0=g 0 0 ∧
    ((!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*(g:Matrix (Fin 2) (Fin 2) Eisenstein)) 1 1=g 0 1
  simp [Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaCompact_transporter_finite {K L : Set (ℂ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKpos : ∀ p∈K, 0<p.2) (hLpos : ∀ p∈L, 0<p.2) :
    Set.Finite {g : SL(2,Eisenstein) | ∃ p∈K, cubicThetaMobius (cubicThetaFullComplex g) p∈L} := by
  let L' := cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) '' L
  have hL' : IsCompact L' := hL.image_of_continuousOn
    (cubicThetaMobius_continuousOn _ hLpos)
  have hL'pos : ∀ p∈L', 0<p.2 := by
    rintro p ⟨q,hq,rfl⟩
    exact cubicThetaMobius_height_pos _ (hLpos q hq)
  obtain ⟨B1,hB1⟩ := cubicThetaCompact_bottomRow_bound hK hL hKpos hLpos
  obtain ⟨B2,hB2⟩ := cubicThetaCompact_bottomRow_bound hK hL' hKpos hL'pos
  let B := max B1 B2
  have hi : Function.Injective (fun g : SL(2,Eisenstein) => ((g 0 0,g 0 1),(g 1 0,g 1 1))) := by
    intro g h he
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun t => t.1.1) he
    · exact congrArg (fun t => t.1.2) he
    · exact congrArg (fun t => t.2.1) he
    · exact congrArg (fun t => t.2.2) he
  have hfin : Set.Finite {g : SL(2,Eisenstein) |
      (norm (g 0 0) ≤ B ∧ norm (g 0 1) ≤ B) ∧ (norm (g 1 0) ≤ B ∧ norm (g 1 1) ≤ B)} :=
    (((finite_norm_le B).prod (finite_norm_le B)).prod
      ((finite_norm_le B).prod (finite_norm_le B))).preimage hi.injOn
  apply hfin.subset
  rintro g ⟨p,hp,hq⟩
  have hb1 := hB1 g p hp hq
  have hq' : cubicThetaMobius (cubicThetaFullComplex (cubicThetaFullInversion*g)) p∈L' := by
    refine ⟨cubicThetaMobius (cubicThetaFullComplex g) p,hq,?_⟩
    rw [map_mul,← cubicThetaMobius_comp _ _ (hKpos p hp)]
  have hb2 := hB2 (cubicThetaFullInversion*g) p hp hq'
  rw [(cubicThetaFullInversion_bottomRow g).1,(cubicThetaFullInversion_bottomRow g).2] at hb2
  have h1 : B1 ≤ B := le_max_left _ _
  have h2 : B2 ≤ B := le_max_right _ _
  exact ⟨⟨by linarith [norm_nonneg (g 0 1)],by linarith [norm_nonneg (g 0 0)]⟩,
    ⟨by linarith [norm_nonneg (g 1 1)],by linarith [norm_nonneg (g 1 0)]⟩⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProperAction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Eisenstein and principal-group actions are properly
discontinuous. This supplies the topological quotient needed for global
cusp gluing from proved compact-chart transport bounds. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFullPointAction_apply (g : SL(2,Eisenstein)) (p : CubicThetaPoint) :
    (g • p).val=cubicThetaMobius (cubicThetaFullComplex g) p.val := rfl

instance cubicThetaFullPointAction_continuous : ContinuousConstSMul SL(2,Eisenstein) CubicThetaPoint where
  continuous_const_smul g := by
    change Continuous (fun p : CubicThetaPoint =>
      (⟨cubicThetaMobius (cubicThetaFullComplex g) p.val,
        cubicThetaMobius_height_pos _ p.property⟩ : CubicThetaPoint))
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaMobius_continuousAt (cubicThetaFullComplex g) p.property).comp
      (x:=p) (f:=fun q : CubicThetaPoint => q.val) continuous_subtype_val.continuousAt

instance cubicThetaFullPointAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul SL(2,Eisenstein) CubicThetaPoint where
  finite_disjoint_inter_image := by
    intro K L hK hL
    have hK' := hK.image continuous_subtype_val
    have hL' := hL.image continuous_subtype_val
    have hKpos : ∀ p∈Subtype.val '' K, 0<p.2 := by
      rintro p ⟨q,_,rfl⟩
      exact q.property
    have hLpos : ∀ p∈Subtype.val '' L, 0<p.2 := by
      rintro p ⟨q,_,rfl⟩
      exact q.property
    apply (cubicThetaCompact_transporter_finite hK' hL' hKpos hLpos).subset
    rintro g ⟨q,⟨⟨p,hp,rfl⟩,hq⟩⟩
    refine ⟨p.val,⟨p,hp,rfl⟩,g • p,hq,?_⟩
    exact cubicThetaFullPointAction_apply g p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

instance cubicThetaPrincipalPointAction_continuous :
    ContinuousConstSMul cubicThetaPrincipalGroup CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

abbrev CubicThetaQuotient :=
  Quotient (MulAction.orbitRel cubicThetaPrincipalGroup CubicThetaPoint)

def cubicThetaQuotientMap : CubicThetaPoint → CubicThetaQuotient :=
  Quotient.mk (MulAction.orbitRel cubicThetaPrincipalGroup CubicThetaPoint)

lemma cubicThetaQuotientMap_surjective : Function.Surjective cubicThetaQuotientMap :=
  Quotient.mk_surjective

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeAction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The level-three quotient is a genuine covering: the actual principal
congruence action has no nontrivial point stabilizers. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipal_fixed_eq_one (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint)
    (hg : g • p=p) : g=1 := by
  have hp : cubicThetaMobius (cubicThetaPrincipalComplex g) p.val=p.val :=
    congrArg Subtype.val hg
  have ht := cubicThetaFixed_trace_norm p (cubicThetaPrincipalComplex g) hp
  have ht' := cubicThetaPrincipal_trace_eq_two_of_norm_le g (by
    simpa only [cubicThetaPrincipalComplex_apply,Subalgebra.coe_add] using ht)
  apply cubicThetaPrincipalComplex_injective
  rw [map_one]
  apply cubicThetaFixed_trace_two p _ hp
  change ((g.val 0 0:Eisenstein):ℂ)+((g.val 1 1:Eisenstein):ℂ)=2
  change ((g.val 0 0+g.val 1 1:Eisenstein):ℂ)=((2:Eisenstein):ℂ)
  exact congrArg Subtype.val ht'

instance cubicThetaPrincipalPointAction_free :
    IsCancelSMul cubicThetaPrincipalGroup CubicThetaPoint :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr cubicThetaPrincipal_fixed_eq_one

lemma cubicThetaQuotient_covering :
    IsQuotientCoveringMap cubicThetaQuotientMap cubicThetaPrincipalGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

lemma cubicThetaQuotient_localHomeomorph : IsLocalHomeomorph cubicThetaQuotientMap :=
  cubicThetaQuotient_covering.isCoveringMap.isLocalHomeomorph

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientCharts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def cubicThetaQuotientLift (q : CubicThetaQuotient) : CubicThetaPoint :=
  Classical.choose (cubicThetaQuotientMap_surjective q)

lemma cubicThetaQuotientLift_map (q : CubicThetaQuotient) :
    cubicThetaQuotientMap (cubicThetaQuotientLift q)=q :=
  Classical.choose_spec (cubicThetaQuotientMap_surjective q)

def cubicThetaCoveringChart (p : CubicThetaPoint) :
    OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient :=
  Classical.choose (cubicThetaQuotient_localHomeomorph p)

lemma cubicThetaCoveringChart_source (p : CubicThetaPoint) :
    p∈(cubicThetaCoveringChart p).source :=
  (Classical.choose_spec (cubicThetaQuotient_localHomeomorph p)).1

lemma cubicThetaCoveringChart_coe (p : CubicThetaPoint) :
    (cubicThetaCoveringChart p : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap :=
  (Classical.choose_spec (cubicThetaQuotient_localHomeomorph p)).2.symm

def cubicThetaQuotientChart (q : CubicThetaQuotient) :
    OpenPartialHomeomorph CubicThetaQuotient (ℂ × ℝ) :=
  (cubicThetaCoveringChart (cubicThetaQuotientLift q)).symm.trans cubicThetaPointInclusion

lemma cubicThetaQuotientChart_source (q : CubicThetaQuotient) :
    q∈(cubicThetaQuotientChart q).source := by
  let p := cubicThetaQuotientLift q
  have hp := (cubicThetaCoveringChart p).map_source (cubicThetaCoveringChart_source p)
  rw [cubicThetaCoveringChart_coe,cubicThetaQuotientLift_map] at hp
  exact ⟨hp,by rw [cubicThetaPointInclusion_source]; trivial⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAutomorphicSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous sections with the actual cubic multiplier. Their norm
descends to the arithmetic quotient, and quotient cutoffs localize them. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAutomorphicSections : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrincipalGroup, ∀ p : CubicThetaPoint,
    F (g • p)=cubicThetaKubotaValue g*F p}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g p
    change F (g • p)+G (g • p)=cubicThetaKubotaValue g*(F p+G p)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro c F hF g p
    change c*F (g • p)=cubicThetaKubotaValue g*(c*F p)
    rw [hF]
    ring

abbrev CubicThetaSection := cubicThetaAutomorphicSections

def cubicThetaSectionNorm (F : CubicThetaSection) (q : CubicThetaQuotient) : ℝ :=
  ‖F.val (cubicThetaQuotientLift q)‖

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable choice of representatives for the actual principal
quotient, obtained from a countable disjoint refinement of covering charts. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

instance cubicThetaQuotient_measurableSpace : MeasurableSpace CubicThetaQuotient := borel _
instance cubicThetaQuotient_borelSpace : BorelSpace CubicThetaQuotient := ⟨rfl⟩

lemma cubicThetaQuotientChart_source_eq (c : CubicThetaQuotient) :
    (cubicThetaQuotientChart c).source=
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)).target := by
  ext q
  change (q∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).target ∧
    (cubicThetaCoveringChart (cubicThetaQuotientLift c)).symm q∈cubicThetaPointInclusion.source)↔_
  rw [cubicThetaPointInclusion_source]
  simp only [mem_univ,and_true]

lemma cubicTheta_countable_chart_cover :
    ∃ c : ℕ → CubicThetaQuotient, ∀ q, ∃ n, q∈(cubicThetaQuotientChart (c n)).source := by
  obtain ⟨S,hSc,hS⟩ := isLindelof_univ.elim_countable_subcover
    (fun c : CubicThetaQuotient => (cubicThetaQuotientChart c).source)
    (fun c => (cubicThetaQuotientChart c).open_source) (by
      intro q _
      exact mem_iUnion.mpr ⟨q,cubicThetaQuotientChart_source q⟩)
  have hSne : S.Nonempty := by
    let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
    obtain ⟨c,hc,_⟩ := mem_iUnion₂.mp (hS (mem_univ (cubicThetaQuotientMap p)))
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hSc.exists_eq_range hSne
  refine ⟨c,fun q => ?_⟩
  obtain ⟨d,hd,hqd⟩ := mem_iUnion₂.mp (hS (mem_univ q))
  rw [hc] at hd
  obtain ⟨n,rfl⟩ := hd
  exact ⟨n,hqd⟩

def cubicThetaAtlasCenter : ℕ → CubicThetaQuotient :=
  Classical.choose cubicTheta_countable_chart_cover

def cubicThetaAtlasOpen (n : ℕ) : Set CubicThetaQuotient :=
  (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).source

def cubicThetaAtlasPiece (n : ℕ) : Set CubicThetaQuotient :=
  disjointed cubicThetaAtlasOpen n

lemma cubicThetaAtlasPiece_measurable (n : ℕ) : MeasurableSet (cubicThetaAtlasPiece n) :=
  MeasurableSet.disjointed (fun n => (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).open_source.measurableSet) n

lemma cubicThetaAtlasPiece_cover : ⋃ n, cubicThetaAtlasPiece n=univ := by
  change (⋃ n, disjointed cubicThetaAtlasOpen n)=univ
  rw [iUnion_disjointed]
  apply eq_univ_of_forall
  intro q
  exact mem_iUnion.mpr (Classical.choose_spec cubicTheta_countable_chart_cover q)

def cubicThetaAtlasLocalLift (n : ℕ) : CubicThetaQuotient → CubicThetaPoint :=
  (cubicThetaAtlasOpen n).piecewise
    (cubicThetaCoveringChart (cubicThetaQuotientLift (cubicThetaAtlasCenter n))).symm
    (fun _ => cubicThetaQuotientLift (cubicThetaAtlasCenter n))

lemma cubicThetaAtlasLocalLift_measurable (n : ℕ) : Measurable (cubicThetaAtlasLocalLift n) := by
  apply ContinuousOn.measurable_piecewise
  · change ContinuousOn _ (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).source
    rw [cubicThetaQuotientChart_source_eq]
    exact (cubicThetaCoveringChart _).symm.continuousOn
  · exact continuous_const.continuousOn
  · exact (cubicThetaQuotientChart (cubicThetaAtlasCenter n)).open_source.measurableSet

lemma cubicThetaAtlasLocalLift_rightInverse (n : ℕ) {q : CubicThetaQuotient}
    (hq : q∈cubicThetaAtlasPiece n) :
    cubicThetaQuotientMap (cubicThetaAtlasLocalLift n q)=q := by
  have hu := disjointed_subset cubicThetaAtlasOpen n hq
  rw [cubicThetaAtlasLocalLift,piecewise_eq_of_mem _ _ _ hu]
  rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift (cubicThetaAtlasCenter n))]
  apply (cubicThetaCoveringChart _).right_inv
  exact (cubicThetaQuotientChart_source_eq _ ▸ hu)

lemma cubicTheta_measurable_section_exists :
    ∃ s : CubicThetaQuotient → CubicThetaPoint,
      Measurable s ∧ Function.RightInverse s cubicThetaQuotientMap := by
  obtain ⟨s,hs,hse⟩ := exists_measurable_piecewise cubicThetaAtlasPiece
    cubicThetaAtlasPiece_measurable cubicThetaAtlasLocalLift cubicThetaAtlasLocalLift_measurable (by
      intro i j hij q hq
      exact False.elim (Set.disjoint_left.mp (disjoint_disjointed cubicThetaAtlasOpen hij) hq.1 hq.2))
  refine ⟨s,hs,fun q => ?_⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp (cubicThetaAtlasPiece_cover.symm ▸ mem_univ q)
  rw [hse n hn]
  exact cubicThetaAtlasLocalLift_rightInverse n hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFundamentalDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish
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

def cubicThetaBorelSection : CubicThetaQuotient → CubicThetaPoint :=
  Classical.choose cubicTheta_measurable_section_exists

def cubicThetaFundamentalDomain : Set CubicThetaPoint :=
  {p | cubicThetaBorelSection (cubicThetaQuotientMap p)=p}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHyperbolicMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish
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

def cubicThetaQuotientMeasure : Measure CubicThetaQuotient :=
  (cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain).map cubicThetaQuotientMap

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothTests
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth sections and their actual Euclidean localizations.
The derivatives here are derivatives of the section, rather than extra
independent data attached to a test vector. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaSmoothTests : Submodule ℂ CubicThetaSection where
  carrier := {F | ContDiffOn ℝ ∞ (fun y => F.val (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2} ∧ HasCompactSupport (cubicThetaSectionNorm F)}
  zero_mem' := by
    constructor
    · change ContDiffOn ℝ ∞ (fun _ : ℂ × ℝ => (0:ℂ)) _
      exact contDiffOn_const
    · change HasCompactSupport (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)
      have he : (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)=(0 : CubicThetaQuotient → ℝ) := by
        funext q
        exact norm_zero
      rw [he]
      exact HasCompactSupport.zero
  add_mem' := by
    rintro F G ⟨hF,hFc⟩ ⟨hG,hGc⟩
    refine ⟨hF.add hG,?_⟩
    apply (hFc.add hGc).mono'
    intro q hq
    contrapose! hq
    have hz : cubicThetaSectionNorm F q=0 ∧ cubicThetaSectionNorm G q=0 := by
      have h := image_eq_zero_of_notMem_tsupport hq
      exact ⟨(add_eq_zero_iff_of_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp h |>.1,
        (add_eq_zero_iff_of_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp h |>.2⟩
    simp only [Function.mem_support,not_not,cubicThetaSectionNorm,norm_eq_zero] at hz ⊢
    change F.val (cubicThetaQuotientLift q)+G.val (cubicThetaQuotientLift q)=0
    rw [hz.1,hz.2,add_zero]
  smul_mem' := by
    rintro c F ⟨hF,hFc⟩
    refine ⟨contDiffOn_const.mul hF,?_⟩
    apply hFc.mono'
    intro q hq
    contrapose! hq
    have hz := image_eq_zero_of_notMem_tsupport hq
    simp only [Function.mem_support,not_not]
    change ‖c*F.val (cubicThetaQuotientLift q)‖=0
    change ‖F.val (cubicThetaQuotientLift q)‖=0 at hz
    rw [norm_eq_zero] at hz
    rw [hz,mul_zero,norm_zero]

def cubicThetaTestLocalization (φ : ℂ × ℝ → ℂ) (F : CubicThetaSection)
    (y : ℂ × ℝ) : ℂ := φ y*F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaTestLocalization_smooth {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) : ContDiff ℝ ∞ (cubicThetaTestLocalization φ F) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y.2
  · exact (hφ.contDiffOn.mul F.property.1).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)
  · have hout : y∉tsupport (cubicThetaTestLocalization φ F) := by
      intro h
      exact hy (hp (tsupport_mul_subset_left h))
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ × ℝ => (0:ℂ)) y).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

lemma cubicThetaTestLocalization_compact {φ : ℂ × ℝ → ℂ}
    (hφ : HasCompactSupport φ) (F : CubicThetaSection) :
    HasCompactSupport (cubicThetaTestLocalization φ F) := hφ.mul_right

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalL2
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

abbrev CubicThetaGlobalL2 := Lp ℂ 2 cubicThetaQuotientMeasure

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalGradient
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
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

abbrev CubicThetaGradientL2 := Lp CubicThetaGradient 2 cubicThetaQuotientMeasure

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant coefficient on cubes as the kernel size of the actual
reduction of residue units to modulus three. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaReductionThree (c : Eisenstein) : Residues (3*c) →+* Residues 3 :=
  residueReduction (show (3:Eisenstein) ∣ 3*c from ⟨c,rfl⟩)

abbrev CubicThetaPrimaryResidue (c : Eisenstein) :=
  {x : Residues (3*c) // IsUnit x ∧ cubicThetaReductionThree c x = 1}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaNonzeroCube := {c : Eisenstein // c≠0 ∧ ∃ j : Eisenstein, j^3=c}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedIdeal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single ramified ideal in the cube part of the constant term. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedPrime : EisensteinIdealPrime :=
  ⟨Associates.mk lambdaE,Associates.irreducible_mk.mpr lambdaE_prime.irreducible⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts
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

abbrev CubicThetaGlobalEnergyAmbient := WithLp 2 (CubicThetaGlobalL2 × CubicThetaGradientL2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStrip
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

def cubicThetaPeriodCoordinates (z : ℂ) : Fin 2 → ℝ :=
  eisensteinRealCoords.symm (z/3)

def cubicThetaCuspStrip (H : ℝ) : Set CubicThetaPoint :=
  {p | H<(cubicThetaPointCoordinates p).2 ∧
    ∀ i, cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1 i∈Ico (0:ℝ) 1}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTranslatedCuspStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def cubicThetaPrincipalConjugate (δ : SL(2,Eisenstein)) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalGroup :=
  ⟨δ⁻¹*g.val*δ,by
    let ρ : SL(2,Eisenstein) →* SL(2,Residues (3:Eisenstein)) :=
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))
    change ρ (δ⁻¹*g.val*δ)=1
    have hg : ρ g.val=1 := g.property
    rw [map_mul,map_mul,map_inv,hg,mul_one,inv_mul_cancel]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCuspRestriction
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

abbrev CubicThetaStripL2 := Lp ℂ 2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyGraph
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local graph of genuine compact smooth sections and its closed
Hilbert energy space. The value and derivative entries remain tied to the
same localized section throughout the construction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaTestLocalization_add (φ : ℂ × ℝ → ℂ) (F G : cubicThetaSmoothTests) :
    cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection)=cubicThetaTestLocalization φ F+cubicThetaTestLocalization φ G := by
  funext y
  change φ y*(F.val.val _+G.val.val _)=φ y*F.val.val _+φ y*G.val.val _
  exact mul_add _ _ _

lemma cubicThetaTestLocalization_smul (φ : ℂ × ℝ → ℂ) (c : ℂ) (F : cubicThetaSmoothTests) :
    cubicThetaTestLocalization φ ((c • F : cubicThetaSmoothTests) : CubicThetaSection)=c • cubicThetaTestLocalization φ F := by
  funext y
  change φ y*(c*F.val.val _)=c*(φ y*F.val.val _)
  ring

lemma cubicThetaLocalSectionJet_memLp {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F)) 2
      (volume : Measure (ℂ × ℝ)) :=
  cubicThetaLocalEnergyJet_memLp ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (cubicThetaTestLocalization_compact hc F) (tsupport_mul_subset_left.trans hp)

def cubicThetaLocalEnergyGraph {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaSmoothTests →ₗ[ℂ] CubicThetaLocalEnergyAmbient where
  toFun F := (cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp (F+G)).coeFn_toLp,
      (cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp,
      (cubicThetaLocalSectionJet_memLp hφ hc hp G).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _)
        ((cubicThetaLocalSectionJet_memLp hφ hc hp G).toLp _)] with y hFG hF hG hadd
    simp only [Pi.add_apply] at hadd
    rw [hFG,hadd,hF,hG,cubicThetaTestLocalization_add]
    exact cubicThetaLocalEnergyJet_add
      ((cubicThetaTestLocalization_smooth hφ hp F).differentiable (by simp))
      ((cubicThetaTestLocalization_smooth hφ hp G).differentiable (by simp)) y
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp (c • F)).coeFn_toLp,
      (cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _)] with y hCF hF hsmul
    simp only [Pi.smul_apply] at hsmul
    simp only [RingHom.id_apply]
    rw [hCF,hsmul,hF,cubicThetaTestLocalization_smul]
    exact cubicThetaLocalEnergyJet_smul c
      ((cubicThetaTestLocalization_smooth hφ hp F).differentiable (by simp)) y

def cubicThetaLocalEnergySpace {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    Submodule ℂ CubicThetaLocalEnergyAmbient :=
  (cubicThetaLocalEnergyGraph hφ hc hp).range.topologicalClosure

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalizationSobolevBound
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Sobolev bounds for the actual localized sections. Together
with the proved supported compact inclusion, these control the core
localization by its hyperbolic energy graph norm. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev

def localizedPair {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) :=
  (realH1 (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (cubicThetaTestLocalization_compact hc F),
    imagH1 (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (cubicThetaTestLocalization_compact hc F))

lemma localizedPair_bound {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ F : cubicThetaSmoothTests,
      ‖localizedPair hφ hc hp F‖^2≤C*‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2 := by
  obtain ⟨C,hC,hbound⟩ := compact_sobolev_bound hc hp
  refine ⟨C,hC,fun F => ?_⟩
  have h := hbound (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (cubicThetaTestLocalization_compact hc F) tsupport_mul_subset_left
  have hn : ‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2=
      ∫ y, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2 := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp] with y hy
    change ‖((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _) y‖^2=_
    rw [hy]
  rw [hn]
  exact h

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalizationLinear
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real linearity of the actual localized Sobolev vectors, with their
fixed compact support retained in the codomain. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

local instance localizationLinear_borel_r2d7b3b_1 : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance localizationLinear_borelSpace_r2d7b3b_1 : BorelSpace CubicThetaTangent := ⟨rfl⟩
def localizedRealTest : cubicThetaSmoothTests →ₗ[ℝ] C1c (E:=CubicThetaTangent) where
  toFun F := realTest (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (cubicThetaTestLocalization_compact hc F)
  map_add' F G := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection) _).re =
      (cubicThetaTestLocalization φ F _).re+(cubicThetaTestLocalization φ G _).re
    rw [cubicThetaTestLocalization_add]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ (((c:ℂ) • F : cubicThetaSmoothTests) : CubicThetaSection) _).re =
      c*(cubicThetaTestLocalization φ F _).re
    rw [cubicThetaTestLocalization_smul]
    simp

def localizedImagTest : cubicThetaSmoothTests →ₗ[ℝ] C1c (E:=CubicThetaTangent) where
  toFun F := imagTest (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (cubicThetaTestLocalization_compact hc F)
  map_add' F G := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection) _).im =
      (cubicThetaTestLocalization φ F _).im+(cubicThetaTestLocalization φ G _).im
    rw [cubicThetaTestLocalization_add]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    funext u
    change (cubicThetaTestLocalization φ (((c:ℂ) • F : cubicThetaSmoothTests) : CubicThetaSection) _).im =
      c*(cubicThetaTestLocalization φ F _).im
    rw [cubicThetaTestLocalization_smul]
    simp

def localizedRealH1 : cubicThetaSmoothTests →ₗ[ℝ] h1 (μ:=tangentBorelVolume) :=
  ((graph (μ:=tangentBorelVolume)).comp (localizedRealTest hφ hc hp)).codRestrict _
    (fun F => Submodule.le_topologicalClosure _ ⟨localizedRealTest hφ hc hp F,rfl⟩)

def localizedImagH1 : cubicThetaSmoothTests →ₗ[ℝ] h1 (μ:=tangentBorelVolume) :=
  ((graph (μ:=tangentBorelVolume)).comp (localizedImagTest hφ hc hp)).codRestrict _
    (fun F => Submodule.le_topologicalClosure _ ⟨localizedImagTest hφ hc hp F,rfl⟩)

def localizedRealSupported : cubicThetaSmoothTests →ₗ[ℝ] Supported (tsupport φ) hc :=
  (localizedRealH1 hφ hc hp).codRestrict _ (fun F =>
    (realSupported hc (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (cubicThetaTestLocalization_compact hc F) tsupport_mul_subset_left).property)

def localizedImagSupported : cubicThetaSmoothTests →ₗ[ℝ] Supported (tsupport φ) hc :=
  (localizedImagH1 hφ hc hp).codRestrict _ (fun F =>
    (imagSupported hc (cubicThetaTestLocalization φ F)
      ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (cubicThetaTestLocalization_compact hc F) tsupport_mul_subset_left).property)

def localizedSupportedPair : cubicThetaSmoothTests →ₗ[ℝ]
    (Supported (tsupport φ) hc × Supported (tsupport φ) hc) :=
  (localizedRealSupported hφ hc hp).prod (localizedImagSupported hφ hc hp)

lemma localizedSupportedPair_norm (F : cubicThetaSmoothTests) :
    ‖localizedSupportedPair hφ hc hp F‖=‖localizedPair hφ hc hp F‖ := rfl

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyRellich
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rellich compactness on the completion of the actual local energy
graph. No independent value and derivative data are introduced. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance energyRellich_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.energyRellich_borel
attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.energyRellich_borelSpace
local instance energyRellich_supportedBounded_r2d7b3b_1 (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsBoundedSMul ℝ (Supported K hK) where
  dist_smul_pair' c u v := by
    change dist (c • (u.val.val : H1Target (μ:=tangentBorelVolume)))
        (c • (v.val.val : H1Target (μ:=tangentBorelVolume)))≤
      dist c 0*dist (u.val.val : H1Target (μ:=tangentBorelVolume)) v.val.val
    exact dist_smul_pair c _ _
  dist_pair_smul' c d u := by
    change dist (c • (u.val.val : H1Target (μ:=tangentBorelVolume)))
        (d • (u.val.val : H1Target (μ:=tangentBorelVolume)))≤
      dist c d*dist (u.val.val : H1Target (μ:=tangentBorelVolume)) 0
    exact dist_pair_smul c d _
def localEnergyTest : cubicThetaSmoothTests →ₗ[ℝ] cubicThetaLocalEnergySpace hφ hc hp :=
  ((cubicThetaLocalEnergyGraph hφ hc hp).restrictScalars ℝ).codRestrict
    ((cubicThetaLocalEnergySpace hφ hc hp).restrictScalars ℝ)
    (fun F => Submodule.le_topologicalClosure (cubicThetaLocalEnergyGraph hφ hc hp).range ⟨F,rfl⟩)

lemma localEnergyTest_norm (F : cubicThetaSmoothTests) :
    ‖localEnergyTest hφ hc hp F‖=‖cubicThetaLocalEnergyGraph hφ hc hp F‖ := rfl

lemma localEnergyTest_dense : DenseRange (localEnergyTest hφ hc hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (localEnergyTest hφ hc hp)=
      Set.range (cubicThetaLocalEnergyGraph hφ hc hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨localEnergyTest hφ hc hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

local instance energyRellich_pairBounded_r2d7b3b_1 (K : Set (ℂ × ℝ)) (hK : IsCompact K) :
    IsBoundedSMul ℝ (Supported K hK × Supported K hK) where
  dist_smul_pair' c u v := by
    let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
      (u.1.val.val,u.2.val.val)
    let v₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
      (v.1.val.val,v.2.val.val)
    change dist (c • u₀) (c • v₀)≤dist c 0*dist u₀ v₀
    exact dist_smul_pair c u₀ v₀
  dist_pair_smul' c d u := by
    let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
      (u.1.val.val,u.2.val.val)
    change dist (c • u₀) (d • u₀)≤dist c d*dist u₀ 0
    exact dist_pair_smul c d u₀
lemma localizedSupportedPair_bound : ∃ C, ∀ F : cubicThetaSmoothTests,
    ‖localizedSupportedPair hφ hc hp F‖≤C*‖localEnergyTest hφ hc hp F‖ := by
  obtain ⟨C,hC,hbound⟩ := localizedPair_bound hφ hc hp
  refine ⟨Real.sqrt C,fun F => ?_⟩
  have hs : ‖localizedSupportedPair hφ hc hp F‖^2≤C*‖localEnergyTest hφ hc hp F‖^2 := by
    rw [localizedSupportedPair_norm hφ hc hp F,localEnergyTest_norm hφ hc hp F]
    exact hbound F
  have he : (Real.sqrt C*‖localEnergyTest hφ hc hp F‖)^2=
      C*‖localEnergyTest hφ hc hp F‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  exact _root_.le_of_sq_le_sq (hs.trans_eq he.symm)
    (mul_nonneg (Real.sqrt_nonneg C) (_root_.norm_nonneg (localEnergyTest hφ hc hp F)))

def localEnergyToSupported : cubicThetaLocalEnergySpace hφ hc hp →L[ℝ]
    (Supported (tsupport φ) hc × Supported (tsupport φ) hc) :=
  @LinearMap.extendOfNorm ℝ ℝ (↥cubicThetaSmoothTests)
    (↥(cubicThetaLocalEnergySpace hφ hc hp))
    (↥(Supported (tsupport φ) hc) × ↥(Supported (tsupport φ) hc))
    inferInstance inferInstance (RingHom.id ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (by
      constructor
      · intro c u v
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        let v₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (v.1.val.val,v.2.val.val)
        change dist (c • u₀) (c • v₀)≤dist c 0*dist u₀ v₀
        exact dist_smul_pair c u₀ v₀
      · intro c d u
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        change dist (c • u₀) (d • u₀)≤dist c d*dist u₀ 0
        exact dist_pair_smul c d u₀) inferInstance inferInstance
    (@CompleteSpace.prod (Supported (tsupport φ) hc) (Supported (tsupport φ) hc)
      _ _ (supported_complete (tsupport φ) hc) (supported_complete (tsupport φ) hc))
    (localizedSupportedPair hφ hc hp) (localEnergyTest hφ hc hp)

lemma localEnergyToSupported_test (F : cubicThetaSmoothTests) :
    localEnergyToSupported hφ hc hp (localEnergyTest hφ hc hp F)=
      localizedSupportedPair hφ hc hp F :=
  @LinearMap.extendOfNorm_eq ℝ ℝ (↥cubicThetaSmoothTests)
    (↥(cubicThetaLocalEnergySpace hφ hc hp))
    (↥(Supported (tsupport φ) hc) × ↥(Supported (tsupport φ) hc))
    inferInstance inferInstance (RingHom.id ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (by
      constructor
      · intro c u v
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        let v₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (v.1.val.val,v.2.val.val)
        change dist (c • u₀) (c • v₀)≤dist c 0*dist u₀ v₀
        exact dist_smul_pair c u₀ v₀
      · intro c d u
        let u₀ : H1Target (μ:=tangentBorelVolume) × H1Target (μ:=tangentBorelVolume) :=
          (u.1.val.val,u.2.val.val)
        change dist (c • u₀) (d • u₀)≤dist c d*dist u₀ 0
        exact dist_pair_smul c d u₀) inferInstance inferInstance
    (@CompleteSpace.prod (Supported (tsupport φ) hc) (Supported (tsupport φ) hc)
      _ _ (supported_complete (tsupport φ) hc) (supported_complete (tsupport φ) hc))
    (localizedSupportedPair hφ hc hp) (localEnergyTest hφ hc hp)
    (localEnergyTest_dense hφ hc hp)
    (localizedSupportedPair_bound hφ hc hp) F

def localEnergyInclusion : cubicThetaLocalEnergySpace hφ hc hp →L[ℝ] TangentComplexL2 :=
  (complexInclusion (tsupport φ) hc).comp (localEnergyToSupported hφ hc hp)

theorem localEnergyInclusion_compact : IsCompactOperator (localEnergyInclusion hφ hc hp) :=
  (complexInclusion_compact (tsupport φ) hc).comp_clm (localEnergyToSupported hφ hc hp)

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalRellichValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact local energy inclusion has the original localized
complex section as its value, rather than an unrelated Sobolev vector. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment.LocalSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.rellichValue_borel
attribute [local instance] OAI.CubicFirstMoment.LocalSobolev.rellichValue_borelSpace
theorem localEnergyInclusion_test {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) :
    localEnergyInclusion hφ hc hp (localEnergyTest hφ hc hp F)=
      tangentFunctionL2 (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (cubicThetaTestLocalization_compact hc F) := by
  change complexInclusion (tsupport φ) hc
    (localEnergyToSupported hφ hc hp (localEnergyTest hφ hc hp F))=_
  rw [localEnergyToSupported_test]
  exact complexInclusion_value hc _ _ _ tsupport_mul_subset_left

end CubicFirstMoment.LocalSobolev

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreMassFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite family of actual core cutoffs is a compact Hilbert-valued
operator; its norm is the sum of the individual squared L2 norms. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

abbrev CubicThetaCoreValueFamily (A : Finset CubicThetaQuotient) :=
  lp (fun _ : A => CubicThetaGlobalL2) 2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveCuspRestriction
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

abbrev CubicThetaPositiveStripL2 (ε : ℝ) :=
  Lp ℂ 2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal half-open level-three cell is a fundamental domain for
horizontal translations. This is the measure bridge for Hecke constant modes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def CubicThetaPeriodGroup := Multiplicative Eisenstein

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def CubicThetaScaledPeriodGroup (_a : Eisenstein) := Multiplicative Eisenstein

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowCompletionTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

theorem cubicThetaBottomRow_equal_translation (g h : cubicThetaPrincipalGroup)
    (he : cubicThetaBottomRow g=cubicThetaBottomRow h) :
    ∃ w : Eisenstein,g=cubicThetaPrincipalTranslation w*h := by
  have hc : g.val 1 0=h.val 1 0 := congrArg CubicThetaBottomRow.c he
  have hd : g.val 1 1=h.val 1 1 := congrArg CubicThetaBottomRow.d he
  let d := g*h⁻¹
  have h10 : d.val 1 0=0 := by
    change (g.val*h.val⁻¹) 1 0=0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    change g.val 1 0*h.val 1 1+g.val 1 1*(-h.val 1 0)=0
    rw [hc,hd]
    ring
  have h11 : d.val 1 1=1 := by
    change (g.val*h.val⁻¹) 1 1=1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    change g.val 1 0*(-h.val 0 1)+g.val 1 1*h.val 0 0=1
    rw [hc,hd]
    linear_combination cubicThetaPrincipalGroup_det h
  have h00 : d.val 0 0=1 := by
    have H := cubicThetaPrincipalGroup_det d
    rw [h10,h11,mul_one,mul_zero,sub_zero] at H
    exact H
  obtain ⟨w,hw⟩ := (cubicThetaPrincipalGroup_offDiagonal d).1
  have hT : d=cubicThetaPrincipalTranslation w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact hw
    · exact h10
    · exact h11
  refine ⟨w,?_⟩
  rw [←hT]
  dsimp only [d]
  rw [mul_assoc,inv_mul_cancel,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimePowerFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma cubicThetaSymbol_prime_pow {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (x : Eisenstein) : cubicSymbol (p^n) x=(cubicSymbol p x)^n := by
  induction n with
  | zero => rw [pow_zero,pow_zero,cubicSymbol_one_lower]
  | succ n ih =>
    rw [pow_succ,cubicSymbol_mul_lower (pow_ne_zero n hp.2.ne_zero) hp.2.ne_zero,ih,pow_succ]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeValuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaDenominator := {c : Eisenstein // (3:Eisenstein) ∣ c ∧ c≠0}
abbrev CubicThetaPrimeFreeDenominator (p : Eisenstein) :=
  {c : Eisenstein // (3:Eisenstein) ∣ c ∧ c≠0 ∧ ¬p ∣ c}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeIwahori
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

lemma cubicThetaPrimeIwahori_diagonal_coprime {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori p) :
    IsCoprime p (g.val.val 0 0) := by
  apply hp.2.coprime_iff_not_dvd.mpr
  intro hd
  exact hp.2.not_isUnit ((cubicThetaPrincipalGroup_column_coprime g.val).isRelPrime hd g.property)

lemma cubicThetaPrimeIwahoriCharacter_cube {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) : (cubicThetaPrimeIwahoriCharacter p hp g)^3=1 :=
  cubicSymbol_cube_of_isCoprime hp.1 _ (cubicThetaPrimeIwahori_diagonal_coprime hp g)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def CubicThetaInvertedRow.height (r : CubicThetaInvertedRow) (p : ℂ × ℝ) : ℝ :=
  p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion preserves the actual cubic multiplier. Consequently its
pullback acts on genuine automorphic sections, with no new multiplier input. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaInversionConjugate_entries (g : cubicThetaPrincipalGroup) :
    (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g).val 0 0=g.val 1 1 ∧
    (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g).val 1 0= -g.val 0 1 := by
  have hi : (cubicThetaFullInversion⁻¹:SL(2,Eisenstein)).val=!![0,1;-1,0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    change Matrix.adjugate !![(0:Eisenstein),-1;1,0]=_
    simp [Matrix.adjugate_fin_two]
  change ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹) 0 0=g.val 1 1 ∧
    ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹) 1 0= -g.val 0 1
  rw [inv_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul,hi]
  simp [cubicThetaFullInversion,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAtkinConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime Atkin involution on the actual arithmetic subgroup. Its
cubic twist disappears on the kernel of the diagonal character. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeAtkinConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) : cubicThetaPrimeIwahori p :=
  ⟨cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate hp.1 g),by
    have he := (cubicThetaInversionConjugate_entries (cubicThetaPrimeConjugate hp.1 g)).2
    change p∣(cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate hp.1 g)).val 1 0
    rw [he]
    change p∣-(p*g.val.val 0 1)
    exact dvd_neg.mpr (dvd_mul_right p _)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAtkinInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime normalizer is an actual involution, not just a map of
multiplier values. This supplies the group equivalence for the finite cover. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimeAtkinConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    ((cubicThetaPrimeAtkinConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p);-p*g.val.val 0 1,g.val.val 0 0] := by
  change (((cubicThetaFullInversion⁻¹)⁻¹*
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero hp.1) g*
      cubicThetaFullInversion⁻¹ : SL(2,Eisenstein)) : Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [inv_inv,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [cubicThetaFullInversion,cubicThetaPrimeConjugatedMatrix,Matrix.adjugate_fin_two]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAtkinAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complex prime normalizer and its action on positive-height
points. The intertwining identity uses the constructed arithmetic involution. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeAtkinMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation hp.2.ne_zero

theorem cubicThetaPrimeAtkinMatrix_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeAtkinMatrix hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeAtkinConjugate hp g).val*
        cubicThetaPrimeAtkinMatrix hp := by
  have he : cubicThetaPrincipalComplex (cubicThetaPrimeAtkinConjugate hp g).val=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 g)*
          (cubicThetaFullComplex cubicThetaFullInversion)⁻¹ := by
    change cubicThetaFullComplex ((cubicThetaFullInversion⁻¹)⁻¹*
      (cubicThetaPrimeConjugate hp.1 g).val*cubicThetaFullInversion⁻¹)=_
    rw [inv_inv,map_mul,map_mul,map_inv]
    rfl
  rw [cubicThetaPrimeAtkinMatrix,mul_assoc,cubicThetaPrimeDilation_intertwines hp.1 g,he]
  group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowTranslationEquiv
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of the principal arithmetic group into the
level-three translation stabilizer and primitive bottom rows. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBottomRow_left_translation (w : Eisenstein) (g : cubicThetaPrincipalGroup) :
    cubicThetaBottomRow (cubicThetaPrincipalTranslation w*g)=cubicThetaBottomRow g := by
  apply CubicThetaBottomRow.ext
  · change ((cubicThetaPrincipalTranslation w).val.val*g.val.val) 1 0=g.val 1 0
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change 0*g.val 0 0+1*g.val 1 0=g.val 1 0
    ring
  · change ((cubicThetaPrincipalTranslation w).val.val*g.val.val) 1 1=g.val 1 1
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change 0*g.val 0 1+1*g.val 1 1=g.val 1 1
    ring

lemma cubicThetaPrincipalTranslation_injective : Function.Injective cubicThetaPrincipalTranslation := by
  intro w z h
  have he : (3:Eisenstein)*w=3*z := congrArg (fun g : cubicThetaPrincipalGroup => g.val 0 1) h
  exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) he

def cubicThetaRowTranslationMap (wr : Eisenstein × CubicThetaBottomRow) : cubicThetaPrincipalGroup :=
  cubicThetaPrincipalTranslation wr.1*wr.2.completion

lemma cubicThetaRowTranslationMap_injective : Function.Injective cubicThetaRowTranslationMap := by
  rintro ⟨w,r⟩ ⟨z,s⟩ h
  have hrs : r=s := by
    have he := congrArg cubicThetaBottomRow h
    simpa only [cubicThetaRowTranslationMap,cubicThetaBottomRow_left_translation,
      CubicThetaBottomRow.completion_row] using he
  subst s
  have ht : cubicThetaPrincipalTranslation w=cubicThetaPrincipalTranslation z := mul_right_cancel h
  exact Prod.ext (cubicThetaPrincipalTranslation_injective ht) rfl

lemma cubicThetaRowTranslationMap_surjective : Function.Surjective cubicThetaRowTranslationMap := by
  intro g
  obtain ⟨w,hw⟩ := cubicThetaBottomRow_equal_translation g (cubicThetaBottomRow g).completion
    (CubicThetaBottomRow.completion_row _).symm
  exact ⟨(w,cubicThetaBottomRow g),hw.symm⟩

def cubicThetaRowTranslationEquiv : (Eisenstein × CubicThetaBottomRow) ≃ cubicThetaPrincipalGroup :=
  Equiv.ofBijective cubicThetaRowTranslationMap
    ⟨cubicThetaRowTranslationMap_injective,cubicThetaRowTranslationMap_surjective⟩

@[simp] lemma cubicThetaRowTranslationEquiv_apply (w : Eisenstein) (r : CubicThetaBottomRow) :
    cubicThetaRowTranslationEquiv (w,r)=cubicThetaPrincipalTranslation w*r.completion := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional root conjugation preserves the actual cubic Kubota
multiplier on its arithmetic subgroup. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeRootConjugate hp x g).val=
      cubicThetaKubotaValue g.val := by
  have hM : cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1
      (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g)))=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g)) := by
    rw [cubicThetaPrimeRootConjugate_dilation,cubicThetaKubotaValue_mul,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,
      cubicThetaPrincipalTranslation_inverse_value,one_mul,mul_one]
  have hleft := cubicThetaPrimeConjugate_kubota hp
    (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))
  change cubicThetaKubotaValue (cubicThetaPrimeRootConjugate hp x g).val=
    cubicSymbol p ((cubicThetaPrimeRootConjugate hp x g).val.val 0 0)*
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1
        (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))) at hleft
  rw [cubicThetaPrimeRootConjugate_diagonal_character,hM] at hleft
  exact hleft.trans (cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeRootIwahori g)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def cubicThetaPrimeCubeRootCoverGroup {p : Eisenstein} (_hp : primaryPrime p) :
    Subgroup cubicThetaPrincipalGroup := cubicThetaPrimeCubeRootSubgroup p

def cubicThetaPrimeCubeRootTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeCubeRootCoverGroup hp).exists_isComplement_right 1)

def cubicThetaPrimeCubeRootCoverDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeCubeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complex root element acts on the arithmetic subgroup with
its original cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaPrimeRootElement_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootElement hp x*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val*
        cubicThetaPrimeRootElement hp x := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let q := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g))
  let q' := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1
    (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g)))
  have hg : D*cubicThetaPrincipalComplex g.val=q*D :=
    cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori g)
  have hg' : D*cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val=q'*D :=
    cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori (cubicThetaPrimeRootConjugate hp x g))
  have hq : q'=t*q*t⁻¹ := by
    change cubicThetaPrincipalComplex _=_
    rw [cubicThetaPrimeRootConjugate_dilation,map_mul,map_mul,map_inv]
  have ht : t*q=q'*t := by rw [hq]; group
  have hg'' : D⁻¹*q'*D=cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val := by
    rw [mul_assoc,←hg']
    group
  change D⁻¹*t*D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val*(D⁻¹*t*D)
  calc
    _ = D⁻¹*t*(D*cubicThetaPrincipalComplex g.val) := by group
    _ = D⁻¹*t*(q*D) := by rw [hg]
    _ = D⁻¹*(t*q)*D := by group
    _ = D⁻¹*(q'*t)*D := by rw [ht]
    _ = (D⁻¹*q'*D)*(D⁻¹*t*D) := by group
    _ = _ := by rw [hg'']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSections
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-cover section space and its fractional root action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimeRootPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeRootElement hp x • (g.val • y)=
      (cubicThetaPrimeRootConjugate hp x g).val • (cubicThetaPrimeRootElement hp x • y) := by
  change cubicThetaPrimeRootElement hp x • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val •
      (cubicThetaPrimeRootElement hp x • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeRootElement_intertwines]

lemma cubicThetaPrimeRootPoint_continuous {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : Continuous (fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) := by
  change Continuous (fun y : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeRootElement hp x) y.val,
      cubicThetaMobius_height_pos _ y.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cubicThetaMobius_continuousAt _ y.property).comp
    (x:=y) (f:=fun z : CubicThetaPoint => z.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeRootSections (p : Eisenstein) : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ∀ g : cubicThetaPrimeRootSubgroup p, ∀ y : CubicThetaPoint,
    F (g.val • y)=cubicThetaKubotaValue g.val*F y}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG g y
    change F (g.val • y)+G (g.val • y)=cubicThetaKubotaValue g.val*(F y+G y)
    rw [hF,hG]
    ring
  smul_mem' := by
    intro a F hF g y
    change a*F (g.val • y)=cubicThetaKubotaValue g.val*(a*F y)
    rw [hF]
    ring

def cubicThetaPrimeRootSectionTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeRootElement hp x • y),
    F.val.continuous.comp (cubicThetaPrimeRootPoint_continuous hp x)⟩,by
    intro g y
    change F.val (cubicThetaPrimeRootElement hp x • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeRootElement hp x • y)
    rw [cubicThetaPrimeRootPoint_intertwines,F.property,cubicThetaPrimeRootConjugate_kubota]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the prime residue field. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootElement_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) :
    cubicThetaPrimeRootElement hp (x+y)=
      cubicThetaPrimeRootElement hp x*cubicThetaPrimeRootElement hp y := by
  simp only [cubicThetaPrimeRootElement_translation]
  apply Subtype.ext
  change (!![1,((3*(x+y):Eisenstein):ℂ)/(p:ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)=
    !![1,((3*x:Eisenstein):ℂ)/(p:ℂ);0,1]*!![1,((3*y:Eisenstein):ℂ)/(p:ℂ);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_add,add_div,add_comm]

lemma cubicThetaPrimeRootElement_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootElement hp (p*x)=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) := by
  rw [cubicThetaPrimeRootElement_translation,cubicThetaPrincipalTranslation_complex]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootOperators
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual linear root translations on the finite-cover section space.
Integral translations act trivially, so the operators depend only on the
residue class of their parameter modulo the prime. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSection_integral {p : Eisenstein}
    (F : cubicThetaPrimeRootSections p) (x : Eisenstein) (y : CubicThetaPoint) :
    F.val (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) • y)=F.val y := by
  have he := F.property (cubicThetaPrimeRootIntegralTranslation p x) y
  change F.val (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x) • y)=
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation x)*F.val y at he
  simpa only [cubicThetaPrincipalTranslation_value,one_mul] using he

lemma cubicThetaPrimeRootSectionTranslate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootSectionTranslate hp (x+y) F=
      cubicThetaPrimeRootSectionTranslate hp x (cubicThetaPrimeRootSectionTranslate hp y F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeRootElement hp (x+y) • z)=
    F.val (cubicThetaPrimeRootElement hp y • (cubicThetaPrimeRootElement hp x • z))
  rw [←mul_smul,←cubicThetaPrimeRootElement_add,add_comm]

@[simp] lemma cubicThetaPrimeRootSectionTranslate_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootSectionTranslate hp 0 F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeRootElement hp 0 • z)=F.val z
  rw [cubicThetaPrimeRootElement_zero,one_smul]

lemma cubicThetaPrimeRootSectionTranslate_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootSectionTranslate hp (p*x) F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeRootElement hp (p*x) • y)=F.val y
  rw [cubicThetaPrimeRootElement_integral,cubicThetaPrimeRootSection_integral]

def cubicThetaPrimeRootOperator {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeRootSections p ≃ₗ[ℂ] cubicThetaPrimeRootSections p where
  toFun := cubicThetaPrimeRootSectionTranslate hp x
  invFun := cubicThetaPrimeRootSectionTranslate hp (-x)
  left_inv F := by
    rw [←cubicThetaPrimeRootSectionTranslate_add,neg_add_cancel,
      cubicThetaPrimeRootSectionTranslate_zero]
  right_inv F := by
    rw [←cubicThetaPrimeRootSectionTranslate_add,add_neg_cancel,
      cubicThetaPrimeRootSectionTranslate_zero]
  map_add' F G := rfl
  map_smul' a F := rfl

theorem cubicThetaPrimeRootOperator_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p∣x-y) :
    cubicThetaPrimeRootOperator hp x=cubicThetaPrimeRootOperator hp y := by
  obtain ⟨z,hz⟩ := hxy
  have hx : x=y+p*z := by linear_combination hz
  apply LinearEquiv.ext
  intro F
  change cubicThetaPrimeRootSectionTranslate hp x F=
    cubicThetaPrimeRootSectionTranslate hp y F
  rw [hx,cubicThetaPrimeRootSectionTranslate_add,
    cubicThetaPrimeRootSectionTranslate_integral]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootSections
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual sections and their fractional translations at the cube modulus. -/
noncomputable section
namespace CubicFirstMoment

abbrev cubicThetaPrimeCubeRootSections (p : Eisenstein) := cubicThetaPrimeRootSections (p^3)

lemma cubicThetaPrimeCubeRootPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeCubeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeCubeRootElement hp x • (g.val • y)=
      (cubicThetaPrimeCubeRootConjugate hp x g).val • (cubicThetaPrimeCubeRootElement hp x • y) := by
  change cubicThetaPrimeCubeRootElement hp x • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootConjugate hp x g).val •
      (cubicThetaPrimeCubeRootElement hp x • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeRootElement_intertwines]

lemma cubicThetaPrimeCubeRootPoint_continuous {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : Continuous (fun y : CubicThetaPoint => cubicThetaPrimeCubeRootElement hp x • y) := by
  change Continuous (fun y : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeCubeRootElement hp x) y.val,
      cubicThetaMobius_height_pos _ y.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cubicThetaMobius_continuousAt _ y.property).comp
    (x:=y) (f:=fun z : CubicThetaPoint => z.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeCubeRootSectionTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeCubeRootElement hp x • y),
    F.val.continuous.comp (cubicThetaPrimeCubeRootPoint_continuous hp x)⟩,by
    intro g y
    change F.val (cubicThetaPrimeCubeRootElement hp x • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeCubeRootElement hp x • y)
    rw [cubicThetaPrimeCubeRootPoint_intertwines,F.property,cubicThetaPrimeCubeRootConjugate_kubota]⟩

@[simp] lemma cubicThetaPrimeCubeRootSectionTranslate_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootSectionTranslate hp 0 F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeCubeRootElement hp 0 • z)=F.val z
  rw [cubicThetaPrimeCubeRootElement_zero,one_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootL2
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaPrimeCubeRootL2 {p : Eisenstein} (hp : primaryPrime p) :=
  Lp ℂ 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional translations give an actual finite additive action on
sections, independent of the chosen representatives modulo the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootResidueOperator {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) : cubicThetaPrimeRootSections p ≃ₗ[ℂ] cubicThetaPrimeRootSections p :=
  cubicThetaPrimeRootOperator hp (residueRepresentative p r)

lemma cubicThetaPrimeRootResidueOperator_mk {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootResidueOperator hp (Ideal.Quotient.mk (modulus p) x)=
      cubicThetaPrimeRootOperator hp x := by
  apply cubicThetaPrimeRootOperator_congr
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (residueRepresentative_spec p (Ideal.Quotient.mk (modulus p) x)))

@[simp] lemma cubicThetaPrimeRootResidueOperator_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootResidueOperator hp 0 F=F := by
  rw [←map_zero (Ideal.Quotient.mk (modulus p)),cubicThetaPrimeRootResidueOperator_mk]
  exact cubicThetaPrimeRootSectionTranslate_zero hp F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootAutomorphism
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootConjugate_complex {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x g).val=
      cubicThetaPrimeRootElement hp x*cubicThetaPrincipalComplex g.val*
        (cubicThetaPrimeRootElement hp x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (cubicThetaPrimeRootElement_intertwines hp x g).symm

@[simp] lemma cubicThetaPrimeRootConjugate_zero {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootConjugate hp 0 g=g := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeRootConjugate_complex,cubicThetaPrimeRootElement_zero,
    one_mul,inv_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable fundamental domain for the fractional-root cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverGroup {p : Eisenstein} (_hp : primaryPrime p) :
    Subgroup cubicThetaPrincipalGroup := cubicThetaPrimeRootSubgroup p

abbrev CubicThetaPrimeRootCover {p : Eisenstein} (hp : primaryPrime p) :=
  Quotient (MulAction.orbitRel (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint)

def cubicThetaPrimeRootCoverMap {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPoint → CubicThetaPrimeRootCover hp :=
  Quotient.mk (MulAction.orbitRel (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint)

def cubicThetaPrimeRootTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeRootCoverGroup hp).exists_isComplement_right 1)

def cubicThetaPrimeRootCoverDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

instance cubicThetaPrimeRootCover_measurableSpace {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSpace (CubicThetaPrimeRootCover hp) := borel _

def cubicThetaPrimeRootCoverMeasure {p : Eisenstein} (hp : primaryPrime p) :
    Measure (CubicThetaPrimeRootCover hp) :=
  (cubicThetaPointMeasure.restrict (cubicThetaPrimeRootCoverDomain hp)).map (cubicThetaPrimeRootCoverMap hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional roots act on the actual finite arithmetic cover. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : CubicThetaPrimeRootCover hp → CubicThetaPrimeRootCover hp :=
  Quotient.map (fun y => cubicThetaPrimeRootElement hp x • y) (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    let k : cubicThetaPrimeRootSubgroup p := ⟨g.val,g.property⟩
    refine ⟨⟨(cubicThetaPrimeRootConjugate hp x k).val,
      (cubicThetaPrimeRootConjugate hp x k).property⟩,?_⟩
    change k.val • b=a at hg
    change (cubicThetaPrimeRootConjugate hp x k).val • (cubicThetaPrimeRootElement hp x • b)=
      cubicThetaPrimeRootElement hp x • a
    rw [←cubicThetaPrimeRootPoint_intertwines,hg])

@[simp] lemma cubicThetaPrimeRootCoverTranslate_apply {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (y : CubicThetaPoint) :
    cubicThetaPrimeRootCoverTranslate hp x (cubicThetaPrimeRootCoverMap hp y)=
      cubicThetaPrimeRootCoverMap hp (cubicThetaPrimeRootElement hp x • y) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSectionNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of a section on the finite root cover is a genuine
continuous quotient function. The fractional-root pullback preserves its exact mass. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSection_property {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (g : cubicThetaPrimeRootCoverGroup hp)
    (x : CubicThetaPoint) : F.val (g • x)=cubicThetaKubotaValue g.val*F.val x := by
  let k : cubicThetaPrimeRootSubgroup p := ⟨g.val,g.property⟩
  exact F.property k x

def cubicThetaPrimeRootSectionNorm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : CubicThetaPrimeRootCover hp → ℝ :=
  Quotient.lift (fun x : CubicThetaPoint => ‖F.val x‖) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg,cubicThetaPrimeRootSection_property hp F,norm_mul,cubicThetaKubotaValue_norm,one_mul])

@[simp] lemma cubicThetaPrimeRootSectionNorm_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (x : CubicThetaPoint) :
    cubicThetaPrimeRootSectionNorm hp F (cubicThetaPrimeRootCoverMap hp x)=‖F.val x‖ := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootDiagonal
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root subgroup has central diagonal reduction modulo the prime.
Its diagonal cubic character is therefore trivial. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRoot_diagonal_square {p : Eisenstein} (_hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : p∣(g.val.val 0 0)^2-1 := by
  have hc : p∣g.val.val 1 0 := (dvd_pow_self p (by decide : 2≠0)).trans g.property.1
  have he : (g.val.val 0 0)^2-1=
      g.val.val 0 0*(g.val.val 0 0-g.val.val 1 1)+g.val.val 0 1*g.val.val 1 0 := by
    linear_combination cubicThetaPrincipalGroup_det g.val
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right g.property.2 _) (dvd_mul_of_dvd_right hc _)

lemma cubicThetaPrimeRoot_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicSymbol p (g.val.val 0 0)=1 := by
  have h2 : (cubicSymbol p (g.val.val 0 0))^2=1 := by
    rw [←cubicSymbol_pow_upper hp.1,
      cubicSymbol_congr (residue_eq_of_dvd_sub (cubicThetaPrimeRoot_diagonal_square hp g))]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  have h3 := cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeRootIwahori g)
  change (cubicSymbol p (g.val.val 0 0))^3=1 at h3
  calc
    _ = (cubicSymbol p (g.val.val 0 0))^2*cubicSymbol p (g.val.val 0 0) := by rw [h2,one_mul]
    _ = (cubicSymbol p (g.val.val 0 0))^3 := by ring
    _ = 1 := h3

def cubicThetaPrimeRootDilationIwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeIwahori p :=
  ⟨cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeRootIwahori g),by
    change p∣g.val.val 1 0/p
    rw [cubicThetaPrimeRoot_lower_single_division hp g]
    exact dvd_mul_right p _⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeyl
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second root direction is supplied by the actual conjugated
inversion. Its integral conjugation preserves the same cubic multiplier. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    ((cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val :
      Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^2);-p^2*g.val.val 0 1,g.val.val 0 0] := by
  rw [cubicThetaPrimeAtkinConjugate_matrix]
  change (!![g.val.val 1 1,-((g.val.val 1 0/p)/p);-p*(p*g.val.val 0 1),g.val.val 0 0] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [cubicThetaPrimeRoot_lower_single_division hp g,mul_div_cancel_left₀ _ hp.2.ne_zero]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pow_two,mul_assoc]

def cubicThetaPrimeRootWeylConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootSubgroup p :=
  ⟨(cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val,by
    change p^2∣(cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val 1 0 ∧
      p∣(cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val 0 0-
        (cubicThetaPrimeAtkinConjugate hp (cubicThetaPrimeRootDilationIwahori hp g)).val.val 1 1
    rw [cubicThetaPrimeRootWeyl_matrix]
    constructor
    · exact ⟨-g.val.val 0 1,by simp⟩
    · simpa using dvd_neg.mpr g.property.2⟩

def cubicThetaPrimeRootWeylElement {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaPrimeAtkinMatrix hp*cubicThetaPrimeDilation hp.2.ne_zero

theorem cubicThetaPrimeRootWeyl_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootWeylElement hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootWeylConjugate hp g).val*
        cubicThetaPrimeRootWeylElement hp := by
  have hD : cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootDilationIwahori hp g).val*
        cubicThetaPrimeDilation hp.2.ne_zero :=
    cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori g)
  have hW : cubicThetaPrimeAtkinMatrix hp*
      cubicThetaPrincipalComplex (cubicThetaPrimeRootDilationIwahori hp g).val=
      cubicThetaPrincipalComplex (cubicThetaPrimeRootWeylConjugate hp g).val*cubicThetaPrimeAtkinMatrix hp :=
    cubicThetaPrimeAtkinMatrix_intertwines hp (cubicThetaPrimeRootDilationIwahori hp g)
  unfold cubicThetaPrimeRootWeylElement
  rw [mul_assoc,hD,←mul_assoc,hW,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Involutivity of the actual conjugated inversion, on both the
arithmetic root subgroup and positive-height points. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeRootWeylElement hp • (g.val • y)=
      (cubicThetaPrimeRootWeylConjugate hp g).val • (cubicThetaPrimeRootWeylElement hp • y) := by
  change cubicThetaPrimeRootWeylElement hp • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeRootWeylConjugate hp g).val •
      (cubicThetaPrimeRootWeylElement hp • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeRootWeyl_intertwines]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylCover
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same conjugated inversion is a homeomorphism of the actual
finite arithmetic cover. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverWeyl {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp → CubicThetaPrimeRootCover hp :=
  Quotient.map (fun y => cubicThetaPrimeRootWeylElement hp • y) (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    let k : cubicThetaPrimeRootSubgroup p := ⟨g.val,g.property⟩
    refine ⟨⟨(cubicThetaPrimeRootWeylConjugate hp k).val,
      (cubicThetaPrimeRootWeylConjugate hp k).property⟩,?_⟩
    change k.val • b=a at hg
    change (cubicThetaPrimeRootWeylConjugate hp k).val • (cubicThetaPrimeRootWeylElement hp • b)=
      cubicThetaPrimeRootWeylElement hp • a
    rw [←cubicThetaPrimeRootWeylPoint_intertwines,hg])

@[simp] lemma cubicThetaPrimeRootCoverWeyl_apply {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeRootCoverWeyl hp (cubicThetaPrimeRootCoverMap hp y)=
      cubicThetaPrimeRootCoverMap hp (cubicThetaPrimeRootWeylElement hp • y) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootPowerCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact diagonal characters of the prime-power dilations. The second
and fourth powers below are the intermediate cubic-root branches. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimePower_primary {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    primary (p^n) := by
  induction n with
  | zero => simpa only [pow_zero] using primary_one
  | succ n ih => simpa only [pow_succ] using primary_mul ih hp.1

lemma cubicThetaPrimePowerConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (g : cubicThetaPrimeIwahori (p^n)) :
    cubicThetaKubotaValue g.val=(cubicSymbol p (g.val.val 0 0))^n*
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimePower_primary hp n) g) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (g.val.val 0 0) (g.val.val 1 0)=
    (cubicSymbol p (g.val.val 0 0))^n*
      cubicSymbol (g.val.val 0 0) (g.val.val 1 0/p^n)
  conv_lhs => rw [←cubicThetaPrimeIwahori_division (pow_ne_zero n hp.2.ne_zero) g]
  rw [cubicSymbol_mul_upper ha,cubic_reciprocity ha (cubicThetaPrimePower_primary hp n),
    cubicThetaSymbol_prime_pow hp]

lemma cubicThetaPrimePowerConjugate_kubota_star {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (g : cubicThetaPrimeIwahori (p^n)) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimePower_primary hp n) g)=
      star ((cubicSymbol p (g.val.val 0 0))^n)*cubicThetaKubotaValue g.val := by
  have hc : IsCoprime (p^n) (g.val.val 0 0) :=
    ((cubicThetaPrincipalGroup_column_coprime g.val).of_isCoprime_of_dvd_right g.property).symm
  have hnorm : ‖(cubicSymbol p (g.val.val 0 0))^n‖=1 := by
    rw [←cubicThetaSymbol_prime_pow hp]
    exact norm_cubicSymbol_of_isCoprime (cubicThetaPrimePower_primary hp n) hc
  have hunit : star ((cubicSymbol p (g.val.val 0 0))^n)*(cubicSymbol p (g.val.val 0 0))^n=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',hnorm]
    norm_num
  rw [cubicThetaPrimePowerConjugate_kubota hp n g,←mul_assoc,hunit,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootL2
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual L2 representatives of sections on the finite root cover.
The Weyl action preserves square integrability and the exact L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaPrimeRootL2 {p : Eisenstein} (hp : primaryPrime p) :=
  Lp ℂ 2 (cubicThetaPrimeRootCoverMeasure hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootMatrix
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact arithmetic subgroup for translations by 3x/p^2.
It is needed to compare the intermediate correlation with finite Fourier classes. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeDouble_primary {p : Eisenstein} (hp : primaryPrime p) : primary (p^2) :=
  cubicThetaPrimePower_primary hp 2

abbrev cubicThetaPrimeDoubleRootSubgroup (p : Eisenstein) := cubicThetaPrimeRootSubgroup (p^2)

lemma cubicThetaPrimeDoubleRoot_lower_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (p^2)^2*(g.val.val 1 0/(p^2)^2)=g.val.val 1 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 (pow_ne_zero 2 hp.2.ne_zero)) g.property.1

lemma cubicThetaPrimeDoubleRoot_diagonal_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    p^2*((g.val.val 1 1-g.val.val 0 0)/p^2)=g.val.val 1 1-g.val.val 0 0 :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero)
    (by simpa only [neg_sub] using dvd_neg.mpr g.property.2)

def cubicThetaPrimeDoubleRootMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) : SL(2,Eisenstein) := by
  let C := g.val.val 1 0/(p^2)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^2
  refine ⟨!![g.val.val 0 0+3*x*p^2*C,g.val.val 0 1+3*x*D-9*x^2*C;
    g.val.val 1 0,g.val.val 1 1-3*x*p^2*C],?_⟩
  rw [Matrix.det_fin_two_of]
  have hC : (p^2)^2*C=g.val.val 1 0 := cubicThetaPrimeDoubleRoot_lower_division hp g
  have hD : g.val.val 1 1=g.val.val 0 0+p^2*D := by
    have he := cubicThetaPrimeDoubleRoot_diagonal_division hp g
    dsimp only [D]
    linear_combination -he
  calc
    _ = g.val.val 0 0*g.val.val 1 1-g.val.val 0 1*g.val.val 1 0 := by
      rw [hD,←hC]
      ring
    _ = 1 := cubicThetaPrincipalGroup_det g.val

lemma cubicThetaPrimeDoubleRootMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootMatrix hp x g∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary g.val).1
  have hd := (cubicThetaPrincipalGroup_diagonal_primary g.val).2
  have hb := (cubicThetaPrincipalGroup_offDiagonal g.val).1
  have hc := (cubicThetaPrincipalGroup_offDiagonal g.val).2
  let C := g.val.val 1 0/(p^2)^2
  let D := (g.val.val 1 1-g.val.val 0 0)/p^2
  have ht : (3:Eisenstein)∣3*x*p^2*C := ⟨x*p^2*C,by ring⟩
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (g.val.val 0 0+3*x*p^2*C) ∧
    (3:Eisenstein)∣g.val.val 0 1+3*x*D-9*x^2*C ∧
    (3:Eisenstein)∣g.val.val 1 0 ∧ primary (g.val.val 1 1-3*x*p^2*C)
  refine ⟨?_,?_,hc,?_⟩
  · change (3:Eisenstein)∣(g.val.val 0 0+3*x*p^2*C)-1
    convert dvd_add ha ht using 1 <;> first | rfl | ring
  · exact dvd_sub (dvd_add hb ⟨x*D,by ring⟩) ⟨3*x^2*C,by ring⟩
  · change (3:Eisenstein)∣(g.val.val 1 1-3*x*p^2*C)-1
    convert dvd_sub hd ht using 1 <;> first | rfl | ring

def cubicThetaPrimeDoubleRootConjugate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeDoubleRootSubgroup p :=
  ⟨⟨cubicThetaPrimeDoubleRootMatrix hp x g,cubicThetaPrimeDoubleRootMatrix_mem hp x g⟩,by
    refine ⟨g.property.1,?_⟩
    change p^2∣(g.val.val 0 0+3*x*p^2*(g.val.val 1 0/(p^2)^2))-
      (g.val.val 1 1-3*x*p^2*(g.val.val 1 0/(p^2)^2))
    convert dvd_add g.property.2 (show p^2∣6*x*p^2*(g.val.val 1 0/(p^2)^2) from
      ⟨6*x*(g.val.val 1 0/(p^2)^2),by ring⟩) using 1; ring⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral conjugation at the square root scale. The cubic twist of
the dilation is trivial, so the original multiplier is retained exactly. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeDoubleRootIwahori {p : Eisenstein} (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeIwahori (p^2) :=
  ⟨g.val,(dvd_pow_self (p^2) (by decide : 2≠0)).trans g.property.1⟩

lemma cubicThetaPrimeDoubleRoot_lower_single_division {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    g.val.val 1 0/p^2=p^2*(g.val.val 1 0/(p^2)^2) := by
  apply mul_left_cancel₀ (pow_ne_zero 2 hp.2.ne_zero)
  have hh : p^2*(g.val.val 1 0/p^2)=g.val.val 1 0 :=
    EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero)
      ((dvd_pow_self (p^2) (by decide : 2≠0)).trans g.property.1)
  rw [hh]
  have he := cubicThetaPrimeDoubleRoot_lower_division hp g
  linear_combination -he

theorem cubicThetaPrimeDoubleRootConjugate_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g))=
      cubicThetaPrincipalTranslation x*cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
        (cubicThetaPrimeDoubleRootIwahori g)*(cubicThetaPrincipalTranslation x)⁻¹ := by
  let a := g.val.val 0 0
  let b := g.val.val 0 1
  let c := g.val.val 1 0
  let d := g.val.val 1 1
  let C := c/(p^2)^2
  let B := (d-a)/p^2
  have hc : c/p^2=p^2*C := cubicThetaPrimeDoubleRoot_lower_single_division hp g
  have hd : p^2*B=d-a := cubicThetaPrimeDoubleRoot_diagonal_division hp g
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  dsimp only [cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
    cubicThetaPrimeDoubleRootIwahori,cubicThetaPrimeDoubleRootConjugate,cubicThetaPrimeDoubleRootMatrix,
    cubicThetaPrincipalTranslation]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,neg_zero]
  change (!![a+3*x*p^2*C,p^2*(b+3*x*B-9*x^2*C);c/p^2,d-3*x*p^2*C] :
    Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1,3*x;0,1]*!![a,p^2*b;c/p^2,d]*!![1,-(3*x);0,1]
  rw [hc]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring_nf
  linear_combination (3*x:Eisenstein)*hd

lemma cubicThetaPrimeDoubleRoot_diagonal_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicSymbol p (g.val.val 0 0)=1 := by
  have hc : p^2∣g.val.val 1 0 := (dvd_pow_self (p^2) (by decide : 2≠0)).trans g.property.1
  have hd : p∣g.val.val 0 0-g.val.val 1 1 := (dvd_pow_self p (by decide : 2≠0)).trans g.property.2
  exact cubicThetaPrimeRoot_diagonal_character hp (⟨g.val,hc,hd⟩ : cubicThetaPrimeRootSubgroup p)

lemma cubicThetaPrimeDoubleRootDilation_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori g))=cubicThetaKubotaValue g.val := by
  have he := cubicThetaPrimePowerConjugate_kubota_star hp 2 (cubicThetaPrimeDoubleRootIwahori g)
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootIwahori g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*cubicThetaKubotaValue g.val at he
  rw [cubicThetaPrimeDoubleRoot_diagonal_character hp g,one_pow,star_one,one_mul] at he
  exact he

theorem cubicThetaPrimeDoubleRootConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeDoubleRootConjugate hp x g).val=
      cubicThetaKubotaValue g.val := by
  have hM : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g)))=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
        (cubicThetaPrimeDoubleRootIwahori g)) := by
    rw [cubicThetaPrimeDoubleRootConjugate_dilation,cubicThetaKubotaValue_mul,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,
      cubicThetaPrincipalTranslation_inverse_value,one_mul,mul_one]
  exact (cubicThetaPrimeDoubleRootDilation_kubota hp
    (cubicThetaPrimeDoubleRootConjugate hp x g)).symm.trans
      (hM.trans (cubicThetaPrimeDoubleRootDilation_kubota hp g))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootAction
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal square-scale fractional root preserves the arithmetic
subgroup and its actual cubic multiplier. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeDoubleRootElement {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : SL(2,ℂ) :=
  (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero))⁻¹*
    cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*
      cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)

theorem cubicThetaPrimeDoubleRootElement_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootElement hp x*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val*
        cubicThetaPrimeDoubleRootElement hp x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let q := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootIwahori g))
  let q' := cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g)))
  have hg : D*cubicThetaPrincipalComplex g.val=q*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeDoubleRootIwahori g)
  have hg' : D*cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val=q'*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootIwahori (cubicThetaPrimeDoubleRootConjugate hp x g))
  have hq : q'=t*q*t⁻¹ := by
    change cubicThetaPrincipalComplex _=_
    rw [cubicThetaPrimeDoubleRootConjugate_dilation,map_mul,map_mul,map_inv]
  have ht : t*q=q'*t := by rw [hq]; group
  have hg'' : D⁻¹*q'*D=cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val := by
    rw [mul_assoc,←hg']
    group
  change D⁻¹*t*D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val*(D⁻¹*t*D)
  calc
    _ = D⁻¹*t*(D*cubicThetaPrincipalComplex g.val) := by group
    _ = D⁻¹*t*(q*D) := by rw [hg]
    _ = D⁻¹*(t*q)*D := by group
    _ = D⁻¹*(q'*t)*D := by rw [ht]
    _ = (D⁻¹*q'*D)*(D⁻¹*t*D) := by group
    _ = _ := by rw [hg'']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-scale fractional root has its literal translation parameter. Its additive
law and integral periods will be used to average over the cube modulus. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootElement_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeDoubleRootElement hp x=
      cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ)) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  let t := cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)
  let u := cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ))
  have hD : D*u=t*D := by
    rw [show t=cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ) from
      cubicThetaPrincipalTranslation_complex x]
    apply Subtype.ext
    change (D:Matrix (Fin 2) (Fin 2) ℂ)*(u:Matrix (Fin 2) (Fin 2) ℂ)=
      (cubicThetaTranslationMatrix ((3*x:Eisenstein):ℂ):Matrix (Fin 2) (Fin 2) ℂ)*
        (D:Matrix (Fin 2) (Fin 2) ℂ)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [D,u,cubicThetaPrimeDilation,cubicThetaTranslationMatrix,
        Matrix.mul_apply,Fin.sum_univ_two]
    have hs : (p:ℂ)^2=(cubicThetaPrimeSquareRoot (p^2))^2 := by
      have hc : ((p^2:Eisenstein):ℂ)=(p:ℂ)^2 := map_pow eisensteinRing.val p 2
      exact hc.symm.trans (cubicThetaPrimeSquareRoot_sq (p^2)).symm
    rw [hs]
    field_simp [cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 2 hp.2.ne_zero)]
  change D⁻¹*t*D=u
  calc
    _ = D⁻¹*(t*D) := by group
    _ = D⁻¹*(D*u) := by rw [hD]
    _ = u := by group

@[simp] lemma cubicThetaPrimeDoubleRootElement_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDoubleRootElement hp 0=1 := by
  rw [cubicThetaPrimeDoubleRootElement_translation]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaTranslationMatrix]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootSections
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual sections and their fractional translations at the cube modulus. -/
noncomputable section
namespace CubicFirstMoment

abbrev cubicThetaPrimeDoubleRootSections (p : Eisenstein) := cubicThetaPrimeRootSections (p^2)

lemma cubicThetaPrimeDoubleRootPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeDoubleRootElement hp x • (g.val • y)=
      (cubicThetaPrimeDoubleRootConjugate hp x g).val • (cubicThetaPrimeDoubleRootElement hp x • y) := by
  change cubicThetaPrimeDoubleRootElement hp x • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val •
      (cubicThetaPrimeDoubleRootElement hp x • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeDoubleRootElement_intertwines]

lemma cubicThetaPrimeDoubleRootPoint_continuous {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : Continuous (fun y : CubicThetaPoint => cubicThetaPrimeDoubleRootElement hp x • y) := by
  change Continuous (fun y : CubicThetaPoint =>
    (⟨cubicThetaMobius (cubicThetaPrimeDoubleRootElement hp x) y.val,
      cubicThetaMobius_height_pos _ y.property⟩ : CubicThetaPoint))
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (cubicThetaMobius_continuousAt _ y.property).comp
    (x:=y) (f:=fun z : CubicThetaPoint => z.val) continuous_subtype_val.continuousAt

def cubicThetaPrimeDoubleRootSectionTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeDoubleRootSections p) : cubicThetaPrimeDoubleRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeDoubleRootElement hp x • y),
    F.val.continuous.comp (cubicThetaPrimeDoubleRootPoint_continuous hp x)⟩,by
    intro g y
    change F.val (cubicThetaPrimeDoubleRootElement hp x • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeDoubleRootElement hp x • y)
    rw [cubicThetaPrimeDoubleRootPoint_intertwines,F.property,cubicThetaPrimeDoubleRootConjugate_kubota]⟩

@[simp] lemma cubicThetaPrimeDoubleRootSectionTranslate_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeDoubleRootSections p) : cubicThetaPrimeDoubleRootSectionTranslate hp 0 F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeDoubleRootElement hp 0 • z)=F.val z
  rw [cubicThetaPrimeDoubleRootElement_zero,one_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootAutomorphism
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootConjugate_complex {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x g).val=
      cubicThetaPrimeDoubleRootElement hp x*cubicThetaPrincipalComplex g.val*
        (cubicThetaPrimeDoubleRootElement hp x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (cubicThetaPrimeDoubleRootElement_intertwines hp x g).symm

@[simp] lemma cubicThetaPrimeDoubleRootConjugate_zero {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeDoubleRootConjugate hp 0 g=g := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeDoubleRootConjugate_complex,cubicThetaPrimeDoubleRootElement_zero,
    one_mul,inv_one,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryPowerCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support coordinates at each unit and ramified power of a primary
frequency. Changing that unit or exponent preserves the squarefree/cube support. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.primary_power {h : Eisenstein} (hh : primary h)
    (e : Eisensteinˣ) (k : ℕ)
    (R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*h)) :
    R.unit=e ∧ R.order=k ∧ R.squarefreePart*R.cubePart^3=h := by
  have hp : primary (R.squarefreePart*R.cubePart^3) :=
    primary_mul R.squarefree_primary (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary))
  exact unit_ramified_primary_unique hp hh R.numerator_eq.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryResidueNine
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaPrimaryNine :=
  {x : Residues (9:Eisenstein) // primary (residueRepresentative 9 x)}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedDenominator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaPrimaryPart := {a : Eisenstein // primary a}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryCubes
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary cubes at the inverted cusp are in exact bijection with
ideals prime to lambda. No choice of a cube root contributes multiplicity. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaUnramifiedIdeal :=
  {ν : EisensteinIdealExponent // ν cubicThetaRamifiedPrime=0}

abbrev CubicThetaPrimaryCube :=
  {c : Eisenstein // primary c ∧ ∃ j : Eisenstein, j^3=c}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCoefficientScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified cube scaling agrees with the normalization of the
published arithmetic coefficient on every positive ramified order. -/
noncomputable section
namespace CubicFirstMoment

def CubicThetaCoordinates.mulLambdaCube {n : Eisenstein} (R : CubicThetaCoordinates n) :
    CubicThetaCoordinates (lambdaE^3*n) where
  unit := R.unit
  order := R.order+3
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := R.cube_primary
  squarefree := R.squarefree
  numerator_eq := by
    calc
      _ = lambdaE^3*((R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3)) :=
        congrArg (fun a => lambdaE^3*a) R.numerator_eq
      _ = _ := by rw [pow_add]; ring

lemma CubicThetaCoordinates.amplitude_mulLambdaCube {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.mulLambdaCube.amplitude=(1/3:ℝ)*R.amplitude := by
  have hd : (R.order+3)/3=R.order/3+1 := by omega
  simp only [CubicThetaCoordinates.amplitude,CubicThetaCoordinates.mulLambdaCube,hd,Nat.cast_add,Nat.cast_one]
  have he : (4:ℝ)-(((R.order/3:ℕ):ℝ)+1)=(4-((R.order/3:ℕ):ℝ))-1 := by ring
  rw [he,Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_one]
  ring

theorem CubicThetaCoordinates.coefficient_mulLambdaCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hR : 0<R.order) :
    R.mulLambdaCube.coefficient=(1/3:ℂ)*R.coefficient := by
  have hmod : (R.order+3)%3=R.order%3 := by omega
  have hA : ((R.order+3)%3=0 ∧ 3≤R.order+3) ↔ (R.order%3=0 ∧ 3≤R.order) := by omega
  have hB : ((R.order+3)%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)) ↔
      (R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)) := by rw [hmod]
  change (if (R.order+3)%3=0 ∧ 3≤R.order+3 then
      (R.mulLambdaCube.amplitude:ℂ)*cubicThetaUnitPhase R.unit*
        star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2))
    else if (R.order+3)%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1) then
      (R.mulLambdaCube.amplitude:ℂ)*star (gauss R.squarefreePart) else 0)=_
  simp only [hA,hB,R.amplitude_mulLambdaCube]
  unfold CubicThetaCoordinates.coefficient
  split_ifs <;> push_cast <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCoefficientSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of a ramified cube preserves arithmetic support. This
extends the coordinate scaling to the literal zero-extended coefficient. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.ramified_emultiplicity {n : Eisenstein} (R : CubicThetaCoordinates n) :
    emultiplicity lambdaE n=R.order := by
  have hp : primary (R.cubePart^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
  have he := congrArg (emultiplicity lambdaE) R.numerator_eq
  simpa only [emultiplicity_mul lambdaE_prime,emultiplicity_pow_self_of_prime lambdaE_prime,
    unit_lambda_emultiplicity,primary_lambda_emultiplicity R.squarefree_primary,
    primary_lambda_emultiplicity hp,zero_add,add_zero] using he

lemma CubicThetaCoordinates.order_pos {n : Eisenstein} (R : CubicThetaCoordinates n)
    (hn : lambdaE∣n) : 0<R.order := by
  have hp := dvd_iff_emultiplicity_pos.mpr hn
  rw [R.ramified_emultiplicity] at hp
  exact_mod_cast hp

lemma CubicThetaCoordinates.cube_order {n : Eisenstein} (R : CubicThetaCoordinates (lambdaE^3*n)) :
    3≤R.order := by
  have hm : (3:ℕ∞)≤emultiplicity lambdaE (lambdaE^3*n) :=
    pow_dvd_iff_le_emultiplicity.mp ⟨n,rfl⟩
  rw [R.ramified_emultiplicity] at hm
  exact_mod_cast hm

def CubicThetaCoordinates.removeLambdaCube {n : Eisenstein}
    (R : CubicThetaCoordinates (lambdaE^3*n)) : CubicThetaCoordinates n where
  unit := R.unit
  order := R.order-3
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := R.cube_primary
  squarefree := R.squarefree
  numerator_eq := by
    apply mul_left_cancel₀ (pow_ne_zero 3 lambdaE_prime.ne_zero)
    have hp : lambdaE^R.order=lambdaE^3*lambdaE^(R.order-3) := by
      rw [←pow_add,Nat.add_sub_of_le R.cube_order]
    calc
      _ = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hp]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def metaplecticFrequency (n : MetaplecticDualArgument) : ℂ :=
  (n.val : ℂ)/traceLambda

/-- Equation (5.68), written as its exact squarefree Euler product. -/
def metaplecticLocalCoefficient (r : Eisenstein) (n : MetaplecticDualArgument) : ℂ :=
  ∏ p ∈ primaryPrimeFactors r,
    ((if p ∣ n.val then norm p-1 else -1 : ℝ):ℂ)

/-- Support read from (5.79), avoiding the repeated ramified exponent in
the printed (5.67). The coefficient bound follows from (5.7), (5.13), (5.14).
The two supported factors may have arbitrarily large exponents. -/
def MetaplecticCoefficientBounds
    (a : Eisenstein → MetaplecticDualArgument → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r → Squarefree r →
    ∀ n : MetaplecticDualArgument, a r n*metaplecticLocalCoefficient r n ≠ 0 →
      ∃ (j : ℤ) (ζ : Eisensteinˣ) (h h' w : Eisenstein),
        -1 ≤ j ∧ primary h ∧ primary h' ∧ primary w ∧
        (∃ k : ℕ, h ∣ r^k) ∧ (∃ k : ℕ, h' ∣ r^k) ∧
        IsCoprime w r ∧ Squarefree (h*w) ∧
        metaplecticFrequency n = traceLambda^j*(ζ.val:ℂ)*(h:ℂ)*(w:ℂ)*(h':ℂ)^3 ∧
        ‖a r n‖ ≤ C*3^((max j 0:ℤ)/3:ℝ)*Real.sqrt (norm h')

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCoefficientSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev MetaplecticCoefficientCode (r : Eisenstein) :=
  ℕ × (Eisensteinˣ × ((metaplecticPrimaryDivisors r) × (PrimaryArgument × PrimaryArgument)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRationalCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal determinant-one lift of each coprime additive numerator.
The lift keeps its prescribed bottom-left entry, including ramified factors. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimitiveMatrix (r a : Eisenstein) (h : IsCoprime r a) : SL(2,Eisenstein) := by
  let u := Classical.choose h
  let v := Classical.choose (Classical.choose_spec h)
  have he : u*r+v*a=1 := Classical.choose_spec (Classical.choose_spec h)
  refine ⟨!![a,-u;r,v],?_⟩
  simp only [Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linear_combination he

@[simp] lemma cubicThetaPrimitiveMatrix_top (r a : Eisenstein) (h : IsCoprime r a) :
    cubicThetaPrimitiveMatrix r a h 0 0=a := rfl

@[simp] lemma cubicThetaPrimitiveMatrix_bottom (r a : Eisenstein) (h : IsCoprime r a) :
    cubicThetaPrimitiveMatrix r a h 1 0=r := rfl

/-- Lambda cubed cancels the selected frequency denominator. -/
def cubicThetaGaussCuspMatrix (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) : SL(2,Eisenstein) :=
  cubicThetaPrimitiveMatrix r (lambdaE^3*u) (((primary_coprime_lambda hr).pow_right).mul_right hu)

@[simp] lemma cubicThetaGaussCuspMatrix_bottom (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaGaussCuspMatrix r hr u hu 1 0=r := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaCommonIndex := Eisensteinˣ × ℕ × CubicThetaPrimaryPair

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex conjugation of the finite arithmetic data used to normalize
Patterson's theta series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_conjugate_lambda : conjugate lambdaE = -lambdaE := by
  apply Subtype.ext
  change star (traceLambda) = -traceLambda
  simp only [traceLambda, star_add, star_mul, star_ofNat, star_one, star_omega]
  linear_combination 2*omega_quadratic

lemma cubicTheta_squarefree_conjugate {b : Eisenstein} (hb : Squarefree b) :
    Squarefree (conjugate b) := by
  intro c hc
  have hd := conjugate.map_dvd hc
  change conjugate (c*c) ∣ conjugate (conjugate b) at hd
  rw [map_mul, conjugate_conjugate] at hd
  have hu := hb _ hd
  have hu' : IsUnit (conjugate (conjugate c)) := hu.map conjugate.toMonoidHom
  simpa only [conjugate_conjugate] using hu'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConjugateCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation preserves the exact arithmetic coefficient coordinates,
including their ramified exponent and unit phase. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma cubicTheta_conjugateUnit_val (u : Eisensteinˣ) :
    ((Units.map conjugate.toMonoidHom u):Eisenstein) = conjugate (u:Eisenstein) := rfl

def CubicThetaCoordinates.conjugated {n : Eisenstein} (R : CubicThetaCoordinates n) :
    CubicThetaCoordinates (conjugate n) where
  unit := Units.map conjugate.toMonoidHom R.unit * (-1)^R.order
  order := R.order
  squarefreePart := conjugate R.squarefreePart
  cubePart := conjugate R.cubePart
  squarefree_primary := primary_conjugate R.squarefree_primary
  cube_primary := primary_conjugate R.cube_primary
  squarefree := cubicTheta_squarefree_conjugate R.squarefree
  numerator_eq := by
    conv_lhs => rw [R.numerator_eq]
    rw [map_mul,map_mul,map_mul,map_pow,map_pow,cubicTheta_conjugate_lambda]
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,cubicTheta_conjugateUnit_val,Units.val_neg,Units.val_one]
    rw [neg_eq_neg_one_mul,mul_pow]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

def CubicThetaCoreSupport (r : Eisenstein) (n : MetaplecticDualArgument) : Prop :=
  ∃ R : CubicThetaCoordinates n.val, ∃ k : ℕ, R.cubePart∣r^k

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFreeCubeIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaCoreIndex (r : Eisenstein) :=
  {x : CubicThetaCommonIndex // ∃ k : ℕ, x.2.2.val.2∣r^k}
abbrev CubicThetaFreeArgument (r : Eisenstein) :=
  {d : PrimaryArgument // IsCoprime (d:Eisenstein) r}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev CubicThetaSquarefreePrimary := {c : Eisenstein // primary c ∧ Squarefree c}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullLevelRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All level-three rows before the coprimality restriction. They form
one explicit affine lattice; primary common factors preserve the lattice. -/
noncomputable section
namespace CubicFirstMoment

@[ext] structure CubicThetaFullRow where
  c : Eisenstein
  d : Eisenstein
  c_three : (3:Eisenstein) ∣ c
  d_primary : primary d

def CubicThetaFullRow.height (r : CubicThetaFullRow) (p : ℂ × ℝ) : ℝ :=
  p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual affine four-dimensional Gaussian, before removal of common
primary factors. Its Mellin integral is the full height series. -/
noncomputable section
namespace CubicFirstMoment

def CubicThetaFullRow.quadratic (r : CubicThetaFullRow) (p : ℂ × ℝ) : ℝ :=
  (Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)/p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNonzeroRowHeat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal two-coordinate Gaussian behind the nonzero-first-row bound. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaNonzeroRow := {c : Eisenstein // c≠0} × Eisenstein

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveAction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right action of the full integral modular group on primitive rows.
This transports the positive scalar cutoff into a fixed Siegel set. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def CubicThetaPrimitiveRow.completion (r : CubicThetaPrimitiveRow) : SL(2,Eisenstein) :=
  Classical.choose (cubicThetaPrimitiveRow_surjective r)

lemma CubicThetaPrimitiveRow.completion_row (r : CubicThetaPrimitiveRow) :
    cubicThetaPrimitiveRow r.completion=r := Classical.choose_spec (cubicThetaPrimitiveRow_surjective r)

lemma CubicThetaPrimitiveRow.completion_c (r : CubicThetaPrimitiveRow) :
    r.completion 1 0=r.c := congrArg CubicThetaPrimitiveRow.c r.completion_row

lemma CubicThetaPrimitiveRow.completion_d (r : CubicThetaPrimitiveRow) :
    r.completion 1 1=r.d := congrArg CubicThetaPrimitiveRow.d r.completion_row

def CubicThetaPrimitiveRow.rightMul (r : CubicThetaPrimitiveRow) (g : SL(2,Eisenstein)) :
    CubicThetaPrimitiveRow := cubicThetaPrimitiveRow (r.completion*g)

lemma CubicThetaPrimitiveRow.rightMul_c (r : CubicThetaPrimitiveRow) (g : SL(2,Eisenstein)) :
    (r.rightMul g).c=r.c*g 0 0+r.d*g 1 0 := by
  change (r.completion*g) 1 0=_
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    r.completion_c,r.completion_d]

lemma CubicThetaPrimitiveRow.rightMul_d (r : CubicThetaPrimitiveRow) (g : SL(2,Eisenstein)) :
    (r.rightMul g).d=r.c*g 0 1+r.d*g 1 1 := by
  change (r.completion*g) 1 1=_
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    r.completion_c,r.completion_d]

lemma cubicThetaPrimitiveRow_mul (g h : SL(2,Eisenstein)) :
    cubicThetaPrimitiveRow (g*h)=(cubicThetaPrimitiveRow g).rightMul h := by
  apply CubicThetaPrimitiveRow.ext
  · rw [CubicThetaPrimitiveRow.rightMul_c]
    change (g*h) 1 0=g 1 0*h 0 0+g 1 1*h 1 0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  · rw [CubicThetaPrimitiveRow.rightMul_d]
    change (g*h) 1 1=g 1 0*h 0 1+g 1 1*h 1 1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

lemma CubicThetaPrimitiveRow.rightMul_one (r : CubicThetaPrimitiveRow) : r.rightMul 1=r := by
  simp only [CubicThetaPrimitiveRow.rightMul,mul_one,r.completion_row]

lemma CubicThetaPrimitiveRow.rightMul_assoc (r : CubicThetaPrimitiveRow)
    (g h : SL(2,Eisenstein)) : (r.rightMul g).rightMul h=r.rightMul (g*h) := by
  change (cubicThetaPrimitiveRow (r.completion*g)).rightMul h=_
  rw [←cubicThetaPrimitiveRow_mul,mul_assoc,cubicThetaPrimitiveRow_mul,r.completion_row]

def CubicThetaPrimitiveRow.rightMulEquiv (g : SL(2,Eisenstein)) :
    CubicThetaPrimitiveRow ≃ CubicThetaPrimitiveRow where
  toFun r := r.rightMul g
  invFun r := r.rightMul g⁻¹
  left_inv r := by
    change (r.rightMul g).rightMul g⁻¹=r
    rw [r.rightMul_assoc,mul_inv_cancel,r.rightMul_one]
  right_inv r := by
    change (r.rightMul g⁻¹).rightMul g=r
    rw [r.rightMul_assoc,inv_mul_cancel,r.rightMul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveZeroRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-first-coordinate rows are exactly the finitely many units.
Their cutoff heat contribution has uniform exponential decay. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaZeroFirstRow := {r : CubicThetaPrimitiveRow // r.c=0}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitiveHeatCusp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform control of the actual truncated primitive heat kernel in a cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

abbrev CubicThetaNonzeroFirstPrimitiveRow := {r : CubicThetaPrimitiveRow // r.c≠0}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev MetaplecticSupportPrefix (r : Eisenstein) :=
  ℕ × (Eisensteinˣ × ((metaplecticPrimaryDivisors r) × PrimaryArgument))

abbrev MetaplecticRetainedCode (r : Eisenstein) :=
  PrimaryArgument × (MetaplecticSupportPrefix r × PrimaryArgument)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCodeDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
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

abbrev MetaplecticDyadPrefix (r : Eisenstein) := PrimaryArgument × MetaplecticSupportPrefix r

end CubicFirstMoment

end

end OAI
end


