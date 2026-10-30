-- Prove2me | Definitions.Def_OAIQ096A013
-- name    : OAIQ096A013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:43:13.400876+00:00
-- url     : https://prove2.me/theorems/4a1e76c8-b195-47e3-a581-2288becde3e8
-- title:
--   Definitions bundle OAIQ096A013 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 286 declarations of OpenAI's Lean: 75 definitions, 16 instances and 195 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaArithmeticTorus`, `OAI.CubicFirstMoment.cubicThetaConstantDirichlet`, `OAI.CubicFirstMoment.cubicThetaConstantTermWeight`, `OAI.CubicFirstMoment.cubicThetaCubeCoordinatesMap`, `OAI.CubicFirstMoment.cubicThetaEisensteinConstantMode`, `OAI.CubicFirstMoment.cubicThetaEisensteinGaussCoefficient`, `OAI.CubicFirstMoment.cubicThetaEisensteinGaussianRow`, `OAI.CubicFirstMoment.cubicThetaEisensteinResidueWeight`, `OAI.CubicFirstMoment.cubicThetaEisensteinRow`, `OAI.CubicFirstMoment.cubicThetaFourierIndex`, `OAI.CubicFirstMoment.cubicThetaFrequencyDirichlet`, `OAI.CubicFirstMoment.cubicThetaFrequencyTerm`, `OAI.CubicFirstMoment.cubicThetaIntegralQuotientMap`, `OAI.CubicFirstMoment.cubicThetaLongWindowDefectSection`, `OAI.CubicFirstMoment.cubicThetaNonzeroFrequencyTerm`, `OAI.CubicFirstMoment.cubicThetaPeriodEquiv`, `OAI.CubicFirstMoment.cubicThetaPrimaryResidueEquivKernel`, `OAI.CubicFirstMoment.cubicThetaPrimeAtkinKernel`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeBranchSum`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeFullBottomSum`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeLowerValue`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFunction`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleAtkinConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleAtkinMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootAutomorphism`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootBruhat`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootBruhatMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootDilationIwahori`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootWeylConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootWeylElement`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleSquareConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeFreeTerm`, `OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2`, `OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphism`, `OAI.CubicFirstMoment.cubicThetaPrimeRootBorelSection`, `OAI.CubicFirstMoment.cubicThetaPrimeRootBruhat`, `OAI.CubicFirstMoment.cubicThetaPrimeRootBruhatMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeRootCoverCenter`, `OAI.CubicFirstMoment.cubicThetaPrimeRootCoverChart`, `OAI.CubicFirstMoment.cubicThetaPrimeRootCoverHomeomorph` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_PeriodicPoisson`, `CubicMoment_Estimates_IdealDirichletInverse`, `CubicMoment_Estimates_IdealMoebiusBounds`, `CubicMoment_Estimates_IdealThetaMellin`, `CubicMoment_Estimates_PrimePowerDivisors`, `CubicMoment_Estimates_PrimeToThreeIdeals`, `CubicMoment_Estimates_PrincipalZetaPole`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Theta_CubicThetaArithmeticTorus`, `CubicMoment_Theta_CubicThetaConstantCharacter`, `CubicMoment_Theta_CubicThetaConstantCount`, `CubicMoment_Theta_CubicThetaConstantDirichlet`, `CubicMoment_Theta_CubicThetaConstantSupport`, `CubicMoment_Theta_CubicThetaCubeConstant`, `CubicMoment_Theta_CubicThetaCubeCoordinates`, `CubicMoment_Theta_CubicThetaCuspFourierSurjective`, `CubicMoment_Theta_CubicThetaCuspRemainder`, `CubicMoment_Theta_CubicThetaDensityLocal`, `CubicMoment_Theta_CubicThetaDualHeatSummability`, `CubicMoment_Theta_CubicThetaEisensteinCusp`, `CubicMoment_Theta_CubicThetaEisensteinFourierRows`, `CubicMoment_Theta_CubicThetaEisensteinResidues`, `CubicMoment_Theta_CubicThetaEisensteinTorus`, `CubicMoment_Theta_CubicThetaFiniteCover`, `CubicMoment_Theta_CubicThetaFourierNonzero`, `CubicMoment_Theta_CubicThetaFrequencyDirichlet`, `CubicMoment_Theta_CubicThetaFrequencyHolomorphic`, `CubicMoment_Theta_CubicThetaHeatMoments`, `CubicMoment_Theta_CubicThetaHorizontalCoefficient`, `CubicMoment_Theta_CubicThetaHorizontalDomain`, `CubicMoment_Theta_CubicThetaHorizontalLattice`, `CubicMoment_Theta_CubicThetaHorizontalSection`, `CubicMoment_Theta_CubicThetaIncomingRows`, `CubicMoment_Theta_CubicThetaIntegralQuotient`, `CubicMoment_Theta_CubicThetaInversionMass`, `CubicMoment_Theta_CubicThetaLongWindowKernel`, `CubicMoment_Theta_CubicThetaPeriodMeasure`, `CubicMoment_Theta_CubicThetaPrimeAtkinConjugation`, `CubicMoment_Theta_CubicThetaPrimeCharacterNontrivial`, `CubicMoment_Theta_CubicThetaPrimeCubeBottomMean`, `CubicMoment_Theta_CubicThetaPrimeCubeBranchCoordinates`, `CubicMoment_Theta_CubicThetaPrimeCubeBranchPeriodicity`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstBranchMean`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeFormula`, `CubicMoment_Theta_CubicThetaPrimeCubeLowerValue`, `CubicMoment_Theta_CubicThetaPrimeCubeReciprocalNormalizer`, `CubicMoment_Theta_CubicThetaPrimeCubeReductionPhase`, `CubicMoment_Theta_CubicThetaPrimeCubeReductionRow`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatPhase`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCuspObservation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDeepCharacter`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFirstIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootPowerOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeCubeRootRamanujan`, `CubicMoment_Theta_CubicThetaPrimeCubeRootSecondIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeight`, `CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchCoordinates`, `CubicMoment_Theta_CubicThetaPrimeCubeUnitBranch`, `CubicMoment_Theta_CubicThetaPrimeDoubleAtkin`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootAutomorphism`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootBruhat`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootMatrix`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootPairing`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootTranslation`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootWeyl`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootWeylSections`, `CubicMoment_Theta_CubicThetaPrimeEulerStep`, `CubicMoment_Theta_CubicThetaPrimePowerFourier`, `CubicMoment_Theta_CubicThetaPrimeRootAutomorphicL2`, `CubicMoment_Theta_CubicThetaPrimeRootAutomorphism`, `CubicMoment_Theta_CubicThetaPrimeRootBruhatMatrix`, `CubicMoment_Theta_CubicThetaPrimeRootBruhatResidues`, `CubicMoment_Theta_CubicThetaPrimeRootCoverAction`, `CubicMoment_Theta_CubicThetaPrimeRootCoverBorel`, `CubicMoment_Theta_CubicThetaPrimeRootCoverDegree`, `CubicMoment_Theta_CubicThetaPrimeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeRootCoverMeasure`, `CubicMoment_Theta_CubicThetaPrimeRootCoverTransport`, `CubicMoment_Theta_CubicThetaPrimeRootDiagonal`, `CubicMoment_Theta_CubicThetaPrimeRootDilationOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeRootHorizontal`, `CubicMoment_Theta_CubicThetaPrimeRootIwahoriConjugation`, `CubicMoment_Theta_CubicThetaPrimeRootL2`, `CubicMoment_Theta_CubicThetaPrimeRootLiftL2`, `CubicMoment_Theta_CubicThetaPrimeRootPairing`, `CubicMoment_Theta_CubicThetaPrimeRootPairingL2`, `CubicMoment_Theta_CubicThetaPrimeRootSectionNorm`, `CubicMoment_Theta_CubicThetaPrimeRootSquareCharacter`, `CubicMoment_Theta_CubicThetaPrimeRootTranslation`, `CubicMoment_Theta_CubicThetaPrimeRootTranslationL2`, `CubicMoment_Theta_CubicThetaPrimeRootWeylInvolution`, `CubicMoment_Theta_CubicThetaPrimeRootWeylMeasure`, `CubicMoment_Theta_CubicThetaRadialProfileAlgebra`, `CubicMoment_Theta_CubicThetaRadialProfileEquation`, `CubicMoment_Theta_CubicThetaRadialProfileSeries`, `CubicMoment_Theta_CubicThetaRadialProfileSmooth`, `CubicMoment_Theta_CubicThetaRamifiedIdeal`, `CubicMoment_Theta_CubicThetaRamifiedSeries`, `CubicMoment_Theta_CubicThetaRowContinuation`, `CubicMoment_Theta_CubicThetaRowFourier`, `CubicMoment_Theta_CubicThetaRowGaussBounds`, `CubicMoment_Theta_CubicThetaRowGaussian`, `CubicMoment_Theta_CubicThetaRowMellin`, `CubicMoment_Theta_CubicThetaRowPoisson`, `CubicMoment_Theta_CubicThetaRowRadius`, `CubicMoment_Theta_CubicThetaTorusModes`, `CubicMoment_Theta_CubicThetaTorusSlices`, `CubicMoment_Theta_CubicThetaTotientEuler`, `CubicMoment_Theta_CubicThetaTotientSeries`, `CubicMoment_Theta_CubicThetaUnitCount`, `CubicMoment_Theta_CubicThetaZeroFourier`, `CubicMoment_Theta_CubicThetaZeroObservable`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A007`, `OAIQ096A008` and `OAIQ096A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A017`, `OAIQ096A018`, `OAIQ096A019` and `OAIQ096A020`; the proofs of `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_large_power`, `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_small_power`, `OAI_CubicFirstMoment_angular_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_angular_low_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_balanced_common_squarefree_exponents`, `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment`, `OAI.CubicFirstMoment.first_angular_primeCoordinateError_moment`, `OAI_CubicFirstMoment_low_noncube_mass` and `OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A009

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma schwartz_summable_eisenstein_coset (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    Summable (fun a : Eisenstein => f (z + q * (a : ℂ))) := by
  have h := schwartz_summable_eisenstein
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq)
      (f.compSubConstCLM ℂ (-z)))
  simpa only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    complexMulEquiv_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add,
    add_comm] using h

lemma traceFourier_summable_eisenstein (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) :
    Summable (fun h : Eisenstein => traceFourier f ((h : ℂ) / q)) := by
  have h := schwartz_summable_eisenstein_coset
    (traceFourierSchwartz f) q⁻¹ (inv_ne_zero hq) 0
  simpa only [traceFourierSchwartz_apply, zero_add, div_eq_mul_inv, mul_comm] using h

lemma traceFourier_phase_summable (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    Summable (fun h : Eisenstein =>
      (Real.fourierChar (tracePair z ((h : ℂ) / q)) : ℂ) *
        traceFourier f ((h : ℂ) / q)) := by
  apply Summable.of_norm_bounded (traceFourier_summable_eisenstein f q hq).norm
  intro h
  simp only [norm_mul, Circle.norm_coe, one_mul, le_refl]

end CubicFirstMoment

namespace CubicFirstMoment

lemma periodic_schwartz_summable (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) :
    Summable (fun a : Eisenstein => ψ (Ideal.Quotient.mk (modulus c) a) * f (a : ℂ)) := by
  let : Finite (Residues c) := finite_residues hc
  let : Fintype (Residues c) := Fintype.ofFinite _
  let C := ∑ v : Residues c, ‖ψ v‖
  apply Summable.of_norm_bounded ((schwartz_summable_eisenstein f).norm.mul_left C)
  intro a
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (_root_.norm_nonneg _)
  exact Finset.single_le_sum (fun v _ => _root_.norm_nonneg (ψ v)) (Finset.mem_univ _)

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealExponentNorm_add (ν κ : EisensteinIdealExponent) :
    idealExponentNorm (ν + κ) = idealExponentNorm ν * idealExponentNorm κ := by
  simp only [idealExponentNorm, idealExponentGenerator_add, normNat_mul, Nat.cast_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.instMeasurableSpace
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

/-- The actual Dirichlet-inverse Möbius coefficients have amplitude at most one. -/
lemma idealMoebiusSeries_abs_le_one (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealMoebiusSeries| ≤ 1 := by
  rw [coeff_idealMoebiusSeries_eq_finite ν.support ν (Finset.Subset.refl _)]
  exact finiteIdealMoebius_coeff_abs_le_one _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An absolutely convergent Möbius inverse of the complete ideal Hecke
series. In particular the actual series has no zeros to the right of one. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDirichlet_weight_add (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (s : ℂ) (ν κ : EisensteinIdealExponent) :
    χ (ν+κ)*(idealExponentNorm (ν+κ):ℂ)^(-s)=
      (χ ν*(idealExponentNorm ν:ℂ)^(-s))*(χ κ*(idealExponentNorm κ:ℂ)^(-s)) := by
  rw [hχ,idealExponentNorm_add,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (idealExponentNorm_pos ν).le (idealExponentNorm_pos κ).le]
  ring

lemma idealMoebius_antidiagonal (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      ((MvPowerSeries.coeff p.1 idealMoebiusSeries : ℝ) : ℂ)) = if ν=0 then 1 else 0 := by
  have h := congrArg (MvPowerSeries.coeff ν) idealMoebiusSeries_mul_zeta
  rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_one] at h
  simp only [MvPowerSeries.coeff_apply,idealZeta,mul_one] at h
  simpa only [Complex.ofReal_sum,apply_ite,Complex.ofReal_one,
    Complex.ofReal_zero,MvPowerSeries.coeff_apply] using congrArg Complex.ofReal h

lemma idealMoebius_twist_summable (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) :
    Summable (fun ν => ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*f ν‖) := by
  apply hf.of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ν
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (idealMoebiusSeries_abs_le_one ν)

lemma idealMoebius_twist_convolution (f : EisensteinIdealExponent → ℂ)
    (hf0 : f 0=1) (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      (((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)*f p.1)*f p.2)=
        if ν=0 then 1 else 0 := by
  calc
    _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ))*f ν := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [mul_assoc,←hfadd,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
    _ = _ := by
      rw [idealMoebius_antidiagonal]
      by_cases hν : ν=0
      · subst ν
        simp only [ite_true, if_true,one_mul,hf0]
      · simp only [hν,ite_false, if_false,zero_mul]

lemma idealMoebius_cauchy (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) :
    (∑' ν, ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*f ν)*(∑' ν, f ν)=
      ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        (((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)*f p.1)*f p.2 := by
  have hg := idealMoebius_twist_summable f hf
  exact ideal_cauchy_product _ _ hg hf

lemma idealMoebius_tsum_mul (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) (hf0 : f 0=1)
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) :
    (∑' ν, ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*f ν)*(∑' ν, f ν)=1 := by
  calc
    _ = ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        (((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)*f p.1)*f p.2 := idealMoebius_cauchy f hf
    _ = ∑' ν : EisensteinIdealExponent, if ν=0 then (1:ℂ) else 0 :=
      tsum_congr (idealMoebius_twist_convolution f hf0 hfadd)
    _ = 1 := by simp only [tsum_ite_eq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_le_of_dvd {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ∣ b) : idealExponentOf a ≤ idealExponentOf b := by
  obtain ⟨c,rfl⟩ := hab
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [idealExponentOf_mul ha hc]
  exact le_add_of_nonneg_right zero_le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeToThreeIdeals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ramified Euler restriction in primary-element polynomials.
Prime-to-three ideals are identified arithmetically, then the complete
ideal-sum exclusion formula restores their missing local factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealPrime_dvd_iff {a : Eisenstein} (ha : a ≠ 0) (p : EisensteinIdealPrime) :
    idealPrimeRepresentative p ∣ a ↔ 0 < idealExponentOf a p := by
  constructor
  · intro hd
    have hle := idealExponentOf_le_of_dvd (idealPrimeRepresentative_irreducible p).ne_zero ha hd
    rw [idealExponentOf_primeRepresentative] at hle
    have h := hle p
    simp only [Finsupp.single_eq_same] at h
    omega
  · intro hp
    have hle : Finsupp.single p 1 ≤ idealExponentOf a :=
      Finsupp.single_le_iff.mpr (Nat.succ_le_iff.mpr hp)
    have hd := idealExponentGenerator_dvd_of_le hle
    have hsingle : idealExponentGenerator (Finsupp.single p 1) = idealPrimeRepresentative p := by
      simp [idealExponentGenerator,Finsupp.prod_single_index]
    rw [hsingle] at hd
    exact hd.trans (idealExponentOf_associated ha).dvd

/-- Coprimality is exactly disjoint prime-ideal support, with no omitted
ramified prime or assumption of squarefreeness. -/
lemma isCoprime_iff_idealExponent_disjoint {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsCoprime a b ↔ ∀ p : EisensteinIdealPrime, idealExponentOf a p = 0 ∨ idealExponentOf b p = 0 := by
  constructor
  · intro h p
    by_cases hpa : idealExponentOf a p = 0
    · exact Or.inl hpa
    · right
      by_contra hpb
      exact (idealPrimeRepresentative_irreducible p).not_isUnit
        (h.isRelPrime ((idealPrime_dvd_iff ha p).mpr (Nat.pos_of_ne_zero hpa))
          ((idealPrime_dvd_iff hb p).mpr (Nat.pos_of_ne_zero hpb)))
  · intro h
    apply IsRelPrime.isCoprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors ha).mpr
    intro d hda hdb hd
    let p : EisensteinIdealPrime := ⟨Associates.mk d,Associates.irreducible_mk.mpr hd.irreducible⟩
    have hassoc : Associated (idealPrimeRepresentative p) d := by
      apply Associates.mk_eq_mk_iff_associated.mp
      exact Associates.quot_out p.val
    have hpa := (idealPrime_dvd_iff ha p).mp (hassoc.dvd.trans hda)
    have hpb := (idealPrime_dvd_iff hb p).mp (hassoc.dvd.trans hdb)
    rcases h p with h0 | h0
    · omega
    · omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin transform of the complete ideal theta series. -/
noncomputable section
namespace CubicFirstMoment

lemma idealTheta_scale (A : ℝ)
    (χ : EisensteinIdealExponent → ℂ) :
    idealTheta A χ = fun t => idealTheta 1 χ (t*(1/A)) := by
  funext t
  unfold idealTheta
  apply tsum_congr
  intro ν
  apply congrArg (fun u : ℝ => χ ν*(Real.exp u : ℝ))
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaPole
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An analytic, nonzero numerator for the simple pole at one of the
actual principal ideal zeta function. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def principalZetaPrefactor (s : ℂ) : ℂ :=
  (residueHeckeScale 1:ℂ)^(-s)*(Complex.Gamma s)⁻¹

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cusp stabilizer and the distinguished zero lower-left
row of the cubic Eisenstein series. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaEisensteinTerm_zeroRow (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinTerm cubicThetaZeroRow p s = (p.2:ℂ)^s := by
  simp [cubicThetaEisensteinTerm,CubicThetaBottomRow.phase,CubicThetaBottomRow.height,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue weight used to unfold the cubic Eisenstein series.
Its modulus is exactly 3c, with zero extension outside primary coprime rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_periodic {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (d m : Eisenstein) :
    cubicThetaEisensteinWeight c (d+3*c*m) = cubicThetaEisensteinWeight c d := by
  have hp : primary (d+3*c*m) ↔ primary d := by
    have h3 : (3:Eisenstein) ∣ 3*c*m := ⟨c*m,by ring⟩
    change (3:Eisenstein) ∣ (d+3*c*m)-1 ↔ (3:Eisenstein) ∣ d-1
    rw [show (d+3*c*m)-1 = (d-1)+3*c*m by ring]
    simpa only [add_comm] using (dvd_add_right h3 :
      (3:Eisenstein) ∣ 3*c*m+(d-1) ↔ (3:Eisenstein) ∣ d-1)
  have hg : IsCoprime c (d+3*c*m) ↔ IsCoprime c d := by
    rw [show d+3*c*m = d+c*(3*m) by ring]
    exact IsCoprime.add_mul_left_right_iff
  unfold cubicThetaEisensteinWeight
  rw [hp,hg]
  split_ifs with hd
  · let r : CubicThetaBottomRow := ⟨c,d,hc,hd.1,hd.2⟩
    have he := congrArg star (r.shift_phase m)
    simpa only [CubicThetaBottomRow.phase,CubicThetaBottomRow.shift_c,
      CubicThetaBottomRow.shift_d,star_star] using he
  · rfl

def cubicThetaEisensteinResidueWeight (c : Eisenstein) (x : Residues (3*c)) : ℂ :=
  cubicThetaEisensteinWeight c (residueRepresentative (3*c) x)

lemma cubicThetaEisensteinResidueWeight_mk {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (d : Eisenstein) :
    cubicThetaEisensteinResidueWeight c (Ideal.Quotient.mk (modulus (3*c)) d) =
      cubicThetaEisensteinWeight c d := by
  let r := residueRepresentative (3*c) (Ideal.Quotient.mk (modulus (3*c)) d)
  have hd : (3*c) ∣ r-d := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    change Ideal.Quotient.mk (modulus (3*c)) r-Ideal.Quotient.mk (modulus (3*c)) d = 0
    rw [residueRepresentative_spec,sub_self]
  obtain ⟨m,hm⟩ := hd
  change cubicThetaEisensteinWeight c r = _
  rw [show r = d+3*c*m by linear_combination hm]
  exact cubicThetaEisensteinWeight_periodic hc d m

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowGaussian
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shifted Gaussians for the actual Eisenstein row, with the exact
trace-Fourier scaling and translation factors. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

def cubicThetaShiftedGaussian (c z : ℂ) (hc : c ≠ 0) (t : ℝ) (ht : 0 < t) :
    𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (complexMulEquiv c⁻¹ (inv_ne_zero hc))
    ((radialGaussianSchwartz t ht).compSubConstCLM ℂ (-z))

lemma cubicThetaShiftedGaussian_apply (c z : ℂ) (hc : c ≠ 0)
    (t : ℝ) (ht : 0 < t) (x : ℂ) :
    cubicThetaShiftedGaussian c z hc t ht x = (Real.exp (-t*‖z+x/c‖^2):ℂ) := by
  change radialGaussianSchwartz t ht (c⁻¹*x- -z) = _
  have he : c⁻¹*x- -z = z+x/c := by rw [div_eq_mul_inv]; ring
  rw [he, radialGaussianSchwartz_apply]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Gauss coefficient and Poisson expansion of a
nonzero cubic Eisenstein row. The dual lattice is independent of the row. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaEisensteinGaussCoefficient (c h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*c), cubicThetaEisensteinResidueWeight c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      ((h:ℂ)/((3*c: Eisenstein)*traceLambda))):ℂ)

def cubicThetaEisensteinGaussianRow (c : Eisenstein) (z : ℂ) (t : ℝ) : ℂ :=
  ∑' d : Eisenstein, cubicThetaEisensteinWeight c d*
    (Real.exp (-t*‖z+(d:ℂ)/(c:ℂ)‖^2):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowGaussBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds and the exact norm of the fixed dual frequency. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_norm (c d : Eisenstein) :
    ‖cubicThetaEisensteinWeight c d‖ ≤ 1 := by
  unfold cubicThetaEisensteinWeight
  split_ifs with h
  · exact norm_cubicSymbol_le_one h.1 c
  · norm_num

lemma cubicThetaEisensteinGaussCoefficient_norm {c : Eisenstein} (hc : c ≠ 0)
    (h : Eisenstein) :
    ‖cubicThetaEisensteinGaussCoefficient c h‖ ≤ (Nat.card (Residues (3*c)):ℝ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  unfold cubicThetaEisensteinGaussCoefficient
  rw [tsum_fintype, Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ x : Residues (3*c),
        ‖cubicThetaEisensteinResidueWeight c x*
          (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
            ((h:ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residues (3*c), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Circle.norm_coe, mul_one]
      exact cubicThetaEisensteinWeight_norm c _
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Character orthogonality for the constant Fourier coefficient, on
the actual subgroup of primary residue classes modulo 3c. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_mul {u c : Eisenstein} (hu : primary u)
    (hcu : IsCoprime c u) (d : Eisenstein) :
    cubicThetaEisensteinWeight c (u*d) = cubicSymbol u c*cubicThetaEisensteinWeight c d := by
  have hp : primary (u*d) ↔ primary d := by
    rw [primary_iff_residue_one, primary_iff_residue_one, map_mul,
      (primary_iff_residue_one u).mp hu, one_mul]
  have hg : IsCoprime c (u*d) ↔ IsCoprime c d := by
    rw [IsCoprime.mul_right_iff, and_iff_right hcu]
  unfold cubicThetaEisensteinWeight
  rw [hp,hg]
  split_ifs with hd
  · exact cubicSymbol_mul_lower (primary_ne_zero hu) (primary_ne_zero hd.1) c
  · simp

lemma cubicThetaEisensteinResidueWeight_mul {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hu : primary u) (hcu : IsCoprime c u)
    (x : Residues (3*c)) :
    cubicThetaEisensteinResidueWeight c (Ideal.Quotient.mk (modulus (3*c)) u*x) =
      cubicSymbol u c*cubicThetaEisensteinResidueWeight c x := by
  calc
    _ = cubicThetaEisensteinResidueWeight c
        (Ideal.Quotient.mk (modulus (3*c)) (u*residueRepresentative (3*c) x)) := by
      rw [map_mul, residueRepresentative_spec]
    _ = cubicThetaEisensteinWeight c (u*residueRepresentative (3*c) x) :=
      cubicThetaEisensteinResidueWeight_mk hc _
    _ = _ := cubicThetaEisensteinWeight_mul hu hcu _

theorem cubicThetaEisenstein_constant_vanish {c u : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c ≠ 0) (hu : primary u)
    (hcu : IsCoprime c u) (hchi : cubicSymbol u c ≠ 1) :
    cubicThetaEisensteinGaussCoefficient c 0 = 0 := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have h3u : IsCoprime (3:Eisenstein) u :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hu (dvd_refl u))
  have hU := residue_isUnit_of_isCoprime (h3u.mul_left hcu)
  let U : (Residues (3*c))ˣ := hU.unit
  have hUv : (U : Residues (3*c)) = Ideal.Quotient.mk (modulus (3*c)) u := hU.unit_spec
  have he : (∑ x : Residues (3*c), cubicThetaEisensteinResidueWeight c x) =
      cubicSymbol u c*∑ x : Residues (3*c), cubicThetaEisensteinResidueWeight c x := by
    calc
      _ = ∑ x : Residues (3*c), cubicThetaEisensteinResidueWeight c ((U:Residues (3*c))*x) :=
        (Equiv.sum_comp U.mulLeft _).symm
      _ = _ := by
        simp_rw [hUv, cubicThetaEisensteinResidueWeight_mul hc hu hcu]
        rw [Finset.mul_sum]
  have hz := eq_zero_of_mul_eq_self_left hchi he.symm
  simpa [cubicThetaEisensteinGaussCoefficient, tracePair, tsum_fintype] using hz

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cube support of the constant coefficient of the cubic
Eisenstein series, including the ramified factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_cube {c : Eisenstein} (hcb : ∃ j : Eisenstein, j^3=c)
    (d : Eisenstein) :
    cubicThetaEisensteinWeight c d = if primary d ∧ IsCoprime c d then 1 else 0 := by
  unfold cubicThetaEisensteinWeight
  split_ifs with hd
  · obtain ⟨j,rfl⟩ := hcb
    have hdj : IsCoprime d j := hd.2.symm.of_isCoprime_of_dvd_right
      (dvd_pow_self j (by norm_num : (3:ℕ) ≠ 0))
    rw [cubicSymbol_pow_upper hd.1, cubicSymbol_cube_of_isCoprime hd.1 j hdj]
  · rfl

theorem cubicThetaEisenstein_constant_cube {c : Eisenstein}
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0 =
      ∑' x : Residues (3*c), if primary (residueRepresentative (3*c) x) ∧
        IsCoprime c (residueRepresentative (3*c) x) then (1:ℂ) else 0 := by
  unfold cubicThetaEisensteinGaussCoefficient cubicThetaEisensteinResidueWeight
  simp only [Eisenstein.coe_zero, zero_div, tracePair, mul_zero, Complex.zero_re,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  apply tsum_congr
  intro x
  exact cubicThetaEisensteinWeight_cube hcb _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaUnitReductionThree (c : Eisenstein) : (Residues (3*c))ˣ →* (Residues 3)ˣ :=
  Units.map (cubicThetaReductionThree c).toMonoidHom

lemma cubicTheta_primaryResidue_iff (c : Eisenstein) (x : Residues (3*c)) :
    (primary (residueRepresentative (3*c) x) ∧
      IsCoprime c (residueRepresentative (3*c) x)) ↔
      (IsUnit x ∧ cubicThetaReductionThree c x = 1) := by
  have hred : Ideal.Quotient.mk (modulus 3) (residueRepresentative (3*c) x) =
      cubicThetaReductionThree c x := by
    change residueReduction (show (3:Eisenstein) ∣ 3*c from ⟨c,rfl⟩)
      (Ideal.Quotient.mk (modulus (3*c)) (residueRepresentative (3*c) x)) = _
    rw [residueRepresentative_spec]
    rfl
  constructor
  · rintro ⟨hp,hc⟩
    refine ⟨?_,?_⟩
    · have hu := residue_isUnit_of_isCoprime ((primary_coprime_three hp).symm.mul_left hc)
      rwa [residueRepresentative_spec] at hu
    · rw [←hred]
      exact (primary_iff_residue_one _).mp hp
  · rintro ⟨hu,hr⟩
    refine ⟨(primary_iff_residue_one _).mpr (hred.trans hr),?_⟩
    have hcop : IsCoprime (3*c) (residueRepresentative (3*c) x) :=
      isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
    exact hcop.of_mul_left_right

def cubicThetaPrimaryResidueEquivKernel (c : Eisenstein) :
    CubicThetaPrimaryResidue c ≃ (cubicThetaUnitReductionThree c).ker where
  toFun x := ⟨x.property.1.unit, by
    apply Units.ext
    change cubicThetaReductionThree c (x.property.1.unit : Residues (3*c)) = 1
    rw [x.property.1.unit_spec]
    exact x.property.2⟩
  invFun u := ⟨(u.val : Residues (3*c)),u.val.isUnit,by
    have he := congrArg (fun v : (Residues 3)ˣ => (v : Residues 3))
      ((MonoidHom.mem_ker).mp u.property)
    exact he⟩
  left_inv x := by
    apply Subtype.ext
    exact x.property.1.unit_spec
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact IsUnit.unit_spec _

theorem cubicThetaPrimaryResidue_card {c : Eisenstein} (hc : c ≠ 0) :
    Nat.card (Residues (3*c))ˣ =
      Nat.card (Residues (3:Eisenstein))ˣ*Nat.card (CubicThetaPrimaryResidue c) := by
  let f := cubicThetaUnitReductionThree c
  have hf : Function.Surjective f := residueReduction_units_surjective
    (mul_ne_zero (by norm_num) hc) ⟨c,rfl⟩
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at he
  rw [Nat.card_congr (cubicThetaPrimaryResidueEquivKernel c)]
  exact he

theorem cubicThetaEisenstein_constant_card {c : Eisenstein} (hc : c ≠ 0)
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0 = (Nat.card (CubicThetaPrimaryResidue c):ℂ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  rw [cubicThetaEisenstein_constant_cube hcb]
  simp_rw [cubicTheta_primaryResidue_iff]
  rw [tsum_fintype, Nat.card_eq_fintype_card]
  change (∑ x : Residues (3*c), if IsUnit x ∧ cubicThetaReductionThree c x = 1 then (1:ℂ) else 0) =
    (Fintype.card {x : Residues (3*c) // IsUnit x ∧ cubicThetaReductionThree c x = 1}:ℂ)
  rw [Fintype.card_subtype]
  simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The six units and the exact index of primary invertible residues. -/
noncomputable section
namespace CubicFirstMoment

lemma eisenstein_unit_pow_six (u : Eisensteinˣ) : u^6=1 := by
  apply Units.ext
  change (u:Eisenstein)^6=1
  have hp (j : ℕ) : (omegaE^j)^6=1 := by
    have hc : (omegaE^j)^3=1 := by
      rw [←pow_mul,Nat.mul_comm j 3,pow_mul,omegaE_cube,one_pow]
    calc
      _ = ((omegaE^j)^3)^2 := by ring
      _ = 1 := by rw [hc]; norm_num
  obtain ⟨j,hj | hj⟩ := eisenstein_unit_eq_signed_omega u.isUnit
  · rw [hj]; exact hp j
  · rw [hj,neg_pow,show (-1:Eisenstein)^6=1 by norm_num,one_mul]
    exact hp j

def eisensteinUnitsEquivSixthRoots : Eisensteinˣ ≃ rootsOfUnity 6 Eisenstein where
  toFun u := ⟨u,by exact eisenstein_unit_pow_six u⟩
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

lemma eisenstein_units_card : Nat.card Eisensteinˣ=6 := by
  rw [Nat.card_congr eisensteinUnitsEquivSixthRoots]
  exact eisenstein_neg_omega_primitive.card_rootsOfUnity

lemma cubicTheta_residue_three_units_card : Nat.card (Residues (3:Eisenstein))ˣ=6 := by
  rw [←Nat.card_congr (Equiv.ofBijective _ eisensteinUnitReductionThree_bijective)]
  exact eisenstein_units_card

theorem cubicTheta_primaryResidue_six {c : Eisenstein} (hc : c≠0) :
    Nat.card (Residues (3*c))ˣ=6*Nat.card (CubicThetaPrimaryResidue c) := by
  rw [cubicThetaPrimaryResidue_card hc,cubicTheta_residue_three_units_card]

theorem cubicThetaEisenstein_constant_units {c : Eisenstein} (hc : c≠0)
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0=(Nat.card (Residues (3*c))ˣ:ℂ)/6 := by
  rw [cubicThetaEisenstein_constant_card hc hcb,cubicTheta_primaryResidue_six hc]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact arithmetic coefficient of a cube row, with its ramified
factor and finite-ring Euler totient retained. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisenstein_constant_cube_totient {j : Eisenstein} (hj : j≠0)
    (h3 : (3:Eisenstein)∣j^3) :
    cubicThetaEisensteinGaussCoefficient (j^3) 0 =
      (3/2:ℂ)*(normNat j:ℂ)^2*(Nat.card (Residues j)ˣ:ℂ) := by
  rw [cubicThetaEisenstein_constant_units (pow_ne_zero _ hj) ⟨j,rfl⟩,
    cubicTheta_three_units_card (pow_ne_zero _ hj) h3]
  have he := cubicTheta_power_units_card hj 2
  rw [he]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma eisenstein_unit_cube_sign (u : Eisensteinˣ) :
    (u:Eisenstein)^3=1 ∨ (u:Eisenstein)^3 = -1 := by
  obtain ⟨j,hj | hj⟩ := eisenstein_unit_eq_signed_omega u.isUnit
  · left
    rw [hj,←pow_mul,Nat.mul_comm j 3,pow_mul,omegaE_cube,one_pow]
  · right
    rw [hj,neg_pow,←pow_mul,Nat.mul_comm j 3,pow_mul,omegaE_cube,one_pow]
    norm_num

lemma cubicThetaSignedCube_ne_zero (ε : Bool) (ν : EisensteinIdealExponent) :
    cubicThetaSignedCube ε ν≠0 := by
  cases ε <;> simp [cubicThetaSignedCube,idealExponentGenerator_ne_zero]

lemma cubicTheta_idealExponentOf_neg {a : Eisenstein} (ha : a≠0) :
    idealExponentOf (-a)=idealExponentOf a :=
  idealExponentOf_eq_of_associated (neg_ne_zero.mpr ha) ha (Associated.refl a).neg_left

def cubicThetaCubeCoordinatesMap (x : Bool × EisensteinIdealExponent) : CubicThetaNonzeroCube :=
  ⟨cubicThetaSignedCube x.1 x.2,cubicThetaSignedCube_ne_zero x.1 x.2,
    cubicThetaSignedCube_is_cube x.1 x.2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientEuler
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaIdealTotient_single (p : EisensteinIdealPrime) (n : ℕ) :
    cubicThetaIdealTotient (Finsupp.single p (n+1))=
      normNat (idealPrimeRepresentative p)^n*(normNat (idealPrimeRepresentative p)-1) := by
  unfold cubicThetaIdealTotient idealExponentGenerator
  rw [Finsupp.prod_single_index (h:=fun p k => idealPrimeRepresentative p^k) (pow_zero _),
    cubicTheta_power_units_card (idealPrimeRepresentative_irreducible p).ne_zero]
  have he := cubicTheta_primePower_units_card (idealPrimeRepresentative_irreducible p).prime 0
  rw [show (0+1:ℕ)=1 from rfl,pow_one,pow_zero] at he
  simp only [pow_one] at he
  exact congrArg (fun k => normNat (idealPrimeRepresentative p)^n*k) he

lemma cubicThetaIdealTotient_single_real (p : EisensteinIdealPrime) {n : ℕ} (hn : n≠0) :
    (cubicThetaIdealTotient (Finsupp.single p n):ℝ)=
      idealExponentNorm (Finsupp.single p n)*
        (1-1/(normNat (idealPrimeRepresentative p):ℝ)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [cubicThetaIdealTotient_single,idealExponentNorm_single]
  have hN : 0 < (normNat (idealPrimeRepresentative p):ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (normNat_ne_zero (idealPrimeRepresentative_irreducible p).ne_zero))
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (normNat_ne_zero (idealPrimeRepresentative_irreducible p).ne_zero)),Nat.cast_one,pow_succ]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaIdealDensity_norm (ν : EisensteinIdealExponent) :
    ‖cubicThetaIdealDensity ν‖ ≤ 1 := by
  let : Finite (Residues (idealExponentGenerator ν)) :=
    finite_residues (idealExponentGenerator_ne_zero ν)
  have he := Nat.card_le_card_of_injective
    (fun u : (Residues (idealExponentGenerator ν))ˣ => (u:Residues (idealExponentGenerator ν)))
    Units.val_injective
  rw [residues_card (idealExponentGenerator_ne_zero ν)] at he
  have hN := idealExponentNorm_pos ν
  have hreal : (cubicThetaIdealTotient ν:ℝ) ≤ idealExponentNorm ν := by
    change (Nat.card (Residues (idealExponentGenerator ν))ˣ:ℝ)≤
      (normNat (idealExponentGenerator ν):ℝ)
    exact_mod_cast he
  rw [cubicThetaIdealDensity,norm_div,Complex.norm_natCast,Complex.norm_real,
    Real.norm_of_nonneg hN.le]
  exact (div_le_one hN).mpr hreal

lemma cubicTheta_norm_cpow_shift (ν : EisensteinIdealExponent) (s : ℂ) :
    (idealExponentNorm ν:ℂ)^(-(s+1))=
      (idealExponentNorm ν:ℂ)^(-s)/(idealExponentNorm ν:ℂ) := by
  rw [show -(s+1)=-s+(-1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'),
    Complex.cpow_neg_one,div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDensityLocal
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaPrimeDensity_norm (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    ‖cubicThetaPrimeDensity p ν‖≤1 := by
  unfold cubicThetaPrimeDensity
  split_ifs
  · exact cubicThetaIdealDensity_norm ν
  · simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedIdeal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single ramified ideal in the cube part of the constant term. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPrime_associated :
    Associated (idealPrimeRepresentative cubicThetaRamifiedPrime) lambdaE := by
  apply Associates.mk_eq_mk_iff_associated.mp
  exact Associates.quot_out _

lemma cubicThetaRamifiedPrime_norm : normNat (idealPrimeRepresentative cubicThetaRamifiedPrime)=3 := by
  rw [associated_normNat cubicThetaRamifiedPrime_associated]
  apply Nat.cast_injective (R:=ℝ)
  rw [normNat_cast]
  exact traceLambda_normSq

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact ramified local factor of the normalized totient series. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedDensitySeries (s : ℂ) : ℂ :=
  normDirichletSeries (cubicThetaPrimeDensity cubicThetaRamifiedPrime) idealExponentNorm s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaConstantTermWeight (s : ℂ) (c : Eisenstein) : ℂ :=
  if (3:Eisenstein)∣c ∧ c≠0 then
    cubicThetaEisensteinGaussCoefficient c 0*(norm c:ℂ)^(-s) else 0

def cubicThetaConstantDirichlet (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, cubicThetaConstantTermWeight s c

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDualHeatSummability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute summation of the integrated Fourier heat modes. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaDualHeat_mass_summable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  let b : ℝ := 4*Real.pi^2/27
  have hb : 0 < b := by dsimp [b]; positivity
  let J : ℝ := Real.Gamma (s.re+1)*(v^2)^(-(s.re+1))
  have hJ : 0 ≤ J := by
    apply mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
    exact Real.rpow_nonneg (sq_nonneg v) _
  let K : ℝ := (2/b^2)*J
  have hK : 0 ≤ K := mul_nonneg (by positivity) hJ
  let m0 : ℝ := ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s 0 t‖
  have hm0 : 0 ≤ m0 := integral_nonneg (fun _ => _root_.norm_nonneg _)
  have ht := (hasSum_ite_eq (0:Eisenstein) m0).summable.add
    ((summable_eisenstein_norm_rpow (s := 2) (by norm_num)).mul_left K)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    by_cases hh : h = 0
    · subst h
      simp only [cubicThetaRowHeatScale_zero, ite_true, if_true]
      exact le_add_of_nonneg_right (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
    · simp only [hh, ite_false, if_false, zero_add]
      apply (cubicThetaDualHeat_norm_mass_bound hv hs (cubicThetaRowHeatScale_pos hh)).trans_eq
      rw [cubicThetaRowHeatScale_eq]
      change (2/(b*norm h)^2)*J = K*(norm h)^(-(2:ℝ))
      rw [Real.rpow_neg (norm_nonneg h), Real.rpow_two]
      dsimp [K]
      ring

theorem cubicThetaWeightedDualHeat_mass_summable {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) {c : Eisenstein} (hc : c ≠ 0) (z : ℂ) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖(cubicThetaEisensteinGaussCoefficient c h*
        (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  have ht := (cubicThetaDualHeat_mass_summable hv hs).mul_left
    (Nat.card (Residues (3*c)):ℝ)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    simp_rw [norm_mul, Circle.norm_coe, mul_one]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaEisensteinGaussCoefficient_norm hc h)
      (integral_nonneg (fun _ => _root_.norm_nonneg _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowRadius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scaling and absolute convergence of a nonzero Eisenstein row
in the radial coordinate used for the Gaussian Mellin integral. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRowRadius_power {c : Eisenstein} (hc : c ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) (d : Eisenstein) (σ : ℝ) :
    (cubicThetaRowRadius c p d)^(-σ) = (norm c/p.2)^σ*
      (p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2))^σ := by
  have hN := norm_pos_of_ne_zero hc
  have hR := cubicThetaRowRadius_pos c d hp
  rw [← cubicThetaRowRadius_scale hc]
  rw [← Real.mul_rpow (div_pos hN hp).le (div_pos hp (mul_pos hN hR)).le]
  have he : (norm c/p.2)*(p.2/(norm c*cubicThetaRowRadius c p d)) =
      (cubicThetaRowRadius c p d)⁻¹ := by field_simp
  rw [he, Real.inv_rpow hR.le, Real.rpow_neg hR.le]

theorem cubicThetaRowRadius_summable {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun d : Eisenstein => ‖cubicThetaEisensteinWeight c d‖*
      (cubicThetaRowRadius c p d)^(-s.re)) := by
  have hr := ((cubicThetaEisensteinGrid_summable hp hs).norm).comp_injective
    (show Function.Injective (fun d : Eisenstein => (c,d)) from fun _ _ he => (Prod.mk.inj he).2)
  have hi := hr.mul_left ((norm c/p.2)^s.re)
  apply hi.congr
  intro d
  dsimp only [Function.comp_apply]
  have hpos : 0 < p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2) := by
    rw [← cubicThetaRowRadius_scale hc0]
    exact div_pos hp (mul_pos (norm_pos_of_ne_zero hc0) (cubicThetaRowRadius_pos c d hp))
  rw [cubicThetaEisensteinGridTerm_row hc, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    cubicThetaRowRadius_power hc0 hp]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian row identity integrated to the actual Eisenstein row
on its initial half-plane of absolute convergence. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaEisensteinRow (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' d : Eisenstein, cubicThetaEisensteinGridTerm (c,d) p s

theorem cubicThetaEisensteinRow_mellin {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisensteinRow c p s =
      ((p.2/norm c:ℝ):ℂ)^s*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(Real.exp (-p.2^2*t):ℂ)*
          cubicThetaEisensteinGaussianRow c p.1 t := by
  have hscale : cubicThetaEisensteinRow c p s =
      ((p.2/norm c:ℝ):ℂ)^s*∑' d : Eisenstein,
        cubicThetaEisensteinWeight c d*(cubicThetaRowRadius c p d:ℂ)^(-s) := by
    unfold cubicThetaEisensteinRow
    rw [← tsum_mul_left]
    apply tsum_congr
    intro d
    rw [cubicThetaEisensteinGridTerm_row hc, cubicThetaRowRadius_complex_power hc0 hp]
    ring
  have hM := cubicTheta_laplace_tsum (cubicThetaEisensteinWeight c)
    (cubicThetaRowRadius c p) (fun d => cubicThetaRowRadius_pos c d hp)
    (show 0 < s.re by linarith) (cubicThetaRowRadius_summable hc hc0 hp hs)
  rw [hscale, mul_left_comm, hM]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  unfold cubicThetaEisensteinGaussianRow
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro d
  have he : Real.exp (-cubicThetaRowRadius c p d*t) =
      Real.exp (-p.2^2*t)*Real.exp (-t*‖p.1+(d:ℂ)/(c:ℂ)‖^2) := by
    rw [← Real.exp_add]
    congr 1
    unfold cubicThetaRowRadius
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [he, Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaRowFourierCoefficient (c : Eisenstein) (z : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaEisensteinGaussCoefficient c h*
    (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinFourierRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal Eisenstein series as a sum of its explicitly
transformed rows, retaining the leading cusp term. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinRow_zero (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinRow 0 p s = (p.2:ℂ)^s := by
  unfold cubicThetaEisensteinRow
  calc
    _ = ∑' d : Eisenstein, if d = 1 then (p.2:ℂ)^s else 0 := by
      apply tsum_congr
      intro d
      by_cases hd : d = 1
      · subst d
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,
          primary_one,cubicSymbol_one_lower,norm,isCoprime_zero_left]
      · have hp : ¬(primary d ∧ IsCoprime (0:Eisenstein) d) := by
          intro h
          exact hd (primary_unit_eq_one (isCoprime_zero_left.mp h.2) h.1)
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hd,hp]
    _ = _ := by simp

lemma cubicThetaEisensteinRow_nondivisible {c : Eisenstein}
    (hc : ¬(3:Eisenstein) ∣ c) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinRow c p s = 0 := by
  simp [cubicThetaEisensteinRow,cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero Fourier mode of the actual Eisenstein row expansion,
including its exact archimedean factor. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_zero_row_factor {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1 < s.re)
    {c : Eisenstein} (hc : c≠0) :
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaEisensteinGaussCoefficient c 0*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s =
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*
        (cubicThetaEisensteinGaussCoefficient c 0*(norm c:ℂ)^(-s)) := by
  have hs0 : s-1≠0 := by intro h; have he := congrArg Complex.re h; simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at he; linarith
  have hg := Complex.Gamma_add_one (s-1) hs0
  rw [sub_add_cancel] at hg
  rw [cubicThetaDualHeat_zero_integral hv hs,hg]
  have hp := cubicTheta_zero_height_factor hv (norm_pos_of_ne_zero hc) s
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (show 0<(s-1).re by simp only [Complex.sub_re,Complex.one_re]; linarith)
  calc
    _ = ((v/norm c:ℝ):ℂ)^s*((v^2:ℝ):ℂ)^(1-s)*
        (2*Real.pi/(9*Real.sqrt 3):ℂ)*cubicThetaEisensteinGaussCoefficient c 0/(s-1) := by
      field_simp
    _ = _ := by rw [hp]; ring

def cubicThetaEisensteinConstantMode (v : ℝ) (s : ℂ) : ℂ :=
  (v:ℂ)^s+∑' c : Eisenstein, if (3:Eisenstein)∣c ∧ c≠0 then
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaEisensteinGaussCoefficient c 0*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s else 0

theorem cubicThetaEisensteinConstantMode_eq {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaEisensteinConstantMode v s=(v:ℂ)^s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*cubicThetaConstantDirichlet s := by
  unfold cubicThetaEisensteinConstantMode cubicThetaConstantDirichlet
  rw [←tsum_mul_left]
  congr 1
  apply tsum_congr
  intro c
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · simp only [cubicThetaConstantTermWeight,ite_eq_left hc]
    exact cubicTheta_zero_row_factor hv hs hc.2
  · simp [hc,cubicThetaConstantTermWeight]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonzero Fourier Dirichlet coefficients and their common
majorant on Re(s)>2. This permits reordering the two lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaFrequencyTerm (s : ℂ) (h c : Eisenstein) : ℂ :=
  if (3:Eisenstein)∣c ∧ c≠0 then
    cubicThetaEisensteinGaussCoefficient c h*(norm c:ℂ)^(-s) else 0

def cubicThetaFrequencyDirichlet (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, cubicThetaFrequencyTerm s h c

lemma cubicThetaEisensteinGaussCoefficient_norm_real {c : Eisenstein} (hc : c≠0)
    (h : Eisenstein) : ‖cubicThetaEisensteinGaussCoefficient c h‖≤9*norm c := by
  have hb := cubicThetaEisensteinGaussCoefficient_norm hc h
  rw [residues_card (mul_ne_zero (by norm_num) hc),normNat_cast] at hb
  have h3 : norm (3:Eisenstein)=9 := by
    change Complex.normSq (3:ℂ)=9
    norm_num
  simpa only [norm_mul_eq,h3] using hb

lemma cubicThetaFrequencyTerm_bound {s : ℂ} (_hs : 2 < s.re) (h c : Eisenstein) :
    ‖cubicThetaFrequencyTerm s h c‖≤9*(norm c)^(-(s.re-1)) := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · rw [cubicThetaFrequencyTerm,ite_eq_left hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hc.2)]
    simp only [Complex.neg_re]
    calc
      _ ≤ (9*norm c)*(norm c)^(-s.re) :=
        mul_le_mul_of_nonneg_right (cubicThetaEisensteinGaussCoefficient_norm_real hc.2 h)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by
        have he : norm c*(norm c)^(-s.re)=(norm c)^(-(s.re-1)) := by
          calc
            _ = (norm c)^(1:ℝ)*(norm c)^(-s.re) := by rw [Real.rpow_one]
            _ = _ := by
              rw [←Real.rpow_add (norm_pos_of_ne_zero hc.2)]
              congr 1
              ring
        rw [mul_assoc,he]
  · simp only [cubicThetaFrequencyTerm,ite_eq_right hc,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

lemma cubicThetaFrequencyTerm_norm_summable {s : ℂ} (hs : 2 < s.re) (h : Eisenstein) :
    Summable (fun c => ‖cubicThetaFrequencyTerm s h c‖) := by
  exact ((summable_eisenstein_norm_rpow (show 1 < s.re-1 by linarith)).mul_left 9).of_nonneg_of_le
    (fun _ => _root_.norm_nonneg _) (cubicThetaFrequencyTerm_bound hs h)

lemma cubicThetaFrequencyDirichlet_zero (s : ℂ) :
    cubicThetaFrequencyDirichlet 0 s=cubicThetaConstantDirichlet s := rfl

lemma cubicThetaFrequency_heat_norm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun ch : Eisenstein × Eisenstein =>
      ‖cubicThetaFrequencyTerm s ch.2 ch.1*
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
  exact mul_le_mul (cubicThetaFrequencyTerm_bound hs ch.2 ch.1)
    (norm_integral_le_integral_norm _) (_root_.norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary inverse-frequency decay of the nonzero heat modes.
The order is chosen after the spectral parameter, without restricting
the latter to its initial half-plane. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaNonzeroHeat_mass_summable {v : ℝ} (hv : 0<v) (s : ℂ) :
    Summable (fun h : Eisenstein => if h=0 then 0 else
      ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2:ℝ) (2-s.re))
  have hk2 : 1<(k:ℝ) := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hk)
  have hks : 0 < s.re+(k:ℝ)-1 := by
    have := (le_max_right (2:ℝ) (2-s.re)).trans_lt hk
    linarith
  let b : ℝ := 4*Real.pi^2/27
  have hb : 0<b := by dsimp [b]; positivity
  let J : ℝ := Real.Gamma (s.re+(k:ℝ)-1)*(v^2)^(-(s.re+(k:ℝ)-1))
  let K : ℝ := ((k.factorial:ℝ)/b^k)*J
  have hK : 0≤K := by
    dsimp [K,J]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos hb k).le)
      (mul_nonneg (Real.Gamma_pos_of_pos hks).le (Real.rpow_nonneg (sq_nonneg _) _))
  apply ((summable_eisenstein_norm_rpow hk2).mul_left K).of_nonneg_of_le
  · intro h
    split_ifs
    · exact le_rfl
    · exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    by_cases hh : h=0
    · rw [ite_eq_left hh]
      exact mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [ite_eq_right hh]
      apply (cubicThetaNonzeroHeat_norm_mass_power hv (cubicThetaRowHeatScale_pos hh) s k hks).trans_eq
      rw [cubicThetaRowHeatScale_eq,show 4*Real.pi^2/27=b from rfl,mul_pow,
        Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
      dsimp only [K,J]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation of each individual Eisenstein row. Its nonzero modes
are entire; the constant mode can have a pole only at s=1. This does not
interchange continuation with the infinite sum over rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFrequencyTerm_entire (h c : Eisenstein) :
    Differentiable ℂ (fun s => cubicThetaFrequencyTerm s h c) := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · let _ : NeZero (norm c:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hc.2).ne'⟩
    simp only [cubicThetaFrequencyTerm,ite_eq_left hc]
    exact ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg).const_mul _
  · simp only [cubicThetaFrequencyTerm,ite_eq_right hc]
    exact differentiable_const 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming cutoff series uses the actual primitive bottom rows.
Above the arithmetic cusp threshold at most one row contributes. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaIncomingEisenstein_high {p : ℂ × ℝ} (hp : 1<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein p s=cubicThetaCuspCutoff p.2*(p.2:ℂ)^s := by
  have he : cubicThetaIncomingEisenstein p s=cubicThetaIncomingTerm cubicThetaZeroRow p s := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hc := r.high_height_c_zero hp (cubicThetaIncomingTerm_high hn)
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he,cubicThetaIncomingTerm,cubicThetaEisensteinTerm_zeroRow]
  simp [CubicThetaBottomRow.height,cubicThetaZeroRow,norm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusModes
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaFourierIndex : Eisenstein ≃ (Fin 2 → ℤ) :=
  (dualIntegerEquiv.trans coordinatesEquiv.toEquiv).symm

lemma cubicTheta_trace_period_cell (h : Eisenstein) (x : Fin 2 → ℝ) :
    tracePair (cubicThetaPeriodCell x) (cubicThetaRowFrequency h)=
      ∑ i, x i*(cubicThetaFourierIndex h i:ℝ) := by
  have he : dualRealCoords (fun i => (cubicThetaFourierIndex h i:ℝ))=(h:ℂ)/traceLambda := by
    rw [dualRealCoords_integer]
    congr 1
    exact congrArg (fun h : Eisenstein => (h:ℂ)) (cubicThetaFourierIndex.symm_apply_apply h)
  rw [← dualRealCoords_trace,he]
  unfold tracePair cubicThetaPeriodCell cubicThetaRowFrequency
  congr 2
  field_simp

def cubicThetaTorusFourier (h : Eisenstein) : C(UnitAddTorus (Fin 2),ℂ) :=
  UnitAddTorus.mFourier (cubicThetaFourierIndex h)

lemma cubicThetaTorusFourier_actual (h : Eisenstein) (x : Fin 2 → ℝ) :
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=
      (Real.fourierChar (tracePair (cubicThetaPeriodCell x) (cubicThetaRowFrequency h)):ℂ) := by
  rw [cubicTheta_trace_period_cell]
  exact cubicTheta_torus_fourier_real _ _

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions
def cubicThetaTorusCoefficient (F : CubicThetaTorusL2) (h : Eisenstein) : ℂ :=
  UnitAddTorus.mFourierCoeff F (cubicThetaFourierIndex h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusSlices
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier coefficients of L2 cusp slices. The finite Bessel bounds and
Parseval identity justify the square-summable family of radial L2 modes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CubicFirstMoment

local instance instMeasureSpaceUnitAddCircle_solutions_1_r27a815_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_r27a815_1 : Countable Eisenstein := cubicThetaFourierIndex.injective.countable
def cubicThetaTorusCoefficientMap (h : Eisenstein) : CubicThetaTorusL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : Fin 2 → ℤ => ℂ) 2 (cubicThetaFourierIndex h)).comp
    UnitAddTorus.mFourierBasis.repr.toLinearIsometry.toContinuousLinearMap

lemma cubicThetaTorusCoefficientMap_apply (h : Eisenstein) (F : CubicThetaTorusL2) :
    cubicThetaTorusCoefficientMap h F=cubicThetaTorusCoefficient F h :=
  UnitAddTorus.mFourierBasis_repr F _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierSurjective
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Single Fourier modes are actual cusp slices. Their finite sums and
completeness prove that the Fourier isometry is onto the radial mode space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

local instance instMeasureSpaceUnitAddCircle_solutions_3_r27a815_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
def cubicThetaTorusBasis (h : Eisenstein) : CubicThetaTorusL2 :=
  UnitAddTorus.mFourierBasis (cubicThetaFourierIndex h)

lemma cubicThetaTorusCoefficient_basis (k h : Eisenstein) :
    cubicThetaTorusCoefficient (cubicThetaTorusBasis h) k=if k=h then 1 else 0 := by
  unfold cubicThetaTorusCoefficient cubicThetaTorusBasis
  rw [← UnitAddTorus.mFourierBasis_repr,HilbertBasis.repr_self]
  simp [lp.single_apply,Pi.single_apply,cubicThetaFourierIndex.injective.eq_iff]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered Eisenstein expansion on the original half-plane,
with the continued constant coefficient separated from the actual
nonzero arithmetic Fourier coefficients. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourierCoefficients_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun h : Eisenstein => cubicThetaFrequencyDirichlet h s*
      (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)) := by
  have h := (cubicThetaFrequency_heat_norm_summable hp hs).of_norm.prod_symm.prod
  apply h.congr
  intro n
  dsimp only [Prod.swap]
  rw [tsum_mul_right,tsum_mul_right]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyHolomorphic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphy of the actual arithmetic Fourier coefficients on their
initial half-plane, with a common bound independent of the frequency. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaFrequencyDirichlet_bound (h : Eisenstein) {s : ℂ} (hs : 2 < s.re) :
    ‖cubicThetaFrequencyDirichlet h s‖ ≤
      9*(∑' c : Eisenstein, (norm c)^(-(s.re-1))) := by
  have hsum := cubicThetaFrequencyTerm_norm_summable hs h
  calc
    _ ≤ ∑' c : Eisenstein, ‖cubicThetaFrequencyTerm s h c‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' c : Eisenstein, 9*(norm c)^(-(s.re-1)) :=
      hsum.tsum_le_tsum (cubicThetaFrequencyTerm_bound hs h)
        ((summable_eisenstein_norm_rpow (show 1 < s.re-1 by linarith)).mul_left 9)
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cusp decay of the actual Eisenstein series after its
constant Fourier mode has been removed. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFrequencyBound_nonneg (s : ℂ) : 0 ≤ cubicThetaFrequencyBound s := by
  unfold cubicThetaFrequencyBound
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _))

def cubicThetaNonzeroFrequencyTerm (p : ℂ × ℝ) (s : ℂ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaFrequencyDirichlet h s*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)

lemma cubicThetaNonzeroFrequencyTerm_bound {p : ℂ × ℝ} {s : ℂ} (hs : 2 < s.re)
    (h : Eisenstein) :
    ‖cubicThetaNonzeroFrequencyTerm p s h‖ ≤ cubicThetaFrequencyBound s*
      (if h=0 then 0 else ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t‖) := by
  by_cases hh : h=0
  · simp [cubicThetaNonzeroFrequencyTerm,hh]
  · simp only [cubicThetaNonzeroFrequencyTerm,ite_eq_right hh,norm_mul,Circle.norm_coe,mul_one]
    exact mul_le_mul (cubicThetaFrequencyDirichlet_bound h hs)
      (norm_integral_le_integral_norm _) (_root_.norm_nonneg _) (cubicThetaFrequencyBound_nonneg s)

lemma cubicThetaNonzeroFrequencyTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) : Summable (cubicThetaNonzeroFrequencyTerm p s) :=
  ((cubicThetaNonzeroHeat_mass_summable hp s).mul_left (cubicThetaFrequencyBound s)).of_norm_bounded
    (cubicThetaNonzeroFrequencyTerm_bound hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonconstant Eisenstein Fourier series is a continuous
function on its period torus. Its coefficients retain the arithmetic
Dirichlet series and heat integral, including the zero-mode exclusion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

def cubicThetaTorusRemainder (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein, cubicThetaNonzeroFrequencyTerm (0,v) s h • cubicThetaTorusFourier h

lemma cubicThetaTorusRemainder_summable {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun h : Eisenstein => cubicThetaNonzeroFrequencyTerm (0,v) s h • cubicThetaTorusFourier h) := by
  apply Summable.of_norm
  have he := (cubicThetaNonzeroFrequencyTerm_summable (p:=(0,v)) hv hs).norm
  simpa only [norm_smul,cubicThetaTorusFourier,UnitAddTorus.mFourier_norm,mul_one] using he

lemma cubicThetaNonzeroFrequencyTerm_phase (v : ℝ) (s : ℂ) (h : Eisenstein) (z : ℂ) :
    cubicThetaNonzeroFrequencyTerm (0,v) s h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)=
      cubicThetaNonzeroFrequencyTerm (z,v) s h := by
  by_cases hh : h=0
  · simp [cubicThetaNonzeroFrequencyTerm,hh]
  · simp [cubicThetaNonzeroFrequencyTerm,hh,tracePair]
    ring

lemma cubicThetaTorusRemainder_real {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaTorusRemainder v s (fun i => (x i:UnitAddCircle))=
      ∑' h : Eisenstein, cubicThetaNonzeroFrequencyTerm (cubicThetaPeriodCell x,v) s h := by
  have he := (ContinuousMap.evalCLM ℂ (fun i => (x i:UnitAddCircle))).map_tsum
    (cubicThetaTorusRemainder_summable hv hs)
  change cubicThetaTorusRemainder v s (fun i => (x i:UnitAddCircle))=_ at he
  rw [he]
  apply tsum_congr
  intro h
  change cubicThetaNonzeroFrequencyTerm (0,v) s h*
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=_
  rw [cubicThetaTorusFourier_actual,cubicThetaNonzeroFrequencyTerm_phase]

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_4
attribute [local instance] OAI.CubicFirstMoment.instIsProbabilityMeasureUnitAddCircleVolume_solutions
lemma cubicThetaTorusFourier_toLp (h : Eisenstein) :
    ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ (cubicThetaTorusFourier h)=cubicThetaTorusBasis h := by
  change UnitAddTorus.mFourierLp 2 (cubicThetaFourierIndex h)=
    UnitAddTorus.mFourierBasis (cubicThetaFourierIndex h)
  exact congrFun UnitAddTorus.coe_mFourierBasis.symm _

theorem cubicThetaTorusRemainder_coefficient {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    (k : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ (cubicThetaTorusRemainder v s)) k=
      cubicThetaNonzeroFrequencyTerm (0,v) s k := by
  let L := (cubicThetaTorusCoefficientMap k).comp (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ)
  rw [← cubicThetaTorusCoefficientMap_apply k]
  change L (cubicThetaTorusRemainder v s)=_
  rw [cubicThetaTorusRemainder,L.map_tsum (cubicThetaTorusRemainder_summable hv hs)]
  rw [tsum_eq_single k]
  · simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,smul_eq_mul,mul_one]
  · intro h hne
    simp only [L,ContinuousLinearMap.comp_apply,map_smul,cubicThetaTorusFourier_toLp,
      cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,
      ite_eq_right hne.symm,smul_zero]

theorem cubicThetaTorusRemainder_mean_zero {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ (cubicThetaTorusRemainder v s)) 0=0 := by
  rw [cubicThetaTorusRemainder_coefficient hv hs]
  simp [cubicThetaNonzeroFrequencyTerm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPeriodMeasure
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Jacobian of the level-three period cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPeriodEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  eisensteinRealCoords.trans (complexMulEquiv 3 (by norm_num))

lemma cubicThetaPeriodEquiv_apply (x : Fin 2 → ℝ) :
    cubicThetaPeriodEquiv x=cubicThetaPeriodCell x := rfl

lemma cubicThetaPeriodCoordinates_cell (x : Fin 2 → ℝ) :
    cubicThetaPeriodCoordinates (cubicThetaPeriodCell x)=x := by
  unfold cubicThetaPeriodCoordinates cubicThetaPeriodCell
  rw [mul_div_cancel_left₀ _ (by norm_num : (3:ℂ)≠0),ContinuousLinearEquiv.symm_apply_apply]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Fourier coefficient normalization for the physical cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaHorizontalCoefficientMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaHorizontalCoefficientProbability
lemma cubicThetaTorusCoefficient_integral (F : C(UnitAddTorus (Fin 2),ℂ))
    (h : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ F) h=
      ∫ t, star (cubicThetaTorusFourier h t)*F t := by
  unfold cubicThetaTorusCoefficient
  rw [UnitAddTorus.mFourierCoeff_toLp]
  simp only [UnitAddTorus.mFourierCoeff,UnitAddTorus.mFourier_neg,
    starRingEnd_apply,smul_eq_mul,cubicThetaTorusFourier]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaFourierIndex_zero : cubicThetaFourierIndex 0=0 := by
  apply (dualIntegerEquiv.trans coordinatesEquiv.toEquiv).injective
  unfold cubicThetaFourierIndex
  rw [Equiv.apply_symm_apply]
  change (0 : Eisenstein)=coordinatesEquiv (dualIntegerEquiv 0)
  have he : dualIntegerEquiv 0=0 := by ext i; fin_cases i <;> simp [dualIntegerEquiv]
  rw [he,map_zero]

lemma cubicThetaTorusFourier_zero : cubicThetaTorusFourier 0=1 := by
  rw [cubicThetaTorusFourier,cubicThetaFourierIndex_zero,UnitAddTorus.mFourier_zero]

def cubicThetaArithmeticTorus (v : ℝ) (s : ℂ) : C(UnitAddTorus (Fin 2),ℂ) :=
  (cubicThetaEisensteinConstantMode v s-(v:ℂ)^s) • cubicThetaTorusFourier 0+
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s) •
      cubicThetaTorusRemainder v s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint (D : CubicThetaArithmeticCover) :
    ContinuousConstSMul D.group CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

variable (D : CubicThetaArithmeticCover) (K : Subgroup cubicThetaPrincipalGroup)
  (hle : K≤D.group) [K.FiniteIndex]

lemma cubicThetaRelativeDomain_measurable : MeasurableSet (cubicThetaRelativeDomain D K) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image' D.measurable

def cubicThetaRelativeCover : CubicThetaArithmeticCover where
  group := K
  domain := cubicThetaRelativeDomain D K
  measurable := cubicThetaRelativeDomain_measurable D K
  unique := cubicThetaRelativeDomain_unique D K hle

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance instCommGroupCubicThetaPeriodGroup : CommGroup CubicThetaPeriodGroup := inferInstanceAs (CommGroup (Multiplicative Eisenstein))
instance instCountableCubicThetaPeriodGroup : Countable CubicThetaPeriodGroup := by
  change Countable Eisenstein
  exact coordinatesEquiv.symm.injective.countable

instance cubicThetaPeriodGroup_action : MulAction CubicThetaPeriodGroup ℂ where
  smul g z := z+3*((Multiplicative.toAdd g:Eisenstein):ℂ)
  one_smul z := by change z+3*((0:Eisenstein):ℂ)=z; simp
  mul_smul g h z := by
    change z+3*((Multiplicative.toAdd g+Multiplicative.toAdd h:Eisenstein):ℂ)=
      (z+3*((Multiplicative.toAdd h:Eisenstein):ℂ))+3*((Multiplicative.toAdd g:Eisenstein):ℂ)
    push_cast
    ring

instance cubicThetaPeriodGroup_continuous : ContinuousConstSMul CubicThetaPeriodGroup ℂ where
  continuous_const_smul g := by
    change Continuous (fun z : ℂ => z+3*((Multiplicative.toAdd g:Eisenstein):ℂ))
    fun_prop

instance cubicThetaPeriodGroup_measure : SMulInvariantMeasure CubicThetaPeriodGroup ℂ volume where
  measure_preimage_smul g A _ := by
    change volume ((fun z : ℂ => z+3*((Multiplicative.toAdd g:Eisenstein):ℂ)) ⁻¹' A)=volume A
    exact measure_preimage_add_right volume _ A

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance instCommGroupCubicThetaScaledPeriodGroup (_a : Eisenstein) : CommGroup (CubicThetaScaledPeriodGroup _a) :=
  inferInstanceAs (CommGroup (Multiplicative Eisenstein))
instance instCountableCubicThetaScaledPeriodGroup (_a : Eisenstein) : Countable (CubicThetaScaledPeriodGroup _a) := by
  change Countable Eisenstein
  exact coordinatesEquiv.symm.injective.countable

instance cubicThetaScaledPeriodGroup_action (a : Eisenstein) :
    MulAction (CubicThetaScaledPeriodGroup a) ℂ where
  smul g z := z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ)
  one_smul z := by change z+3*(a:ℂ)*((0:Eisenstein):ℂ)=z; simp
  mul_smul g h z := by
    change z+3*(a:ℂ)*((Multiplicative.toAdd g+Multiplicative.toAdd h:Eisenstein):ℂ)=
      (z+3*(a:ℂ)*((Multiplicative.toAdd h:Eisenstein):ℂ))+
        3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ)
    push_cast
    ring

instance cubicThetaScaledPeriodGroup_continuous (a : Eisenstein) :
    ContinuousConstSMul (CubicThetaScaledPeriodGroup a) ℂ where
  continuous_const_smul g := by
    change Continuous (fun z : ℂ => z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ))
    fun_prop

instance cubicThetaScaledPeriodGroup_measure (a : Eisenstein) :
    SMulInvariantMeasure (CubicThetaScaledPeriodGroup a) ℂ volume where
  measure_preimage_smul g A _ := by
    change volume ((fun z : ℂ => z+(3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ))) ⁻¹' A)=volume A
    exact measure_preimage_add_right volume _ A

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimePowerFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimePowerWeight_inflation {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (x : Residues (p^(n+1))) :
    cubicSymbol (p^(n+1)) (residueRepresentative (p^(n+1)) x)=
      (cubicResidueChar p hp
        (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x))^(n+1) := by
  rw [cubicThetaSymbol_prime_pow hp]
  congr 1
  have he : residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)) x=
      Ideal.Quotient.mk (modulus p) (residueRepresentative (p^(n+1)) x) := by
    exact (congrArg (residueReduction (dvd_pow_self p (Nat.succ_ne_zero n)))
      (residueRepresentative_spec (p^(n+1)) x)).symm
  rw [he,cubicResidueChar_mk,cubicSymbol_prime hp]

theorem cubicThetaLocalPrimePowerGauss_reduction {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero (n+1) (p^n*h)=
      (norm (p^n):ℂ)*∑' y : Residues p, (cubicResidueChar p hp y)^(n+1)*
        residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y) := by
  unfold cubicThetaLocalPrimePowerGauss
  simp_rw [cubicThetaPrimePowerWeight_inflation hp]
  exact residueFourier_inflation_of_eq (pow_ne_zero _ hp.2.ne_zero) hp.2.ne_zero
    (pow_ne_zero n hp.2.ne_zero) (pow_succ' p n)
    (dvd_pow_self p (Nat.succ_ne_zero n))
    (fun y : Residues p => (cubicResidueChar p hp y)^(n+1)) h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine zero-frequency observation retains the explicit
arithmetic scattering coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaZeroObservableMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaZeroObservableProbability
lemma cubicThetaArithmeticTorus_zero {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticTorus v s)) 0=
      cubicThetaEisensteinConstantMode v s-(v:ℂ)^s := by
  let L := (cubicThetaTorusCoefficientMap 0).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [← cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaArithmeticTorus v s)=_
  rw [cubicThetaArithmeticTorus,map_add,map_smul,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusFourier_toLp,
    cubicThetaTorusCoefficientMap_apply,cubicThetaTorusCoefficient_basis,ite_true, if_true,
    cubicThetaTorusRemainder_mean_zero hv hs,smul_eq_mul,mul_one,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeEulerStep
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact first local Euler step for a frequency prime to p. The two
remaining series retain their actual cubic twists on the prime-free rows. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeFreeTerm (p : Eisenstein) (s : ℂ) (h : Eisenstein) (j : ℕ)
    (d : CubicThetaPrimeFreeDenominator p) : ℂ :=
  (cubicSymbol p d.val)^j*cubicThetaEisensteinGaussCoefficient d.val h*(norm d.val:ℂ)^(-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReductionRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows that triangularize the three nonzero valuation
branches of the cubed-prime lower chart. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReduction_phase {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))=
      (cubicSymbol p (3*n))^(3-k.val) := by
  rw [cubicThetaKubotaValue_bottomRow]
  change star (star (cubicSymbol ((cubicThetaPrimeCubeReduction hp k n hn).val 1 1)
    ((cubicThetaPrimeCubeReduction hp k n hn).val 1 0)))=_
  rw [cubicThetaPrimeCubeReduction_c,cubicThetaPrimeCubeReduction_d,
    star_star,cubicThetaSymbol_prime_pow hp]
  rw [show -3*n= -(3*n) by ring,cubicSymbol_neg hp.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReductionPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic phase of each triangularized branch is the corresponding
power of the numerator character of its upper-right entry. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeReduction_phase_top {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))=
      (cubicSymbol p ((cubicThetaPrimeCubeReduction hp k n hn).val 0 1))^k.val := by
  let c := cubicSymbol p (3*n)
  let d := cubicSymbol p ((cubicThetaPrimeCubeReduction hp k n hn).val 0 1)
  have hcd : c*d=1 := by
    dsimp only [c,d]
    rw [←cubicSymbol_mul_upper hp.1,cubicSymbol_congr
      (residue_eq_of_dvd_sub (cubicThetaPrimeCubeReduction_top_congruence hp k n hn))]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  have hc3 : c^3=1 := cubicSymbol_cube_of_isCoprime hp.1 _
    ((primary_coprime_three hp.1).mul_right (hp.2.coprime_iff_not_dvd.mpr hn))
  have hd : d=c^2 := by linear_combination c^2*hcd-d*hc3
  have hc : c=d^2 := by
    rw [hd]
    calc
      c = c*c^3 := by rw [hc3,mul_one]
      _ = (c^2)^2 := by ring
  rw [cubicThetaPrimeCubeReduction_phase hp]
  change c^(3-k.val)=d^k.val
  fin_cases k
  · simpa only [pow_zero] using hc3
  · simpa only [pow_one] using hd.symm
  · simpa only [Nat.reduceSub,pow_one] using hc

theorem cubicThetaPrimeCubeReduction_section {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalLower (p^k.val*n) • x))=
      (cubicSymbol p ((cubicThetaPrimeCubeReduction hp k n hn).val 0 1))^k.val*
        F.val (cubicThetaPrimeCubeReducedMatrix hp k n hn • x) := by
  rw [←cubicThetaPrimeCubeReduction_phase_top hp]
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  rw [cubicThetaPrimeCubeReducedMatrix,mul_smul,mul_smul]
  change _=star (cubicThetaKubotaValue (cubicThetaPrimeCubeReduction hp k n hn))*
    F.val (cubicThetaPrimeCubeReduction hp k n hn •
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalLower (p^k.val*n) • x)))
  rw [F.property,←mul_assoc,hu,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBranchCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized prime-power coordinates of each nonzero valuation
branch in the actual cubed-prime trace. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeBranch_section {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalLower (p^k.val*n) • x))=
      (cubicSymbol p (3*cubicThetaPrimeCubeReductionTranslation hp k n hn))^k.val*
        F.val (cubicThetaPrimeCubeBranchPoint hp k
          (cubicThetaPrimeCubeReductionTranslation hp k n hn) x) := by
  rw [cubicThetaPrimeCubeReduction_section hp]
  have he : cubicThetaPrimeCubeReducedMatrix hp k n hn • x=
      cubicThetaPrimeCubeBranchPoint hp k (cubicThetaPrimeCubeReductionTranslation hp k n hn) x := by
    apply Subtype.ext
    change cubicThetaMobius _ x.val=_
    rw [cubicThetaPrimeCubeReducedMatrix_coordinates,
      ←cubicThetaPrimeCubeReductionTranslation_three hp k n hn]
    rfl
  rw [he,cubicThetaPrimeCubeReductionTranslation_three]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBranchPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each triangular branch depends only on its residue parameter, with
the period-three automorphy and the cubic phase both retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeBranch_section_congr {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b c : Eisenstein) (hbc : p^(3-k.val)∣b-c)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    F.val (cubicThetaPrimeCubeBranchPoint hp k b x)=
      F.val (cubicThetaPrimeCubeBranchPoint hp k c x) := by
  obtain ⟨m,hm⟩ := hbc
  have hb : b=c+p^(3-k.val)*m := by linear_combination hm
  rw [hb,cubicThetaPrimeCubeBranchPoint_translate,F.property,
    cubicThetaPrincipalTranslation_value,one_mul]

lemma cubicThetaPrimeCubeBranch_term_congr {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b c : Eisenstein) (hbc : p^(3-k.val)∣b-c)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicSymbol p (3*b))^k.val*F.val (cubicThetaPrimeCubeBranchPoint hp k b x)=
      (cubicSymbol p (3*c))^k.val*F.val (cubicThetaPrimeCubeBranchPoint hp k c x) := by
  have hd : p∣3*b-3*c := by
    rw [←mul_sub]
    exact dvd_mul_of_dvd_right
      ((dvd_pow_self p (by have := k.isLt; omega)).trans hbc) 3
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hd),
    cubicThetaPrimeCubeBranch_section_congr hp k b c hbc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaSectionHorizontal (F : CubicThetaSection) (v : ℝ) (hv : 0<v) : C(ℂ,ℂ) :=
  ⟨fun z => F.val (cubicThetaHorizontalPoint v hv z),
    F.val.continuous.comp (cubicThetaHorizontalPoint_continuous v hv)⟩

lemma cubicThetaSectionHorizontal_periodic (F : CubicThetaSection) (v : ℝ) (hv : 0<v)
    (w : Eisenstein) (z : ℂ) :
    cubicThetaSectionHorizontal F v hv (z+3*(w:ℂ))=cubicThetaSectionHorizontal F v hv z := by
  have hp : cubicThetaHorizontalPoint v hv (z+3*(w:ℂ))=
      cubicThetaPrincipalTranslation w • cubicThetaHorizontalPoint v hv z := by
    apply Subtype.ext
    change (z+3*(w:ℂ),v)=cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) (z,v)
    rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
    push_cast
    rfl
  change F.val (cubicThetaHorizontalPoint v hv (z+3*(w:ℂ)))=_
  rw [hp,F.property,cubicThetaPrincipalTranslation_value,one_mul]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegralQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral Mobius changes of cusp descend to the actual principal
quotient and preserve its constructed hyperbolic measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaIntegralQuotientMap (δ : SL(2,Eisenstein)) :
    CubicThetaQuotient → CubicThetaQuotient :=
  Quotient.map (fun p => δ • p) (by
    intro p q hpq
    obtain ⟨g,hg⟩ := hpq
    refine ⟨cubicThetaPrincipalConjugate δ⁻¹ g,?_⟩
    change (((δ⁻¹)⁻¹*g.val*δ⁻¹):SL(2,Eisenstein)) • (δ • q)=δ • p
    rw [inv_inv]
    simp only [←mul_smul,mul_assoc,inv_mul_cancel,mul_one]
    rw [mul_smul]
    exact congrArg (fun r => δ • r) hg)

lemma cubicThetaIntegralQuotientMap_apply (δ : SL(2,Eisenstein)) (p : CubicThetaPoint) :
    cubicThetaIntegralQuotientMap δ (cubicThetaQuotientMap p)=cubicThetaQuotientMap (δ • p) := rfl

lemma cubicThetaIntegralQuotientMap_comp (δ ε : SL(2,Eisenstein)) (q : CubicThetaQuotient) :
    cubicThetaIntegralQuotientMap δ (cubicThetaIntegralQuotientMap ε q)=
      cubicThetaIntegralQuotientMap (δ*ε) q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change cubicThetaQuotientMap (δ • (ε • p))=cubicThetaQuotientMap ((δ*ε) • p)
    rw [mul_smul]

lemma cubicThetaIntegralQuotientMap_one (q : CubicThetaQuotient) :
    cubicThetaIntegralQuotientMap 1 q=q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change cubicThetaQuotientMap ((1:SL(2,Eisenstein)) • p)=cubicThetaQuotientMap p
    rw [one_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCharacterNontrivial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nontriviality of the actual prime-level character. A nontrivial
residue-field value is lifted to a primary bottom row and completed in
the original level-three group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrime_primary_nontrivial {p : Eisenstein} (hp : primaryPrime p) :
    ∃ d : Eisenstein, primary d ∧ IsCoprime p d ∧ cubicSymbol p d≠1 := by
  obtain ⟨x,hx⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  let v := residueRepresentative p (x : Residues p)
  have hv : IsCoprime p v := by
    apply isCoprime_of_residue_isUnit
    simpa only [v,residueRepresentative_spec] using x.isUnit
  obtain ⟨d,hd,hdp⟩ := residue_crt_one (primary_coprime_three hp.1) v
  refine ⟨d,hdp,isCoprime_of_residue_congr hd hv,?_⟩
  intro he
  apply hx
  have heq : cubicSymbol p v=cubicResidueChar p hp (x : Residues p) := by
    rw [cubicSymbol_prime hp]
    exact (cubicResidueChar_mk p hp v).symm.trans
      (congrArg (cubicResidueChar p hp) (residueRepresentative_spec p (x : Residues p)))
  rw [←heq,←cubicSymbol_congr (residue_eq_of_dvd_sub hd),he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAtkinConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime Atkin involution on the actual arithmetic subgroup. Its
cubic twist disappears on the kernel of the diagonal character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeAtkinConjugate_diagonal {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    (cubicThetaPrimeAtkinConjugate hp g).val.val 0 0=g.val.val 1 1 := by
  exact (cubicThetaInversionConjugate_entries (cubicThetaPrimeConjugate hp.1 g)).1

lemma cubicThetaPrimeAtkinConjugate_character_product {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeIwahoriCharacter p hp g*
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeAtkinConjugate hp g)=1 := by
  change cubicSymbol p (g.val.val 0 0)*
    cubicSymbol p ((cubicThetaPrimeAtkinConjugate hp g).val.val 0 0)=1
  rw [cubicThetaPrimeAtkinConjugate_diagonal,←cubicSymbol_mul_upper hp.1]
  have hd : p∣g.val.val 0 0*g.val.val 1 1-1 := by
    rw [show g.val.val 0 0*g.val.val 1 1-1=g.val.val 0 1*g.val.val 1 0 by
      linear_combination cubicThetaPrincipalGroup_det g.val]
    exact dvd_mul_of_dvd_right g.property _
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hd)]
  simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0

def cubicThetaPrimeAtkinKernel {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCharacterKernel hp) : cubicThetaPrimeCharacterKernel hp :=
  ⟨cubicThetaPrimeAtkinConjugate hp g.val,by
    have he := cubicThetaPrimeAtkinConjugate_character_product hp g.val
    have hg : cubicThetaPrimeIwahoriCharacter p hp g.val=1 := g.property
    rw [hg,one_mul] at he
    exact he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionMass
attribute [-instance] _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric inversion on the actual automorphic mass completion. -/
noncomputable section
namespace CubicFirstMoment

local instance inversionMass_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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


theorem cubicThetaRadialProfileSeries_compact_sum (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K,
      cubicThetaRadialProfileSeries p W=∑ r∈S, cubicThetaRadialProfileTerm r p W := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact mul_eq_zero_of_right _ (hW _ (hS p hp r hr).le)

lemma cubicThetaRadialProfileSeries_continuousOn (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) :
    ContinuousOn (fun p => cubicThetaRadialProfileSeries p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaRadialProfileSeries_compact_sum W hW hK hKpos
  have he : (fun q => cubicThetaRadialProfileSeries q W) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContinuousAt (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (continuousAt_const.mul (W.continuous.continuousAt.comp
        (r.height_contDiffAt hp).continuousAt)).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

def cubicThetaRadialProfileSection (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaRadialProfileSeries p.val W,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaRadialProfileSeries_continuousOn W hW).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaRadialProfileSeries_automorphy g p.property W⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.instMeasurableSpace
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

lemma cubicThetaRadialProfileSeries_contDiffOn (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaRadialProfileSeries p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaRadialProfileSeries_compact_sum W hW hK hKpos
  have he : (fun q => cubicThetaRadialProfileSeries q W) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) p :=
    ContDiffAt.sum (fun r _ => cubicThetaRadialProfileTerm_contDiffAt W hsm r hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

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

lemma cubicThetaRadialProfileTerm_equation (W J : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (r : CubicThetaBottomRow) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint a b t) W) x y v=
      lam*cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) W-
        cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) J := by
  have hf : ContDiffAt ℝ 2 (W : ℝ → ℂ) (cubicThetaRowHeightCoordinates r x y v) :=
    hsm.contDiffAt.of_le (by norm_num)
  change cubicThetaHyperbolicOperator
    (fun a b t => star r.phase*W (cubicThetaRowHeightCoordinates r a b t)) x y v=_
  rw [cubicThetaHyperbolicOperator_const_mul,cubicThetaRowHeight_operator r x y hv hf]
  have hh : 0 < cubicThetaRowHeightCoordinates r x y v := r.height_pos hv
  have he : cubicThetaHyperbolicOperator (fun _ _ t => W t) 0 0
      (cubicThetaRowHeightCoordinates r x y v)=
      cubicThetaRadialEuler W (cubicThetaRowHeightCoordinates r x y v) := by
    simp only [cubicThetaHyperbolicOperator,cubicThetaRadialEuler,
      deriv_const',deriv_const,zero_add]
  rw [he,hEq _ hh]
  unfold cubicThetaRadialProfileTerm cubicThetaRowHeightCoordinates
  ring

lemma cubicThetaRadialProfileFinite_equation (W J : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (S : Finset CubicThetaBottomRow) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => ∑ r∈S, cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint a b t) W) x y v=
      lam*(∑ r∈S, cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) W)-
        ∑ r∈S, cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint x y v) J := by
  have hcoords := fun r => radial_coordinate_smooth W hsm r x y hv
  rw [cubicThetaHyperbolicOperator_finite S
    (fun r a b t => cubicThetaRadialProfileTerm r (cubicThetaCartesianPoint a b t) W) x y v
    (fun r _ => (hcoords r).1) (fun r _ => (hcoords r).2.1) (fun r _ => (hcoords r).2.2)]
  simp_rw [cubicThetaRadialProfileTerm_equation W J hsm lam hEq _ x y hv]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]

theorem cubicThetaRadialProfileSeries_equation (W J : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hJ : ∀ v≤(1:ℝ), J v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaRadialProfileSeries (cubicThetaCartesianPoint a b t) W) x y v=
      lam*cubicThetaRadialProfileSeries (cubicThetaCartesianPoint x y v) W-
        cubicThetaRadialProfileSeries (cubicThetaCartesianPoint x y v) J := by
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood
    (p:=cubicThetaCartesianPoint x y v) hv
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hKpos
  have hsum (U : C_c(ℝ,ℂ)) (hU : ∀ v≤(1:ℝ), U v=0) (p) (hp : p∈K) :
      cubicThetaRadialProfileSeries p U=∑ r∈S, cubicThetaRadialProfileTerm r p U := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (hU _ (hS p hp r hr).le)
  have he : (fun p => cubicThetaRadialProfileSeries p W)=ᶠ[𝓝 (cubicThetaCartesianPoint x y v)]
      (fun p => ∑ r∈S, cubicThetaRadialProfileTerm r p W) := by
    filter_upwards [hKn] with p hp
    exact hsum W hW p hp
  have hpK : cubicThetaCartesianPoint x y v∈K := mem_of_mem_nhds hKn
  rw [cubicThetaHyperbolicOperator_germ x y v he,
    cubicThetaRadialProfileFinite_equation W J hsm lam hEq S x y hv,
    ←hsum W hW _ hpK,←hsum J hJ _ hpK]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeUnitBranch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of each nonzero valuation branch of the actual
trace into a finite cubic-character-weighted translation sum. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeUnitBranch {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^(3-k.val)))ˣ,
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalLower (p^k.val*
          residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) • x)))=
      ∑' v : (Residues (p^(3-k.val)))ˣ,
        (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))))^k.val*
          F.val (cubicThetaPrimeCubeBranchPoint hp k
            (residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))) x) := by
  let T := fun v : (Residues (p^(3-k.val)))ˣ =>
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))))^k.val*
      F.val (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (v : Residues (p^(3-k.val)))) x)
  calc
    _ = ∑' u : (Residues (p^(3-k.val)))ˣ, T (cubicThetaPrimeCubeUnitPermutation hp k u) := by
      apply tsum_congr
      intro u
      let n := residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))
      have hn := cubicThetaPrimeCubeUnitRepresentative_not_dvd hp k u
      rw [cubicThetaPrimeCubeBranch_section hp k n hn]
      apply cubicThetaPrimeCubeBranch_term_congr hp
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq.mp
      exact (cubicThetaPrimeCubeUnitTranslation_residue hp k u).trans
        (residueRepresentative_spec _ _).symm
    _ = _ := (cubicThetaPrimeCubeUnitPermutation hp k).tsum_eq T

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeLowerValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower-chart value is a genuine function modulo p^3. Its scaled
versions descend to the smaller residue rings used in the valuation split. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeLowerValue {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (m : Eisenstein) : ℂ :=
  F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (cubicThetaPrincipalLower m • x))

lemma cubicThetaPrimeCubeLowerValue_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeLowerValue hp F x 0=
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x) := by
  simp [cubicThetaPrimeCubeLowerValue,cubicThetaPrincipalLower_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeFormula
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal four-branch cubed-prime Hecke formula for actual cubic
automorphic sections, with the two intermediate cubic-character sums. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeBranchSum {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (x : CubicThetaPoint) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      F.val (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) x)

def cubicThetaPrimeCubeFullBottomSum {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) : ℂ :=
  ∑' r : Residues (p^3), F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r) x)

lemma cubicThetaPrimeCubeBranchSum_lower {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^(3-k.val)))ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (p^k.val*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))=
        cubicThetaPrimeCubeBranchSum hp k F x :=
  cubicThetaPrimeCubeUnitBranch hp k F x

lemma cubicThetaPrimeCubeBranchSum_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^3))ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (residueRepresentative (p^3) (u : Residues (p^3))))=
        cubicThetaPrimeCubeBranchSum hp 0 F x := by
  simpa only [cubicThetaPrimeCubeLowerValue,cubicThetaPrimeCubeBranchSum,
    Fin.val_zero,Nat.sub_zero,pow_zero,one_mul] using cubicThetaPrimeCubeUnitBranch hp 0 F x

lemma cubicThetaPrimeCubeBranchSum_one {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues (p^2))ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (p*residueRepresentative (p^2) (u : Residues (p^2))))=
        cubicThetaPrimeCubeBranchSum hp 1 F x := by
  simpa only [cubicThetaPrimeCubeLowerValue,cubicThetaPrimeCubeBranchSum,
    Fin.val_one,Nat.reduceSub,pow_one] using cubicThetaPrimeCubeUnitBranch hp 1 F x

lemma cubicThetaPrimeCubeBranchSum_two {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' u : (Residues p)ˣ,cubicThetaPrimeCubeLowerValue hp F x
      (p^2*residueRepresentative p (u : Residues p)))=
        cubicThetaPrimeCubeBranchSum hp (⟨2,by decide⟩ : Fin 3) F x := by
  calc
    _ = ∑' u : (Residues (p^1))ˣ,cubicThetaPrimeCubeLowerValue hp F x
        (p^2*residueRepresentative (p^1) (u : Residues (p^1))) := by
      exact (congrArg (fun q : Eisenstein => ∑' u : (Residues q)ˣ,
        cubicThetaPrimeCubeLowerValue hp F x (p^2*residueRepresentative q (u : Residues q)))
          (pow_one p)).symm
    _ = _ := by
      with_reducible_and_instances exact
        cubicThetaPrimeCubeBranchSum_lower hp (⟨2,by decide⟩ : Fin 3) F x

lemma cubicThetaPrimeCubeBottomValue_split {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFullBottomSum hp F x=cubicThetaPrimeCubeBranchSum hp 0 F x+
      ∑' r : cubicThetaPrimeCubeUpperParameter p,
        F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r.val) x) := by
  simpa only [cubicThetaPrimeCubeFullBottomSum,cubicThetaPrimeCubeBranchSum,
    Fin.val_zero,Nat.sub_zero,pow_zero,one_mul] using
      cubicThetaPrimeCubeResidueComplement_sum hp
        (fun r => F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r) x))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second character branch is an integral horizontal dilation.
Its constant mode can therefore be reduced by the actual cell integral. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSecondBranch_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    F.val (cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3) b
      (cubicThetaHorizontalPoint v hv z))=
    cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
      (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)
      ((p:ℂ)*z+3*(b:ℂ)/(p:ℂ)) := by
  rw [cubicThetaPrimeCubeSecondBranch_point]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstBranchMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeFirstBranch_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    F.val (cubicThetaPrimeCubeBranchPoint hp 1 b (cubicThetaHorizontalPoint v hv z))=
    cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖)
      (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))
      (z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2) := by
  rw [cubicThetaPrimeCubeFirstBranch_point]
  rfl

lemma cubicThetaPrimeCubeFirstBranch_periodization {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z)=
      cubicThetaPrimeCubeFirstPeriodization p
        (cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖)
          (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))) z := by
  rw [cubicThetaPrimeCubeFirstPeriodization_units hp]
  unfold cubicThetaPrimeCubeUnitFunctionSum
  apply tsum_congr
  intro u
  simp only [Fin.val_one,pow_one,cubicThetaPrimeCubeFirstTerm]
  rw [cubicThetaPrimeCubeFirstBranch_section]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBottomMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeBottom_periodization {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPeriodization (p^3)
        (cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
          (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))) z := by
  unfold cubicThetaPrimeCubeBottomFunctionSum cubicThetaHorizontalPeriodization
  apply tsum_congr
  intro r
  rw [cubicThetaPrimeCubeBottomBranch_point]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-support identities for the actual compact radial Poincaré sum. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfileSeries_sub (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hV : ∀ v≤(1:ℝ), V v=0)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaRadialProfileSeries p (W-V)=
      cubicThetaRadialProfileSeries p W-cubicThetaRadialProfileSeries p V := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact (isCompact_singleton (x:=p))
    (by intro q hq; simpa only [mem_singleton_iff.mp hq] using hp)
  have hsum (U : C_c(ℝ,ℂ)) (hU : ∀ v≤(1:ℝ),U v=0) :
      cubicThetaRadialProfileSeries p U=∑ r∈S,cubicThetaRadialProfileTerm r p U := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (hU _ (hS p (mem_singleton p) r hr).le)
  rw [hsum (W-V) (by intro v hv; change W v-V v=0; rw [hW v hv,hV v hv,sub_self]),
    hsum W hW,hsum V hV,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  change star r.phase*(W (r.height p)-V (r.height p))=_
  exact mul_sub _ _ _

lemma cubicThetaRadialProfileSection_sub (W V : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hV : ∀ v≤(1:ℝ), V v=0) :
    cubicThetaRadialProfileSection (W-V)
        (by intro v hv; change W v-V v=0; rw [hW v hv,hV v hv,sub_self])=
      cubicThetaRadialProfileSection W hW-cubicThetaRadialProfileSection V hV := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  exact cubicThetaRadialProfileSeries_sub W V hW hV p.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindowKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual theta kernel can be paired with the incoming forcing in an
arbitrarily high compact annulus. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaLongWindowDefectSection (H : ℝ) (hH : 2≤H) (s : ℂ) : CubicThetaSection :=
  cubicThetaRadialProfileSection (cubicThetaLongWindowDefect H hH s)
    (cubicThetaLongWindowDefect_low H hH s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReciprocalNormalizer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral normalizer used to compare the cubed-prime correspondence
with its reciprocal. Its lower-left entry vanishes modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeIwahori_integral_conjugate (q : Eisenstein)
    (δ : SL(2,Eisenstein)) (hδ : q∣δ.val 1 0)
    (g : cubicThetaPrimeIwahori q) :
    cubicThetaPrincipalConjugate δ g.val∈cubicThetaPrimeIwahori q := by
  change q∣(δ⁻¹*g.val.val*δ) 1 0
  have he : (δ⁻¹*g.val.val*δ) 1 0=
      (δ.val 0 0)^2*g.val.val 1 0-(δ.val 1 0)^2*g.val.val 0 1+
        δ.val 0 0*δ.val 1 0*(g.val.val 1 1-g.val.val 0 0) := by
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    ring
  rw [he]
  have hc : q∣(δ.val 1 0)^2 := by simpa only [pow_two] using dvd_mul_of_dvd_left hδ (δ.val 1 0)
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_right g.property _) (dvd_mul_of_dvd_left hc _))
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeRootElement_neg {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeRootElement hp (-x)=(cubicThetaPrimeRootElement hp x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←cubicThetaPrimeRootElement_add,neg_add_cancel,cubicThetaPrimeRootElement_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootAutomorphism
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootConjugate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaPrimeRootConjugate hp (x+y) g=
      cubicThetaPrimeRootConjugate hp x (cubicThetaPrimeRootConjugate hp y g) := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeRootConjugate_complex,cubicThetaPrimeRootElement_add,mul_inv_rev]
  group

def cubicThetaPrimeRootAutomorphism {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeRootSubgroup p ≃* cubicThetaPrimeRootSubgroup p where
  toFun := cubicThetaPrimeRootConjugate hp x
  invFun := cubicThetaPrimeRootConjugate hp (-x)
  left_inv g := by
    rw [←cubicThetaPrimeRootConjugate_add,neg_add_cancel,cubicThetaPrimeRootConjugate_zero]
  right_inv g := by
    rw [←cubicThetaPrimeRootConjugate_add,add_neg_cancel,cubicThetaPrimeRootConjugate_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply cubicThetaPrincipalComplex_injective
    change cubicThetaPrincipalComplex (cubicThetaPrimeRootConjugate hp x (g*h)).val=
      cubicThetaPrincipalComplex ((cubicThetaPrimeRootConjugate hp x g).val*
        (cubicThetaPrimeRootConjugate hp x h).val)
    simp only [cubicThetaPrimeRootConjugate_complex,map_mul,Subgroup.coe_mul]
    group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance cubicThetaPrimeRootCoverGroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeRootCoverGroup hp).FiniteIndex :=
  cubicThetaPrimeRootSubgroup_finiteIndex hp.2.ne_zero

instance cubicThetaPrimeRootCoverGroup_continuous {p : Eisenstein} (hp : primaryPrime p) :
    ContinuousConstSMul (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

lemma cubicThetaPrimeRootCoverMap_open {p : Eisenstein} (hp : primaryPrime p) :
    IsOpenQuotientMap (cubicThetaPrimeRootCoverMap hp) :=
  MulAction.isOpenQuotientMap_quotientMk

lemma cubicThetaPrimeRootCover_covering {p : Eisenstein} (hp : primaryPrime p) :
    IsQuotientCoveringMap (cubicThetaPrimeRootCoverMap hp) (cubicThetaPrimeRootCoverGroup hp) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

lemma cubicThetaPrimeRootTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeRootCoverGroup hp) (cubicThetaPrimeRootTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeRootCoverGroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeRootTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeRootTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeRootTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

instance cubicThetaPrimeRootCover_borelSpace {p : Eisenstein} (hp : primaryPrime p) :
    BorelSpace (CubicThetaPrimeRootCover hp) := ⟨rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independence of the fractional-root cover measure from the finite translated
fundamental domain used in its construction. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootCoverMeasure_apply {p : Eisenstein} (hp : primaryPrime p)
    {S : Set (CubicThetaPrimeRootCover hp)} (hS : MeasurableSet S) :
    cubicThetaPrimeRootCoverMeasure hp S=
      cubicThetaPointMeasure ((cubicThetaPrimeRootCoverMap hp) ⁻¹' S ∩ cubicThetaPrimeRootCoverDomain hp) := by
  rw [cubicThetaPrimeRootCoverMeasure,Measure.map_apply
    (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable hS,
    Measure.restrict_apply (hS.preimage (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverAction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional roots act on the actual finite arithmetic cover. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverHomeomorph {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : CubicThetaPrimeRootCover hp ≃ₜ CubicThetaPrimeRootCover hp where
  toFun := cubicThetaPrimeRootCoverTranslate hp x
  invFun := cubicThetaPrimeRootCoverTranslate hp (-x)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootElement hp (-x) • (cubicThetaPrimeRootElement hp x • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootElement_neg,inv_smul_smul]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootElement hp x • (cubicThetaPrimeRootElement hp (-x) • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootElement_neg,smul_inv_smul]
  continuous_toFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootElement hp x))
  continuous_invFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootElement hp (-x)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fractional roots preserve hyperbolic measure on their
finite arithmetic cover, by transport of the proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRoot_map_restrict {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun y : CubicThetaPoint =>
      cubicThetaPrimeRootElement hp x • y)=
      cubicThetaPointMeasure.restrict ((fun y : CubicThetaPoint =>
        cubicThetaPrimeRootElement hp x • y) '' S) := by
  have hImage := (Homeomorph.smul (cubicThetaPrimeRootElement hp x)).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) '' S) at hImage
  have he := Measure.restrict_map (measurable_const_smul (cubicThetaPrimeRootElement hp x))
    hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul (cubicThetaPrimeRootElement hp x) cubicThetaPointMeasure).map_eq] at he
  have hpre : (fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) ⁻¹'
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective (cubicThetaPrimeRootElement hp x))
  rw [hpre] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSectionNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeRootSectionTranslate_norm {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionTranslate hp x F) q=
      cubicThetaPrimeRootSectionNorm hp F (cubicThetaPrimeRootCoverTranslate hp x q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootHorizontal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual root average selects exactly the Fourier frequencies
divisible by the prime, on every positive-height horizontal slice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeRootHorizontal {p : Eisenstein} (F : cubicThetaPrimeRootSections p)
    (v : ℝ) (hv : 0<v) : C(ℂ,ℂ) :=
  ⟨fun z => F.val (cubicThetaHorizontalPoint v hv z),
    F.val.continuous.comp (cubicThetaHorizontalPoint_continuous v hv)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootDiagonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root subgroup has central diagonal reduction modulo the prime.
Its diagonal cubic character is therefore trivial. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootDilation_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeRootDilationIwahori hp g).val=
      cubicThetaKubotaValue g.val := by
  have he := cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeRootIwahori g)
  change cubicThetaKubotaValue g.val=cubicSymbol p (g.val.val 0 0)*
    cubicThetaKubotaValue (cubicThetaPrimeRootDilationIwahori hp g).val at he
  rw [cubicThetaPrimeRoot_diagonal_character hp g,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeRootWeylConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    ((cubicThetaPrimeRootWeylConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^2);-p^2*g.val.val 0 1,g.val.val 0 0] :=
  cubicThetaPrimeRootWeyl_matrix hp g

theorem cubicThetaPrimeRootWeylConjugate_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeRootWeylConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeRootWeylConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -(p^2*g.val.val 0 1)=p^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeRoot_lower_division hp g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeRootWeylConjugate_matrix hp g)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugated inversion preserves the root-cover measure
and the square norm of its sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_map_restrict {p : Eisenstein} (hp : primaryPrime p)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun y : CubicThetaPoint =>
      cubicThetaPrimeRootWeylElement hp • y)=
      cubicThetaPointMeasure.restrict ((fun y : CubicThetaPoint =>
        cubicThetaPrimeRootWeylElement hp • y) '' S) := by
  have hImage := (Homeomorph.smul (cubicThetaPrimeRootWeylElement hp)).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) '' S) at hImage
  have he := Measure.restrict_map (measurable_const_smul (cubicThetaPrimeRootWeylElement hp))
    hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul (cubicThetaPrimeRootWeylElement hp) cubicThetaPointMeasure).map_eq] at he
  have hpre : (fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) ⁻¹'
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective (cubicThetaPrimeRootWeylElement hp))
  rw [hpre] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhatMatrix
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integral Bruhat representative for two inverse nonzero root
parameters. Its multiplier is the literal cubic residue symbol. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootBruhat_division {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    p*((1-9*x*y)/p)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' hp.2.ne_zero
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaPrimeRootBruhatMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![p,3*x;-3*y,(1-9*x*y)/p],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaPrimeRootBruhat_division hp x y hxy⟩

lemma cubicThetaPrimeRootBruhatMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    cubicThetaPrimeRootBruhatMatrix hp x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary p ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/p)
  refine ⟨hp.1,⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/p-1
  apply (primary_coprime_three hp.1).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaPrimeRootBruhat_division hp x y hxy]
  convert dvd_sub (dvd_neg.mpr hp.1) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  all_goals try with_reducible_and_instances rfl
  ring

def cubicThetaPrimeRootBruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeRootBruhatMatrix hp x y hxy,cubicThetaPrimeRootBruhatMatrix_mem hp x y hxy⟩

lemma cubicThetaPrimeRootBruhat_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeRootBruhat hp x y hxy)=cubicSymbol p (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol p (-3*y)=cubicSymbol p (3*y)
  rw [neg_mul,cubicSymbol_neg hp.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhatResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice-independent nonzero Bruhat branches, indexed by the actual
prime residue units. The cubic multiplier is the original residue character. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootReciprocal (p : Eisenstein) (r : Residues p) : Residues p :=
  Ring.inverse (Ideal.Quotient.mk (modulus p) 9*r)

lemma cubicThetaPrimeRoot_nine_unit {p : Eisenstein} (hp : primaryPrime p) :
    IsUnit (Ideal.Quotient.mk (modulus p) 9) := by
  have hc : IsCoprime p (9:Eisenstein) := by
    convert (primary_coprime_three hp.1).pow_right (n:=2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hc
  rw [←hu]
  exact u.isUnit

lemma cubicThetaPrimeRootReciprocal_pair {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) :
    p∣9*residueRepresentative p (cubicThetaPrimeRootReciprocal p r)*residueRepresentative p r-1 := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (modulus p)
    (9*residueRepresentative p (cubicThetaPrimeRootReciprocal p r)*residueRepresentative p r-1)=0
  rw [map_sub,map_one,sub_eq_zero]
  simp only [map_mul,residueRepresentative_spec,cubicThetaPrimeRootReciprocal]
  calc
    _ = Ring.inverse (Ideal.Quotient.mk (modulus p) 9*r)*
        (Ideal.Quotient.mk (modulus p) 9*r) := by ring
    _ = 1 := Ring.inverse_mul_cancel _ ((cubicThetaPrimeRoot_nine_unit hp).mul hr)

lemma cubicThetaPrimeRootBruhat_residue_character {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) :
    cubicSymbol p (3*residueRepresentative p r)=cubicSymbol p 3*cubicResidueChar p hp r := by
  rw [cubicSymbol_mul_upper hp.1]
  congr 1
  rw [cubicSymbol_prime hp,←cubicResidueChar_mk p hp,residueRepresentative_spec]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-scale unit branch has trivial multiplier. This is a
consequence of the elementary cubic character, not a residue hypothesis. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootBruhat_coprime {p : Eisenstein} (_hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : IsCoprime p (3*y) := by
  obtain ⟨z,hz⟩ := hxy
  refine ⟨-(p^2*z),3*x,?_⟩
  linear_combination hz

lemma cubicThetaPrimeCubeRootBruhat_phase {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : cubicSymbol (p^3) (3*y)=1 := by
  have hc := cubicThetaPrimeCubeRootBruhat_coprime hp x y hxy
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hc
  have hp3 : cubicSymbol p (3*y)^3=1 := by
    rw [cubicSymbol_prime hp]
    apply cubicSymbolAtPrime_unit_cube hp
    rw [←hu]
    exact u.isUnit
  calc
    _ = cubicSymbol p (3*y)^3 := by
      rw [pow_succ,pow_two,cubicSymbol_mul_lower (mul_ne_zero hp.2.ne_zero hp.2.ne_zero) hp.2.ne_zero,
        cubicSymbol_mul_lower hp.2.ne_zero hp.2.ne_zero]
      ring
    _ = 1 := hp3

lemma cubicThetaPrimeCubeRoot_nine_unit {p : Eisenstein} (hp : primaryPrime p) :
    IsUnit (Ideal.Quotient.mk (modulus (p^3)) 9) := by
  have hc : IsCoprime (p^3) (9:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCube_primary hp)).pow_right (n:=2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hc
  rw [←hu]
  exact u.isUnit

lemma cubicThetaPrimeCubeRootReciprocal_pair {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : IsUnit r) :
    p^3∣9*residueRepresentative (p^3) (cubicThetaPrimeRootReciprocal (p^3) r)*
      residueRepresentative (p^3) r-1 := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (modulus (p^3))
    (9*residueRepresentative (p^3) (cubicThetaPrimeRootReciprocal (p^3) r)*
      residueRepresentative (p^3) r-1)=0
  rw [map_sub,map_one,sub_eq_zero]
  simp only [map_mul,residueRepresentative_spec,cubicThetaPrimeRootReciprocal]
  calc
    _ = Ring.inverse (Ideal.Quotient.mk (modulus (p^3)) 9*r)*
        (Ideal.Quotient.mk (modulus (p^3)) 9*r) := by ring
    _ = 1 := Ring.inverse_mul_cancel _ ((cubicThetaPrimeCubeRoot_nine_unit hp).mul hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCuspObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted cusp observations of finite cubic-root sections, evaluated
by absolutely convergent Fubini integrals. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootFunction {p : Eisenstein} (F : cubicThetaPrimeCubeRootSections p)
    (y : ℂ × ℝ) : ℂ := F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaPrimeCubeRootFunction_coordinates {p : Eisenstein}
    (F : cubicThetaPrimeCubeRootSections p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeRootFunction F x.val=F.val x := by
  exact congrArg F.val (cubicThetaPointInclusion.left_inv (by
    rw [cubicThetaPointInclusion_source]; trivial))

lemma cubicThetaPrimeCubeRootFunction_apply {p : Eisenstein}
    (F : cubicThetaPrimeCubeRootSections p) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPrimeCubeRootFunction F y=F.val ⟨y,hy⟩ := by
  apply congrArg F.val
  apply Subtype.ext
  exact cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootIwahoriConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic Iwahori subgroup normalizes the actual root-cover
subgroup. The proof retains its lower-entry and central-diagonal congruences. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootIwahori_lower (g h : cubicThetaPrincipalGroup) :
    (g*h*g⁻¹).val 1 0=
      g.val 1 0*g.val 1 1*(h.val 0 0-h.val 1 1)+
        (g.val 1 1)^2*h.val 1 0-(g.val 1 0)^2*h.val 0 1 := by
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

lemma cubicThetaPrimeRootIwahori_diagonal (g h : cubicThetaPrincipalGroup) :
    (g*h*g⁻¹).val 0 0-(g*h*g⁻¹).val 1 1=
      (g.val 0 0*g.val 1 1+g.val 0 1*g.val 1 0)*(h.val 0 0-h.val 1 1)+
        2*g.val 0 1*g.val 1 1*h.val 1 0-2*g.val 0 0*g.val 1 0*h.val 0 1 := by
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

def cubicThetaPrimeRootIwahoriConjugate {p : Eisenstein} (g : cubicThetaPrimeIwahori p)
    (h : cubicThetaPrimeRootSubgroup p) : cubicThetaPrimeRootSubgroup p :=
  ⟨g.val*h.val*g.val⁻¹,by
    obtain ⟨C,hC⟩ := g.property
    obtain ⟨c,hc⟩ := h.property.1
    obtain ⟨d,hd⟩ := h.property.2
    change p^2∣(g.val*h.val*g.val⁻¹).val 1 0 ∧
      p∣(g.val*h.val*g.val⁻¹).val 0 0-(g.val*h.val*g.val⁻¹).val 1 1
    rw [cubicThetaPrimeRootIwahori_lower,cubicThetaPrimeRootIwahori_diagonal,hC,hc,hd]
    constructor
    · refine ⟨C*g.val.val 1 1*d+(g.val.val 1 1)^2*c-C^2*h.val.val 0 1,?_⟩
      ring
    · refine ⟨(g.val.val 0 0*g.val.val 1 1+g.val.val 0 1*(p*C))*d+
        2*g.val.val 0 1*g.val.val 1 1*p*c-2*g.val.val 0 0*C*h.val.val 0 1,?_⟩
      ring⟩

def cubicThetaPrimeRootIwahoriEquiv {p : Eisenstein} (g : cubicThetaPrimeIwahori p) :
    cubicThetaPrimeRootSubgroup p ≃ cubicThetaPrimeRootSubgroup p where
  toFun := cubicThetaPrimeRootIwahoriConjugate g
  invFun := cubicThetaPrimeRootIwahoriConjugate g⁻¹
  left_inv h := by
    apply Subtype.ext
    change g.val⁻¹*(g.val*h.val*g.val⁻¹)*(g.val⁻¹)⁻¹=h.val
    group
  right_inv h := by
    apply Subtype.ext
    change g.val*(g.val⁻¹*h.val*(g.val⁻¹)⁻¹)*g.val⁻¹=h.val
    group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Hermitian pairing on the finite arithmetic root cover.
Both root translations and Weyl inversion preserve its integral. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeRootSectionPairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) : CubicThetaPrimeRootCover hp → ℂ :=
  Quotient.lift (fun x : CubicThetaPoint => star (F.val x)*G.val x) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg,cubicThetaPrimeRootSection_property hp F,cubicThetaPrimeRootSection_property hp G,
      star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
          (star (F.val y)*G.val y) := by ring
      _ = _ := by rw [hk,one_mul])

lemma cubicThetaPrimeRootSectionPairing_apply {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) (x : CubicThetaPoint) :
    cubicThetaPrimeRootSectionPairing hp F G (cubicThetaPrimeRootCoverMap hp x)=
      star (F.val x)*G.val x := rfl

lemma cubicThetaPrimeRootSectionPairing_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) :
    Continuous (cubicThetaPrimeRootSectionPairing hp F G) := by
  apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact F.val.continuous.star.mul G.val.continuous

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootDilationOrthogonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original and once-dilated global subspaces are orthogonal in
the actual root-cover pairing, by their distinct cubic diagonal characters. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionPairing_unfold {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) :
    (∫ q, cubicThetaPrimeRootSectionPairing hp F G q ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ x in cubicThetaPrimeRootCoverDomain hp,star (F.val x)*G.val x ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeRootCoverMeasure]
  exact integral_map_of_stronglyMeasurable
    (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable
    (cubicThetaPrimeRootSectionPairing_continuous hp F G).stronglyMeasurable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSquareCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second dilation has the other nontrivial cubic character on
the subgroup with lower-left entry divisible by the prime square. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeSquareIwahori {p : Eisenstein} (g : cubicThetaPrimeIwahori (p^2)) :
    cubicThetaPrimeIwahori p :=
  ⟨g.val,(dvd_pow_self p (by decide : 2≠0)).trans g.property⟩

def cubicThetaPrimeSquareConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) : cubicThetaPrimeIwahori p :=
  ⟨cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g),by
    change p∣g.val.val 1 0/p
    obtain ⟨b,hb⟩ := g.property
    rw [hb,pow_two,mul_assoc,mul_div_cancel_left₀ _ hp.2.ne_zero]
    exact dvd_mul_right p b⟩

lemma cubicThetaPrimeSquareConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g))=
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)*
        cubicThetaKubotaValue g.val := by
  let c := cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)
  have h1 := cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimeConjugate_kubota hp (cubicThetaPrimeSquareConjugate hp g)
  have hc : cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareConjugate hp g)=c := rfl
  rw [hc] at h2
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g))=
    c*cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g)) at h2
  change cubicThetaKubotaValue g.val=c*
    cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g)) at h1
  have he := h1.trans (congrArg (fun z : ℂ => c*z) h2)
  have h3 : c^3=1 := cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeSquareIwahori g)
  change _=c*cubicThetaKubotaValue g.val
  rw [he]
  calc
    _ = 1*cubicThetaKubotaValue
        (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g)) := by rw [one_mul]
    _ = c^3*cubicThetaKubotaValue
        (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g)) := by rw [h3]
    _ = _ := by ring

theorem cubicThetaPrimeSquareCharacter_nontrivial {p : Eisenstein} (hp : primaryPrime p) :
    ∃ g : cubicThetaPrimeIwahori (p^2),
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)≠1 := by
  obtain ⟨d,hd,hpd,hχ⟩ := cubicThetaPrime_primary_nontrivial hp
  let r : CubicThetaBottomRow :=
    ⟨3*p^2,d,dvd_mul_right 3 (p^2),hd,(primary_coprime_three hd).symm.mul_left hpd.pow_left⟩
  let g : cubicThetaPrimeIwahori (p^2) := ⟨r.completion,by
    have hc := congrArg CubicThetaBottomRow.c r.completion_row
    change r.completion.val 1 0=3*p^2 at hc
    change p^2∣r.completion.val 1 0
    rw [hc]
    exact dvd_mul_left (p^2) 3⟩
  refine ⟨g,?_⟩
  have hr := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 1=d at hr
  have he : p∣g.val.val 0 0*d-1 := by
    have hg := cubicThetaPrincipalGroup_det g.val
    rw [show g.val.val 1 1=d from hr] at hg
    rw [show g.val.val 0 0*d-1=g.val.val 0 1*g.val.val 1 0 by linear_combination hg]
    exact dvd_mul_of_dvd_right (cubicThetaPrimeSquareIwahori g).property _
  have hone : cubicSymbol p (g.val.val 0 0*d)=1 := by
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  rw [cubicSymbol_mul_upper hp.1] at hone
  intro htriv
  change cubicSymbol p (g.val.val 0 0)=1 at htriv
  rw [htriv,one_mul] at hone
  exact hχ hone

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDeepCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nontrivial diagonal character deep enough to normalize the actual
cubic root cover, for the intermediate-valuation cancellation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeSixthIwahori {p : Eisenstein} (g : cubicThetaPrimeIwahori (p^6)) :
    cubicThetaPrimeIwahori p :=
  ⟨g.val,(dvd_pow_self p (by decide : 6≠0)).trans g.property⟩

theorem cubicThetaPrimeSixthCharacter_nontrivial {p : Eisenstein} (hp : primaryPrime p) :
    ∃ g : cubicThetaPrimeIwahori (p^6),
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSixthIwahori g)≠1 := by
  obtain ⟨d,hd,hpd,hχ⟩ := cubicThetaPrime_primary_nontrivial hp
  let r : CubicThetaBottomRow :=
    ⟨3*p^6,d,dvd_mul_right 3 (p^6),hd,(primary_coprime_three hd).symm.mul_left hpd.pow_left⟩
  let g : cubicThetaPrimeIwahori (p^6) := ⟨r.completion,by
    have hc := congrArg CubicThetaBottomRow.c r.completion_row
    change r.completion.val 1 0=3*p^6 at hc
    change p^6∣r.completion.val 1 0
    rw [hc]
    exact dvd_mul_left (p^6) 3⟩
  refine ⟨g,?_⟩
  have hr := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 1=d at hr
  have he : p∣g.val.val 0 0*d-1 := by
    have hg := cubicThetaPrincipalGroup_det g.val
    rw [show g.val.val 1 1=d from hr] at hg
    rw [show g.val.val 0 0*d-1=g.val.val 0 1*g.val.val 1 0 by linear_combination hg]
    exact dvd_mul_of_dvd_right (cubicThetaPrimeSixthIwahori g).property _
  have hone : cubicSymbol p (g.val.val 0 0*d)=1 := by
    rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
    simpa only [pow_zero] using cubicSymbol_pow_upper hp.1 1 0
  rw [cubicSymbol_mul_upper hp.1] at hone
  intro htriv
  change cubicSymbol p (g.val.val 0 0)=1 at htriv
  rw [htriv,one_mul] at hone
  exact hχ hone


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootPowerOrthogonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing of the second and fourth dilation pairings on the actual
cubic root cover, forced by their nontrivial diagonal characters. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeSixthPowerIwahori {p : Eisenstein} (n : ℕ) (hn : n≤6)
    (g : cubicThetaPrimeIwahori (p^6)) : cubicThetaPrimeIwahori (p^n) :=
  ⟨g.val,(pow_dvd_pow p hn).trans g.property⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverDegree
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root cover has its exact finite subgroup index as measure degree. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverProjection {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp → CubicThetaQuotient :=
  Quotient.map id (by
    intro a b hab
    obtain ⟨g,hg⟩ := hab
    exact ⟨g.val,hg⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverBorel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable section of the actual root cover, constructed from
a countable disjoint refinement of its injective covering charts. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimeRootCoverChart {p : Eisenstein} (hp : primaryPrime p) (x : CubicThetaPoint) :
    OpenPartialHomeomorph CubicThetaPoint (CubicThetaPrimeRootCover hp) :=
  Classical.choose ((cubicThetaPrimeRootCover_covering hp).isCoveringMap.isLocalHomeomorph x)

lemma cubicThetaPrimeRootCoverChart_source {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) : x∈(cubicThetaPrimeRootCoverChart hp x).source :=
  (Classical.choose_spec ((cubicThetaPrimeRootCover_covering hp).isCoveringMap.isLocalHomeomorph x)).1

lemma cubicThetaPrimeRootCoverChart_coe {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    (cubicThetaPrimeRootCoverChart hp x : CubicThetaPoint → CubicThetaPrimeRootCover hp)=
      cubicThetaPrimeRootCoverMap hp :=
  (Classical.choose_spec ((cubicThetaPrimeRootCover_covering hp).isCoveringMap.isLocalHomeomorph x)).2.symm

lemma cubicThetaPrimeRootCover_countable_charts {p : Eisenstein} (hp : primaryPrime p) :
    ∃ c : ℕ → CubicThetaPoint,
      ∀ q : CubicThetaPrimeRootCover hp, ∃ n, q∈(cubicThetaPrimeRootCoverChart hp (c n)).target := by
  obtain ⟨S,hSc,hS⟩ := isLindelof_univ.elim_countable_subcover
    (fun x : CubicThetaPoint => (cubicThetaPrimeRootCoverChart hp x).target)
    (fun x => (cubicThetaPrimeRootCoverChart hp x).open_target) (by
      intro q _
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective q
      apply mem_iUnion.mpr
      refine ⟨x,?_⟩
      change cubicThetaPrimeRootCoverMap hp x∈(cubicThetaPrimeRootCoverChart hp x).target
      rw [←cubicThetaPrimeRootCoverChart_coe hp x]
      exact (cubicThetaPrimeRootCoverChart hp x).map_source (cubicThetaPrimeRootCoverChart_source hp x))
  have hSne : S.Nonempty := by
    let x : CubicThetaPoint := ⟨(0,1),by norm_num⟩
    obtain ⟨y,hy,_⟩ := mem_iUnion₂.mp (hS (mem_univ (cubicThetaPrimeRootCoverMap hp x)))
    exact ⟨y,hy⟩
  obtain ⟨c,hc⟩ := hSc.exists_eq_range hSne
  refine ⟨c,fun q => ?_⟩
  obtain ⟨x,hx,hqx⟩ := mem_iUnion₂.mp (hS (mem_univ q))
  rw [hc] at hx
  obtain ⟨n,rfl⟩ := hx
  exact ⟨n,hqx⟩

def cubicThetaPrimeRootCoverCenter {p : Eisenstein} (hp : primaryPrime p) : ℕ → CubicThetaPoint :=
  Classical.choose (cubicThetaPrimeRootCover_countable_charts hp)

def cubicThetaPrimeRootCoverOpen {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Set (CubicThetaPrimeRootCover hp) :=
  (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).target

def cubicThetaPrimeRootCoverPiece {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Set (CubicThetaPrimeRootCover hp) := disjointed (cubicThetaPrimeRootCoverOpen hp) n

lemma cubicThetaPrimeRootCoverPiece_measurable {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    MeasurableSet (cubicThetaPrimeRootCoverPiece hp n) :=
  MeasurableSet.disjointed
    (fun n => (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).open_target.measurableSet) n

lemma cubicThetaPrimeRootCoverPiece_cover {p : Eisenstein} (hp : primaryPrime p) :
    ⋃ n, cubicThetaPrimeRootCoverPiece hp n=univ := by
  change (⋃ n, disjointed (cubicThetaPrimeRootCoverOpen hp) n)=univ
  rw [iUnion_disjointed]
  apply eq_univ_of_forall
  intro q
  exact mem_iUnion.mpr (Classical.choose_spec (cubicThetaPrimeRootCover_countable_charts hp) q)

def cubicThetaPrimeRootCoverLocalLift {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    CubicThetaPrimeRootCover hp → CubicThetaPoint :=
  (cubicThetaPrimeRootCoverOpen hp n).piecewise
    (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).symm
    (fun _ => cubicThetaPrimeRootCoverCenter hp n)

lemma cubicThetaPrimeRootCoverLocalLift_measurable {p : Eisenstein} (hp : primaryPrime p) (n : ℕ) :
    Measurable (cubicThetaPrimeRootCoverLocalLift hp n) := by
  apply ContinuousOn.measurable_piecewise
  · exact (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).symm.continuousOn
  · exact continuous_const.continuousOn
  · exact (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).open_target.measurableSet

lemma cubicThetaPrimeRootCoverLocalLift_rightInverse {p : Eisenstein} (hp : primaryPrime p)
    (n : ℕ) {q : CubicThetaPrimeRootCover hp} (hq : q∈cubicThetaPrimeRootCoverPiece hp n) :
    cubicThetaPrimeRootCoverMap hp (cubicThetaPrimeRootCoverLocalLift hp n q)=q := by
  have hu := disjointed_subset (cubicThetaPrimeRootCoverOpen hp) n hq
  rw [cubicThetaPrimeRootCoverLocalLift,piecewise_eq_of_mem _ _ _ hu]
  rw [←cubicThetaPrimeRootCoverChart_coe hp (cubicThetaPrimeRootCoverCenter hp n)]
  exact (cubicThetaPrimeRootCoverChart hp (cubicThetaPrimeRootCoverCenter hp n)).right_inv hu

theorem cubicThetaPrimeRootCover_measurable_section_exists {p : Eisenstein} (hp : primaryPrime p) :
    ∃ s : CubicThetaPrimeRootCover hp → CubicThetaPoint,
      Measurable s ∧ Function.RightInverse s (cubicThetaPrimeRootCoverMap hp) := by
  obtain ⟨s,hs,hse⟩ := exists_measurable_piecewise (cubicThetaPrimeRootCoverPiece hp)
    (cubicThetaPrimeRootCoverPiece_measurable hp) (cubicThetaPrimeRootCoverLocalLift hp)
    (cubicThetaPrimeRootCoverLocalLift_measurable hp) (by
      intro i j hij q hq
      exact False.elim (Set.disjoint_left.mp
        (disjoint_disjointed (cubicThetaPrimeRootCoverOpen hp) hij) hq.1 hq.2))
  refine ⟨s,hs,fun q => ?_⟩
  obtain ⟨n,hn⟩ := mem_iUnion.mp ((cubicThetaPrimeRootCoverPiece_cover hp).symm ▸ mem_univ q)
  rw [hse n hn]
  exact cubicThetaPrimeRootCoverLocalLift_rightInverse hp n hn

def cubicThetaPrimeRootBorelSection {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp → CubicThetaPoint :=
  Classical.choose (cubicThetaPrimeRootCover_measurable_section_exists hp)

lemma cubicThetaPrimeRootBorelSection_measurable {p : Eisenstein} (hp : primaryPrime p) :
    Measurable (cubicThetaPrimeRootBorelSection hp) :=
  (Classical.choose_spec (cubicThetaPrimeRootCover_measurable_section_exists hp)).1

lemma cubicThetaPrimeRootBorelSection_rightInverse {p : Eisenstein} (hp : primaryPrime p) :
    Function.RightInverse (cubicThetaPrimeRootBorelSection hp) (cubicThetaPrimeRootCoverMap hp) :=
  (Classical.choose_spec (cubicThetaPrimeRootCover_measurable_section_exists hp)).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeRootSectionRepresentative {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) : ℂ :=
  F.val (cubicThetaPrimeRootBorelSection hp q)

lemma cubicThetaPrimeRootSectionRepresentative_measurable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : Measurable (cubicThetaPrimeRootSectionRepresentative hp F) :=
  F.val.continuous.measurable.comp (cubicThetaPrimeRootBorelSection_measurable hp)

lemma cubicThetaPrimeRootSectionRepresentative_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) :
    ‖cubicThetaPrimeRootSectionRepresentative hp F q‖=cubicThetaPrimeRootSectionNorm hp F q := by
  have he := cubicThetaPrimeRootSectionNorm_apply hp F (cubicThetaPrimeRootBorelSection hp q)
  rw [cubicThetaPrimeRootBorelSection_rightInverse hp q] at he
  exact he.symm

lemma cubicThetaPrimeRootSectionL2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)) :
    ‖hF.toLp (cubicThetaPrimeRootSectionRepresentative hp F)‖^2=
      ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with q hq
  rw [hq,cubicThetaPrimeRootSectionRepresentative_norm]

def cubicThetaPrimeRootFiniteSections {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (cubicThetaPrimeRootSections p) where
  carrier := {F | MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)}
  zero_mem' := MemLp.zero
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

def cubicThetaPrimeRootFiniteValue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ] CubicThetaPrimeRootL2 hp where
  toFun F := F.property.toLp _
  map_add' F G := MemLp.toLp_add F.property G.property
  map_smul' c F := MemLp.toLp_const_smul c F.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootAutomorphicL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completion of the actual finite-mass sections on the root cover.
The geometric Weyl pullback extends to a linear isometry of this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance rootFiniteSections_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeRootAutomorphicL2 {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (CubicThetaPrimeRootL2 hp) := (cubicThetaPrimeRootFiniteValue hp).range.topologicalClosure

instance cubicThetaPrimeRootAutomorphicL2_complete {p : Eisenstein} (hp : primaryPrime p) :
    CompleteSpace (cubicThetaPrimeRootAutomorphicL2 hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaPrimeRootFiniteEmbedding {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  (cubicThetaPrimeRootFiniteValue hp).codRestrict (cubicThetaPrimeRootAutomorphicL2 hp)
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaPrimeRootFiniteEmbedding_dense {p : Eisenstein} (hp : primaryPrime p) :
    DenseRange (cubicThetaPrimeRootFiniteEmbedding hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (cubicThetaPrimeRootFiniteEmbedding hp)=
      Set.range (cubicThetaPrimeRootFiniteValue hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaPrimeRootFiniteEmbedding hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootTranslationL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional translations extend isometrically to the actual completed
space of root-cover sections. -/
noncomputable section
namespace CubicFirstMoment

local instance rootTranslation_finiteGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

local instance rootLift_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

lemma cubicThetaPrimeRootCoverDegree_pos {p : Eisenstein} (hp : primaryPrime p) :
    0<((cubicThetaPrimeRootCoverGroup hp).index:ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootPairingL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal root-cover integral is its L2 pairing; the original
and twice-dilated global Hilbert subspaces are orthogonal. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionPairing_L2 {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootFiniteSections hp) :
    inner ℂ (cubicThetaPrimeRootFiniteEmbedding hp F) (cubicThetaPrimeRootFiniteEmbedding hp G)=
      ∫ q, cubicThetaPrimeRootSectionPairing hp F.val G.val q ∂cubicThetaPrimeRootCoverMeasure hp := by
  change inner ℂ (F.property.toLp (cubicThetaPrimeRootSectionRepresentative hp F.val))
    (G.property.toLp (cubicThetaPrimeRootSectionRepresentative hp G.val))=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp,G.property.coeFn_toLp] with q hF hG
  rw [hF,hG]
  have he := cubicThetaPrimeRootSectionPairing_apply hp F.val G.val (cubicThetaPrimeRootBorelSection hp q)
  rw [cubicThetaPrimeRootBorelSection_rightInverse hp q] at he
  simpa only [RCLike.inner_apply',Complex.star_def,cubicThetaPrimeRootSectionRepresentative] using he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFirstIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the first root level to the actual cube-root domain.
In particular the nonzero p-squared residue branches have zero pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_le_first {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootCoverGroup hp ≤ cubicThetaPrimeRootCoverGroup hp := by
  intro g hg
  refine ⟨(show p^2∣(p^3)^2 from ⟨p^4,by ring⟩).trans hg.1,?_⟩
  exact (dvd_pow_self p (by decide : 3≠0)).trans hg.2

lemma cubicThetaPrimeCubeRootElement_square {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (p^2*x)=cubicThetaPrimeRootElement hp x := by
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrimeRootElement_translation]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp [hpC]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootRamanujan
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cube-modulus Ramanujan value at the missing square class.
This is a finite character identity, independent of its later Hecke application. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRoot_ramanujan {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=-(norm p:ℂ)^2 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 2 h
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=
    (norm (p^2):ℂ)*cubicThetaPrimeFourier p hp 3 h at he
  rw [cubicThetaPrimeFourier_three hp h,ite_eq_right hh] at he
  rw [he,eisenstein_norm_pow,Complex.ofReal_pow]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootMatrix
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeDoubleRootSubgroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeDoubleRootSubgroup p).FiniteIndex :=
  cubicThetaPrimeRootSubgroup_finiteIndex (pow_ne_zero 2 hp.2.ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeDoubleRootElement_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) :
    cubicThetaPrimeDoubleRootElement hp (x+y)=
      cubicThetaPrimeDoubleRootElement hp x*cubicThetaPrimeDoubleRootElement hp y := by
  simp only [cubicThetaPrimeDoubleRootElement_translation]
  apply Subtype.ext
  change (!![1,((3*(x+y):Eisenstein):ℂ)/((p^2:Eisenstein):ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)=
    !![1,((3*x:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ);0,1]*!![1,((3*y:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ);0,1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_add,add_div,add_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleAtkin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squared-prime Atkin matrix and its exact integral conjugation.
Character invariance is used only on the root subgroup. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeDoubleAtkinConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) : cubicThetaPrimeIwahori (p^2) :=
  ⟨cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g),by
    have he := (cubicThetaInversionConjugate_entries
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)).2
    change p^2∣(cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)).val 1 0
    rw [he]
    change p^2∣-(p^2*g.val.val 0 1)
    exact dvd_neg.mpr (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeDoubleAtkinConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    ((cubicThetaPrimeDoubleAtkinConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^2);-p^2*g.val.val 0 1,g.val.val 0 0] := by
  change (((cubicThetaFullInversion⁻¹)⁻¹*
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero (cubicThetaPrimeDouble_primary hp)) g*
      cubicThetaFullInversion⁻¹ : SL(2,Eisenstein)) : Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [inv_inv,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [cubicThetaFullInversion,cubicThetaPrimeConjugatedMatrix,Matrix.adjugate_fin_two]

def cubicThetaPrimeDoubleAtkinMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)

theorem cubicThetaPrimeDoubleAtkinMatrix_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    cubicThetaPrimeDoubleAtkinMatrix hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleAtkinConjugate hp g).val*
        cubicThetaPrimeDoubleAtkinMatrix hp := by
  have he : cubicThetaPrincipalComplex (cubicThetaPrimeDoubleAtkinConjugate hp g).val=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)*
          (cubicThetaFullComplex cubicThetaFullInversion)⁻¹ := by
    change cubicThetaFullComplex ((cubicThetaFullInversion⁻¹)⁻¹*
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g).val*cubicThetaFullInversion⁻¹)=_
    rw [inv_inv,map_mul,map_mul,map_inv]
    rfl
  rw [cubicThetaPrimeDoubleAtkinMatrix,mul_assoc,
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) g,he]
  group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootWeyl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeDoubleRootDilationIwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeIwahori (p^2) :=
  ⟨cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeDoubleRootIwahori g),by
    change p^2∣g.val.val 1 0/p^2
    rw [cubicThetaPrimeDoubleRoot_lower_single_division hp g]
    exact dvd_mul_right _ _⟩

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry00 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 0 0=g.val.val 0 0 := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry01 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 0 1=p^2*g.val.val 0 1 := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry10 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 1 0=g.val.val 1 0/p^2 := rfl

lemma cubicThetaPrimeDoubleRootDilationIwahori_entry11 {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    (cubicThetaPrimeDoubleRootDilationIwahori hp g).val.val 1 1=g.val.val 1 1 := rfl

lemma cubicThetaPrimeDoubleRootWeylRaw_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    ((cubicThetaPrimeDoubleAtkinConjugate hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val :
      Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^2)^2);-(p^2)^2*g.val.val 0 1,g.val.val 0 0] := by
  have he := cubicThetaPrimeDoubleAtkinConjugate_matrix hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)
  rw [cubicThetaPrimeDoubleRootDilationIwahori_entry00,
    cubicThetaPrimeDoubleRootDilationIwahori_entry01,
    cubicThetaPrimeDoubleRootDilationIwahori_entry10,
    cubicThetaPrimeDoubleRootDilationIwahori_entry11] at he
  rw [he,cubicThetaPrimeDoubleRoot_lower_single_division hp g,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero)]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pow_two,mul_assoc]

def cubicThetaPrimeDoubleRootWeylConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) : cubicThetaPrimeDoubleRootSubgroup p :=
  ⟨(cubicThetaPrimeDoubleAtkinConjugate hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val,by
    change (p^2)^2∣(cubicThetaPrimeDoubleAtkinConjugate hp
      (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val 1 0 ∧
      p^2∣(cubicThetaPrimeDoubleAtkinConjugate hp
      (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val 0 0-
      (cubicThetaPrimeDoubleAtkinConjugate hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)).val.val 1 1
    rw [cubicThetaPrimeDoubleRootWeylRaw_matrix]
    constructor
    · exact ⟨-g.val.val 0 1,by simp⟩
    · simpa only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_sub]
        using dvd_neg.mpr g.property.2⟩

lemma cubicThetaPrimeDoubleRootWeylConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    ((cubicThetaPrimeDoubleRootWeylConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^2)^2);-(p^2)^2*g.val.val 0 1,g.val.val 0 0] :=
  cubicThetaPrimeDoubleRootWeylRaw_matrix hp g


def cubicThetaPrimeDoubleRootWeylElement {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaPrimeDoubleAtkinMatrix hp*cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)

theorem cubicThetaPrimeDoubleRootWeyl_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootWeylElement hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootWeylConjugate hp g).val*
        cubicThetaPrimeDoubleRootWeylElement hp := by
  have hD : cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootDilationIwahori hp g).val*
        cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeDoubleRootIwahori g)
  have hW : cubicThetaPrimeDoubleAtkinMatrix hp*
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootDilationIwahori hp g).val=
      cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootWeylConjugate hp g).val*cubicThetaPrimeDoubleAtkinMatrix hp :=
    cubicThetaPrimeDoubleAtkinMatrix_intertwines hp (cubicThetaPrimeDoubleRootDilationIwahori hp g)
  unfold cubicThetaPrimeDoubleRootWeylElement
  rw [mul_assoc,hD,←mul_assoc,hW,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootBruhat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal integral Bruhat identity for unit translations modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootBruhat_division {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    p^2*((1-9*x*y)/p^2)=1-9*x*y := by
  apply EuclideanDomain.mul_div_cancel' (pow_ne_zero 2 hp.2.ne_zero)
  simpa only [neg_sub] using dvd_neg.mpr hxy

def cubicThetaPrimeDoubleRootBruhatMatrix {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) : SL(2,Eisenstein) :=
  ⟨!![p^2,3*x;-3*y,(1-9*x*y)/p^2],by
    rw [Matrix.det_fin_two_of]
    linear_combination cubicThetaPrimeDoubleRootBruhat_division hp x y hxy⟩

lemma cubicThetaPrimeDoubleRootBruhatMatrix_mem {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    cubicThetaPrimeDoubleRootBruhatMatrix hp x y hxy∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (p^2) ∧ (3:Eisenstein)∣3*x ∧ (3:Eisenstein)∣-3*y ∧ primary ((1-9*x*y)/p^2)
  refine ⟨(cubicThetaPrimeDouble_primary hp),⟨x,rfl⟩,⟨-y,by ring⟩,?_⟩
  change (3:Eisenstein)∣(1-9*x*y)/p^2-1
  apply (primary_coprime_three (cubicThetaPrimeDouble_primary hp)).symm.dvd_of_dvd_mul_left
  rw [mul_sub,mul_one,cubicThetaPrimeDoubleRootBruhat_division hp x y hxy]
  convert dvd_sub (dvd_neg.mpr (cubicThetaPrimeDouble_primary hp)) (show (3:Eisenstein)∣9*x*y from ⟨3*x*y,by ring⟩) using 1
  all_goals try with_reducible_and_instances rfl
  ring

def cubicThetaPrimeDoubleRootBruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeDoubleRootBruhatMatrix hp x y hxy,cubicThetaPrimeDoubleRootBruhatMatrix_mem hp x y hxy⟩

lemma cubicThetaPrimeDoubleRootBruhat_kubota {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeDoubleRootBruhat hp x y hxy)=cubicSymbol (p^2) (3*y) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol (p^2) (-3*y)=cubicSymbol (p^2) (3*y)
  rw [neg_mul,cubicSymbol_neg (cubicThetaPrimeDouble_primary hp)]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootWeylSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Involutive action of the opposite square root on actual sections. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootWeylConjugate_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeDoubleRootWeylConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeDoubleRootWeylConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -((p^2)^2*g.val.val 0 1)=(p^2)^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (pow_ne_zero 2 hp.2.ne_zero)),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeDoubleRoot_lower_division hp g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeDoubleRootWeylConjugate_matrix hp g)

lemma cubicThetaPrimeDoubleRootWeylPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeDoubleRootWeylElement hp • (g.val • y)=
      (cubicThetaPrimeDoubleRootWeylConjugate hp g).val • (cubicThetaPrimeDoubleRootWeylElement hp • y) := by
  change cubicThetaPrimeDoubleRootWeylElement hp • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootWeylConjugate hp g).val •
      (cubicThetaPrimeDoubleRootWeylElement hp • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeDoubleRootWeyl_intertwines]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootAutomorphism
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fractional roots normalize the actual arithmetic subgroup. The
inverse is the negative root, with no choice of an abstract local model. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootConjugate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaPrimeDoubleRootConjugate hp (x+y) g=
      cubicThetaPrimeDoubleRootConjugate hp x (cubicThetaPrimeDoubleRootConjugate hp y g) := by
  apply Subtype.ext
  apply cubicThetaPrincipalComplex_injective
  simp only [cubicThetaPrimeDoubleRootConjugate_complex,cubicThetaPrimeDoubleRootElement_add,mul_inv_rev]
  group

def cubicThetaPrimeDoubleRootAutomorphism {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeDoubleRootSubgroup p ≃* cubicThetaPrimeDoubleRootSubgroup p where
  toFun := cubicThetaPrimeDoubleRootConjugate hp x
  invFun := cubicThetaPrimeDoubleRootConjugate hp (-x)
  left_inv g := by
    rw [←cubicThetaPrimeDoubleRootConjugate_add,neg_add_cancel,cubicThetaPrimeDoubleRootConjugate_zero]
  right_inv g := by
    rw [←cubicThetaPrimeDoubleRootConjugate_add,add_neg_cancel,cubicThetaPrimeDoubleRootConjugate_zero]
  map_mul' g h := by
    apply Subtype.ext
    apply cubicThetaPrincipalComplex_injective
    change cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootConjugate hp x (g*h)).val=
      cubicThetaPrincipalComplex ((cubicThetaPrimeDoubleRootConjugate hp x g).val*
        (cubicThetaPrimeDoubleRootConjugate hp x h).val)
    simp only [cubicThetaPrimeDoubleRootConjugate_complex,map_mul,Subgroup.coe_mul]
    group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal Hermitian integral transport on the intermediate root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRoot_pair_invariant {p : Eisenstein} (_hp : primaryPrime p)
    (F G : cubicThetaPrimeDoubleRootSections p) (g : cubicThetaPrimeDoubleRootSubgroup p)
    (z : CubicThetaPoint) :
    star (F.val (g • z))*G.val (g • z)=star (F.val z)*G.val z := by
  change star (F.val (g.val • z))*G.val (g.val • z)=_
  rw [F.property,G.property,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
      (star (F.val z)*G.val z) := by ring
    _ = _ := by rw [hk,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootOrthogonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The twice-squared dilation has a nontrivial diagonal character.
Its actual integral pairing with global sections vanishes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeDoubleSquareConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori ((p^2)^2)) : cubicThetaPrimeIwahori (p^2) :=
  ⟨cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeSquareIwahori g),by
    change p^2∣g.val.val 1 0/p^2
    obtain ⟨b,hb⟩ := g.property
    rw [hb,show (p^2)^2*b=p^2*(p^2*b) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero)]
    exact dvd_mul_right (p^2) b⟩

lemma cubicThetaPrimeDoubleSquareConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori ((p^2)^2)) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleSquareConjugate hp g))=
    star ((cubicSymbol p (g.val.val 0 0))^4)*cubicThetaKubotaValue g.val := by
  have h1 := cubicThetaPrimePowerConjugate_kubota_star hp 2 (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimePowerConjugate_kubota_star hp 2 (cubicThetaPrimeDoubleSquareConjugate hp g)
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeSquareIwahori g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*cubicThetaKubotaValue g.val at h1
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleSquareConjugate hp g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*cubicThetaKubotaValue
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeSquareIwahori g)) at h2
  rw [h2,h1,show (cubicSymbol p (g.val.val 0 0))^4=
    (cubicSymbol p (g.val.val 0 0))^2*(cubicSymbol p (g.val.val 0 0))^2 by ring,star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootSecondIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of intermediate root orthogonality to the cubic root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_le_double {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootCoverGroup hp ≤ cubicThetaPrimeDoubleRootSubgroup p := by
  intro g hg
  constructor
  · exact (show (p^2)^2∣(p^3)^2 from ⟨p^2,by ring⟩).trans hg.1
  · exact (show p^2∣p^3 from ⟨p,by ring⟩).trans hg.2

lemma cubicThetaPrimeCubeRootElement_single {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (p*x)=cubicThetaPrimeDoubleRootElement hp x := by
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrimeDoubleRootElement_translation]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp [hpC]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic character at the cube modulus is the literal unit detector. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_weight_unit {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : IsUnit r) :
    cubicSymbol (p^3) (residueRepresentative (p^3) r)=1 := by
  rw [cubicThetaPrimePowerWeight_inflation hp 2,←MulChar.pow_apply' _ (by decide),cubicResidueChar_cube hp]
  exact MulChar.one_apply (hr.map (residueReduction (dvd_pow_self p (by decide : 3≠0))))

lemma cubicThetaPrimeCubeRoot_weight_nonunit {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : ¬IsUnit r) :
    cubicSymbol (p^3) (residueRepresentative (p^3) r)=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [cubicThetaPrimePowerWeight_inflation hp 2]
  have hz := (cubicTheta_primePower_nonunit_iff hp.2 2 r).mp hr
  rw [hz,MulChar.map_zero]
  norm_num

lemma cubicThetaPrimeCubeRoot_weight_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbol (p^3) (residueRepresentative (p^3) 0)=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [cubicThetaPrimePowerWeight_inflation hp 2,map_zero,MulChar.map_zero]
  norm_num

end CubicFirstMoment

end

end OAI
end


