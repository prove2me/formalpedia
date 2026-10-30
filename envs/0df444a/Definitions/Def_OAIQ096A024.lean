-- Prove2me | Definitions.Def_OAIQ096A024
-- name    : OAIQ096A024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T04:09:37.565193+00:00
-- url     : https://prove2.me/theorems/57468ed9-5078-4345-9e72-92641c191ca5
-- title:
--   Definitions bundle OAIQ096A024 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 124 declarations of OpenAI's Lean: 6 definitions and 118 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaConstantRegular`, `OAI.CubicFirstMoment.cubicThetaInversionMass`, `OAI.CubicFirstMoment.cubicThetaInvertedCuspObservable`, `OAI.CubicFirstMoment.cubicThetaInvertedForcedCusp`, `OAI.CubicFirstMoment.cubicThetaInvertedFourierObservable`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootUnitCorrelation`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Estimates_PrincipalZetaPole`, `CubicMoment_Theta_CubicThetaArithmeticPoleIsolation`, `CubicMoment_Theta_CubicThetaConstantContinuation`, `CubicMoment_Theta_CubicThetaCuspFourierIntegral`, `CubicMoment_Theta_CubicThetaCuspFourierNormalization`, `CubicMoment_Theta_CubicThetaCuspFourierObservable`, `CubicMoment_Theta_CubicThetaCuspObservable`, `CubicMoment_Theta_CubicThetaCuspRestriction`, `CubicMoment_Theta_CubicThetaEndpointRegularity`, `CubicMoment_Theta_CubicThetaEnergySimplePole`, `CubicMoment_Theta_CubicThetaForcedCusp`, `CubicMoment_Theta_CubicThetaForcedResidue`, `CubicMoment_Theta_CubicThetaFourierPoleIsolation`, `CubicMoment_Theta_CubicThetaFrequencyContinuation`, `CubicMoment_Theta_CubicThetaFrequencyResidue`, `CubicMoment_Theta_CubicThetaHighWindowPairing`, `CubicMoment_Theta_CubicThetaInversionFiniteCompletion`, `CubicMoment_Theta_CubicThetaInversionMass`, `CubicMoment_Theta_CubicThetaInvertedCusp`, `CubicMoment_Theta_CubicThetaInvertedFourierObservable`, `CubicMoment_Theta_CubicThetaInvertedResidue`, `CubicMoment_Theta_CubicThetaInvertedWindow`, `CubicMoment_Theta_CubicThetaLongWindowKernel`, `CubicMoment_Theta_CubicThetaMeromorphicIdentity`, `CubicMoment_Theta_CubicThetaPointC1Hecke`, `CubicMoment_Theta_CubicThetaPrimeCubeCompletedAdjoint`, `CubicMoment_Theta_CubicThetaPrimeCubeDerivativeAdjoint`, `CubicMoment_Theta_CubicThetaPrimeCubeFiniteAdjoint`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergyOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeMassOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeRadialPairing`, `CubicMoment_Theta_CubicThetaPrimeCubeRadialResidue`, `CubicMoment_Theta_CubicThetaPrimeCubeResidueEigenvalue`, `CubicMoment_Theta_CubicThetaPrimeCubeResiduePeriodicity`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAverageIdentity`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAverageObservation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCorrelationFormula`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCriticalSquare`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCuspLift`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFirstIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootNonunitCorrelation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootNormBalance`, `CubicMoment_Theta_CubicThetaPrimeCubeRootResidueAverage`, `CubicMoment_Theta_CubicThetaPrimeCubeRootResidueOverlap`, `CubicMoment_Theta_CubicThetaPrimeCubeRootTraceNormalized`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylGlobal`, `CubicMoment_Theta_CubicThetaPrimeCubeSelfAdjoint`, `CubicMoment_Theta_CubicThetaPrimeCubeWeakEquation`, `CubicMoment_Theta_CubicThetaPrimeFreeContinuation`, `CubicMoment_Theta_CubicThetaPrimeRootBruhatMass`, `CubicMoment_Theta_CubicThetaPrimeRootOrbitOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeRootTranslationIntegral`, `CubicMoment_Theta_CubicThetaRadialProfilePairing`, `CubicMoment_Theta_CubicThetaRamifiedLowContinuation`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryContinuation`, `CubicMoment_Theta_CubicThetaRegularizedFourier`, `CubicMoment_Theta_CubicThetaResidueSourceOrbit`, `CubicMoment_Theta_CubicThetaResidueVanishing`, `CubicMoment_Theta_CubicThetaScatteringRegular`, `CubicMoment_Theta_CubicThetaSpectralSimplePole`, `CubicMoment_Theta_CubicThetaThetaObservation`, `CubicMoment_Theta_CubicThetaWindowWeak`, `CubicMoment_Theta_CubicThetaZeroObservable`, `CubicMoment_Theta_CubicThetaZeroWindow`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A021`, `OAIQ096A022` and `OAIQ096A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A026`, `OAIQ096A028`, `OAIQ096A029`, `OAIQ096A030` and `OAIQ096A031`; the proofs of `OAI_CubicFirstMoment_ProfileControl_large_common_nonzero_power`, `OAI_CubicFirstMoment_ProfileControl_low_coprime_height_real`, `OAI_CubicFirstMoment_ProfileControl_smallB_nonzero_variance_height_power`, `OAI_CubicFirstMoment_ShortFactorFamily_first_rows_contradiction`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_weighted_bilinear`, `OAI_CubicFirstMoment_all_frequency_outer_sieve`, `OAI_CubicFirstMoment_angular_divisor_full_model_asymptotic`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI_CubicFirstMoment_angular_stopped_divisor_full_model_log_saving`, `OAI_CubicFirstMoment_angular_two_prime_transition_height`, `OAI_CubicFirstMoment_bounded_rough_divisor_variance_remainder`, `OAI_CubicFirstMoment_cubicThetaScalarRankinKernel_residue`, `OAI_CubicFirstMoment_cubic_gram_large_value_count`, `OAI_CubicFirstMoment_divisor_coprime_gram_asymptotic`, `OAI_CubicFirstMoment_first_squarefreeCoordinateError_moment`, `OAI_CubicFirstMoment_normalized_angular_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_normalized_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_primeGroupTail_common_row_height_power`, `OAI_CubicFirstMoment_primeGroupTail_core_block_sieve`, `OAI_CubicFirstMoment_prime_variance_transition_bound`, `OAI_CubicFirstMoment_primitiveResidueHeckeInput_proved`, `OAI_CubicFirstMoment_smallB_core_block_sieve` and `OAI_CubicFirstMoment_stopped_divisor_coprime_model_log_saving`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A021
import Definitions.Def_OAIQ096A022
import Definitions.Def_OAIQ096A023

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaPole
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma principalZetaRegularFactor_analyticAt_one : AnalyticAt ℂ principalZetaRegularFactor 1 := by
  unfold principalZetaRegularFactor
  apply (principalZetaPrefactor_differentiable.analyticAt 1).mul
  apply AnalyticAt.add
  · apply (analyticAt_id.sub analyticAt_const).mul
    exact (principalIdealFEPair.differentiable_Λ₀.analyticAt 1).sub
      (analyticAt_const.div analyticAt_id one_ne_zero)
  · exact analyticAt_const

lemma principalZetaRegularFactor_one :
    principalZetaRegularFactor 1=principalThetaConstant/(residueHeckeScale 1:ℂ) := by
  simp [principalZetaRegularFactor,principalZetaPrefactor,Complex.cpow_neg,
    div_eq_mul_inv,mul_comm]

lemma principalZetaRegularFactor_eq {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    principalZetaRegularFactor s=(s-1)*principalIdealZeta s := by
  change principalZetaPrefactor s*((s-1)*(principalIdealFEPair.Λ₀ s-principalThetaConstant/s)+
    principalThetaConstant)=(s-1)*(principalZetaPrefactor s*
      (principalIdealFEPair.Λ₀ s-(1/s)*principalThetaConstant-
        (1/(1-s))*principalThetaConstant))
  have h1s : 1-s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation of the actual zero-frequency scattering coefficient.
This does not assert continuation of the nonzero Fourier coefficients. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaConstantRegular (s : ℂ) : ℂ :=
  (2*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(2-3*s))/principalIdealZeta (3*s-2))*
    (principalZetaRegularFactor (3*s-3)/3)

lemma cubicThetaConstantRegular_analyticAt :
    AnalyticAt ℂ cubicThetaConstantRegular (4/3:ℂ) := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  have ha (a b : ℂ) : AnalyticAt ℂ (fun z : ℂ => a*z+b) (4/3:ℂ) := by fun_prop
  have hp (a b : ℂ) : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(a*z+b)) (4/3:ℂ) :=
    ((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp (f:=fun z : ℂ => a*z+b) (x:=(4/3:ℂ)) (ha a b)
  have hP : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(3-3*z)) (4/3:ℂ) := by
    have he : (fun z : ℂ => (3:ℂ)^(3-3*z))=(fun z : ℂ => (3:ℂ)^(-3*z+3)) := by
      funext z
      congr 1
      ring
    rw [he]
    exact hp (-3) 3
  have hQ : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(2-3*z)) (4/3:ℂ) := by
    have he : (fun z : ℂ => (3:ℂ)^(2-3*z))=(fun z : ℂ => (3:ℂ)^(-3*z+2)) := by
      funext z
      congr 1
      ring
    rw [he]
    exact hp (-3) 2
  have hZ : AnalyticAt ℂ (fun z : ℂ => principalIdealZeta (3*z-2)) (4/3:ℂ) := by
    have ho : AnalyticAt ℂ principalIdealZeta (3*(4/3:ℂ)-2) := by
      convert cubicTheta_principalZeta_analyticAt (s:=2) (by norm_num) (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    exact ho.comp (f:=fun z : ℂ => 3*z-2) (x:=(4/3:ℂ)) (by fun_prop)
  have hR : AnalyticAt ℂ (fun z : ℂ => principalZetaRegularFactor (3*z-3)) (4/3:ℂ) := by
    have ho : AnalyticAt ℂ principalZetaRegularFactor (3*(4/3:ℂ)-3) := by
      convert principalZetaRegularFactor_analyticAt_one using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    exact ho.comp (f:=fun z : ℂ => 3*z-3) (x:=(4/3:ℂ)) (by fun_prop)
  have hden : 1-(3:ℂ)^(2-3*(4/3:ℂ))≠0 := by
    norm_num [Complex.cpow_neg,Complex.cpow_ofNat]
  have hzne : principalIdealZeta (3*(4/3:ℂ)-2)≠0 := by
    convert cubicTheta_principalZeta_two_ne_zero using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  exact (((analyticAt_const.mul hP).div (analyticAt_const.sub hQ) hden).div hZ hzne).mul
    (hR.div analyticAt_const (by norm_num))

lemma cubicThetaConstantRegular_eq {s : ℂ} (hs0 : 3*s-3≠0) (hs1 : 3*s-3≠1) :
    cubicThetaConstantRegular s=(s-4/3)*cubicThetaConstantContinuation s := by
  rw [cubicThetaConstantRegular,principalZetaRegularFactor_eq hs0 hs1,
    cubicThetaConstantContinuation]
  ring

lemma cubicThetaConstantRegular_value :
    cubicThetaConstantRegular (4/3:ℂ)=
      (principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2) := by
  unfold cubicThetaConstantRegular
  norm_num [principalZetaRegularFactor_one,Complex.cpow_neg,Complex.cpow_ofNat]
  ring

theorem cubicThetaConstantContinuation_residue :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaConstantContinuation s) (𝓝[≠] (4/3:ℂ))
      (𝓝 ((principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2))) := by
  have h := cubicThetaConstantRegular_analyticAt.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ))
  rw [cubicThetaConstantRegular_value] at h
  apply h.congr'
  have hn : ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ), s≠1 :=
    (eventually_ne_nhds (by norm_num : (4/3:ℂ)≠1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with s hs hs'
  change s≠(4/3:ℂ) at hs'
  apply cubicThetaConstantRegular_eq
  · intro he
    apply hs
    linear_combination (1/3:ℂ)*he
  · intro he
    apply hs'
    linear_combination (1/3:ℂ)*he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded restriction from the completed global energy space to the
literal high cusp strip, extending all actual C1 finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.finiteEnergy_addCommGroup
lemma cubicThetaCuspRestriction_finiteEnergy (F : cubicThetaFiniteEnergySections) :
    cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding F)=cubicThetaFiniteCuspRestriction F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaFiniteCuspRestriction) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense cubicThetaFiniteCuspRestriction_energy_bound F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergySimplePole
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residue of the actual energy inverse. The complementary
inverse is analytic and the exceptional projection gives a simple pole. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaProjectedInverse_analytic {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    AnalyticAt ℂ (fun w : ℂ => Ring.inverse
      (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))) (z:ℂ) := by
  have hu := cubicThetaProjectedPencil_unit hz hz2
  have hi : AnalyticAt ℂ Ring.inverse
      (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
    convert analyticAt_inverse (𝕜:=ℂ)
      (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hu.unit using 1
    all_goals try with_reducible_and_instances rfl
    exact hu.unit_spec
  exact hi.comp (f:=fun w : ℂ => cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))
    (x:=(z:ℂ)) ((cubicThetaEnergyPencil_analytic (z:ℂ)).add analyticAt_const)

theorem cubicThetaEnergyInverse_residue {z : ℝ} (hz : 0<z) (hz2 : z<2) :
    Tendsto (fun w : ℂ => (w-(z:ℂ)) • Ring.inverse (cubicThetaEnergyPencil w))
      (𝓝[≠] (z:ℂ)) (𝓝 ((-(z:ℂ)) • cubicThetaExceptionalProjection (z:ℂ))) := by
  let _ : NormedRing (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  let _ : NormedAlgebra ℂ (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  let P : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
    cubicThetaExceptionalProjection (z:ℂ)
  let R : ℂ → (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := fun w : ℂ => Ring.inverse (cubicThetaEnergyPencil w+P)*(1-P)
  have hR : ContinuousAt R (z:ℂ) :=
    (cubicThetaProjectedInverse_analytic hz.le hz2).continuousAt.clm_comp continuousAt_const
  have hreg : Tendsto (fun w : ℂ => (w-(z:ℂ)) • R w)
      (𝓝[≠] (z:ℂ)) (𝓝 0) := by
    have ht : Tendsto (fun w : ℂ => w-(z:ℂ)) (𝓝[≠] (z:ℂ)) (𝓝 0) := by
      have hzero : ContinuousAt (fun w : ℂ => w-(z:ℂ)) (z:ℂ) :=
        continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hzero.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (z:ℂ)≤𝓝 (z:ℂ))
    have h := ht.smul (hR.tendsto.mono_left nhdsWithin_le_nhds)
    simpa only [sub_self,zero_smul] using h
  have hu := cubicThetaProjectedPencil_unit hz.le hz2
  have hevent : ∀ᶠ w : ℂ in 𝓝 (z:ℂ), IsUnit (cubicThetaEnergyPencil w+P) :=
    ((cubicThetaEnergyPencil_analytic (z:ℂ)).add analyticAt_const).continuousAt.eventually
      ((Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds hu)
  have he : (fun w : ℂ => (w-(z:ℂ)) • Ring.inverse (cubicThetaEnergyPencil w))=ᶠ[𝓝[≠] (z:ℂ)]
      (fun w => (w-(z:ℂ)) • R w+(-(z:ℂ)) • P) := by
    filter_upwards [nhdsWithin_le_nhds hevent,self_mem_nhdsWithin] with w hw hne
    have hn : w≠(z:ℂ) := hne
    rw [← cubicThetaLocalEnergyResolvent_eq_inverse hz.ne' hn hw]
    exact cubicThetaLocalEnergyResolvent_scaled hn
  have h := hreg.add (tendsto_const_nhds (x:=(-(z:ℂ)) • P))
  simpa only [zero_add] using h.congr' he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSpectralSimplePole
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the simple energy pole to the Eisenstein parameter.
The derivative factor is explicit and nonzero on the real interval (1,2). -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaSpectralEnergyInverse_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s)))
      (𝓝[≠] (σ:ℂ))
      (𝓝 ((cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)))) := by
  let _ : NormedRing (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  let _ : NormedAlgebra ℂ (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := inferInstance
  have hr := cubicThetaRealSpectralParameter_closedRange hσ hσ2
  have hz : ((1-σ*(σ-2):ℝ):ℂ)=cubicThetaGlobalSpectralParameter (σ:ℂ) := by
    simp only [cubicThetaGlobalSpectralParameter,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hp₀ := cubicThetaEnergyInverse_residue hr.1 hr.2
  rw [hz] at hp₀
  have hp := hp₀.comp (cubicThetaSpectralParameter_punctured hσ)
  have hden : ((σ:ℂ)+(σ:ℂ)-2)≠0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hre
    norm_num at hre
    linarith
  have hc : ContinuousAt (fun s : ℂ => -(s+(σ:ℂ)-2)⁻¹) (σ:ℂ) :=
    ((continuousAt_id.add continuousAt_const).sub continuousAt_const).inv₀ hden |>.neg
  have h := (hc.tendsto.mono_left nhdsWithin_le_nhds).smul hp
  have hnear : ∀ᶠ s : ℂ in 𝓝 (σ:ℂ), s+(σ:ℂ)-2≠0 :=
    ((continuousAt_id.add continuousAt_const).sub continuousAt_const).eventually_ne hden
  have he : (fun s : ℂ => -(s+(σ:ℂ)-2)⁻¹ •
      ((cubicThetaGlobalSpectralParameter s-cubicThetaGlobalSpectralParameter (σ:ℂ)) •
        Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s))))=ᶠ[𝓝[≠] (σ:ℂ)]
      (fun s : ℂ => (s-(σ:ℂ)) •
        Ring.inverse (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s))) := by
    filter_upwards [nhdsWithin_le_nhds hnear] with s hs
    exact spectral_rescale (σ:ℂ) s hs _
  have hcval : -((σ:ℂ)+(σ:ℂ)-2)⁻¹ •
      (-cubicThetaGlobalSpectralParameter (σ:ℂ) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)))=
      (cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)) •
        cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ)) := by
    have hc : -((σ:ℂ)+(σ:ℂ)-2)⁻¹*(-cubicThetaGlobalSpectralParameter (σ:ℂ))=
        cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ) := by
      have he : ((2*σ-2:ℝ):ℂ)=(σ:ℂ)+(σ:ℂ)-2 := by push_cast; ring
      rw [he,div_eq_mul_inv]
      ring
    exact (rescale_associative _ _ _).trans (congrArg (fun c : ℂ => c •
      cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ))) hc)
  rw [hcval] at h
  exact h.congr' he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

theorem cubicThetaForcedEnergy_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s))
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaArithmeticResidueEnergy σ)) := by
  have hA := cubicThetaSpectralEnergyInverse_residue_closed hσ hσ2
  have hF : Tendsto (fun s : ℂ => cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 s))
      (𝓝[≠] (σ:ℂ))
      (𝓝 (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ)))) :=
    (cubicThetaGlobalInclusion.adjoint.continuous.continuousAt.comp
      (cubicThetaForcingL2_analytic (σ:ℂ)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hc : Continuous (fun p :
      (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) × cubicThetaGlobalEnergySpace =>
      p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have h := (hc.tendsto _).comp (hA.prodMk_nhds hF)
  simpa only [Function.comp_def,smul_apply,cubicThetaContinuedEnergyLift,
    cubicThetaArithmeticResidueEnergy] using h

lemma cubicThetaArithmeticResidueEnergy_weak (σ : ℝ) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalEnergyGradient (cubicThetaArithmeticResidueEnergy σ))+
    ((σ:ℂ)*((σ:ℂ)-2))*inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))=0 := by
  have h := cubicThetaEnergyPencil_inner (cubicThetaGlobalSpectralParameter (σ:ℂ))
    v (cubicThetaArithmeticResidueEnergy σ)
  rw [cubicThetaArithmeticResidueEnergy_kernel,inner_zero_right] at h
  simpa only [cubicThetaGlobalSpectralParameter,sub_sub_cancel] using h.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic continuation restricted to the high cusp.
Both its meromorphic dependence and its initial pointwise representative
are retained in the L2 strip space. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaForcedEnergy_meromorphic {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (fun w => cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter w) (cubicThetaForcingL2 w)) s := by
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  have hA := (cubicThetaEnergyInverse_meromorphic
    (cubicThetaGlobalSpectralParameter_below_threshold hs)).comp_analyticAt hp
  have hF : AnalyticAt ℂ (fun w => cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 w)) s :=
    (cubicThetaGlobalInclusion.adjoint.analyticAt _).comp (f:=cubicThetaForcingL2) (x:=s)
      (cubicThetaForcingL2_analytic s)
  exact cubicThetaMeromorphic_apply hA hF

theorem cubicThetaForcedCusp_meromorphic {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt cubicThetaForcedCusp s :=
  cubicThetaMeromorphic_clm cubicThetaCuspRestriction (cubicThetaForcedEnergy_meromorphic hs)

lemma cubicThetaForcedCusp_right {s : ℂ} (hs : 3 < s.re) :
    cubicThetaForcedCusp s=cubicThetaFiniteCuspRestriction (cubicThetaArithmeticFiniteEnergy s hs) := by
  rw [cubicThetaForcedCusp,← cubicThetaArithmeticEnergy_eq_continued hs,
    ← cubicThetaArithmeticFiniteEnergy_embedding s hs,cubicThetaCuspRestriction_finiteEnergy]

lemma cubicThetaForcedCusp_coe {s : ℂ} (hs : 3 < s.re) :
    cubicThetaForcedCusp s =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)]
      (fun p => cubicThetaArithmeticRemainder p.val s) := by
  rw [cubicThetaForcedCusp_right hs]
  exact (cubicThetaFiniteEnergy_strip_memLp (cubicThetaArithmeticFiniteEnergy s hs)).coeFn_toLp

theorem cubicThetaForcedCusp_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedCusp s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))) := by
  have h := (cubicThetaCuspRestriction.continuous.tendsto _).comp
    (cubicThetaForcedEnergy_residue_closed hσ hσ2)
  simpa only [Function.comp_def,map_smul,cubicThetaForcedCusp] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded L2 observations of the actual continued cusp restriction.
Their initial values and residues are genuine hyperbolic strip integrals. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaCuspObservable_meromorphic (T : CubicThetaStripL2)
    {s : ℂ} (hs : 1 < s.re) : MeromorphicAt (cubicThetaCuspObservable T) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ T) (cubicThetaForcedCusp_meromorphic hs)

lemma cubicThetaCuspObservable_right (T : CubicThetaStripL2)
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCuspObservable T s=
      ∫ p in cubicThetaCuspStrip 2, star (T p)*cubicThetaArithmeticRemainder p.val s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaCuspObservable,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cubicThetaForcedCusp_coe hs] with p hp
  rw [hp,RCLike.inner_apply]
  simp only [starRingEnd_apply]
  ring

theorem cubicThetaCuspObservable_residue_closed (T : CubicThetaStripL2)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspObservable T s)
      (𝓝[≠] (σ:ℂ))
      (𝓝 (inner ℂ T (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ)))) := by
  have h := ((innerSL ℂ T).continuous.tendsto _).comp (cubicThetaForcedCusp_residue_closed hσ hσ2)
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,cubicThetaCuspObservable] using h

theorem cubicThetaCuspObservable_residue (T : CubicThetaStripL2)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspObservable T s)
      (𝓝[≠] (σ:ℂ))
      (𝓝 (inner ℂ T (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ)))) :=
  cubicThetaCuspObservable_residue_closed T hσ hσ2.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaCuspFourierObservable_meromorphic (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 1 < s.re) : MeromorphicAt (cubicThetaCuspFourierObservable h W) s :=
  cubicThetaCuspObservable_meromorphic _ hs

lemma cubicThetaCuspFourierObservable_right (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCuspFourierObservable h W s=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaArithmeticRemainder p.val s ∂cubicThetaPointMeasure := by
  rw [cubicThetaCuspFourierObservable,cubicThetaCuspObservable_right _ hs]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp] with p hp
  change star (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)*_=_
  rw [hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolutely convergent evaluation of the genuine weighted cusp observations. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaCuspFourier_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaArithmeticRemainder p.val s)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W) (cubicThetaForcedCusp s)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    cubicThetaForcedCusp_coe hs] with p hp hR
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) _=_
  rw [hp,hR,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaCuspFourierObservable_iterated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCuspFourierObservable h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticRemainder (z,v) s := by
  rw [cubicThetaCuspFourierObservable_right h W hs]
  have hf := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaArithmeticRemainder y s) (cubicThetaCuspFourier_integrable h W hs)
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaArithmeticRemainder p.val s ∂cubicThetaPointMeasure)=_ at hf
  rw [hf]
  apply integral_congr_ae
  filter_upwards with v
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [star_mul]
  ring

lemma cubicThetaCuspFourierObservable_coefficient {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCuspFourierObservable h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^3*
        ((9*Real.sqrt 3/2:ℝ) •
          (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
            cubicThetaNonzeroFrequencyTerm (0,v) s h)) := by
  rw [cubicThetaCuspFourierObservable_iterated h W hs]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaArithmetic_horizontal_coefficient hv.le (by linarith) hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the actual weighted arithmetic Fourier coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaCuspFourierObservable_normalized {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCuspFourierObservable h W s=
      ((Real.pi:ℂ)/Complex.Gamma s)*cubicThetaFrequencyDirichlet h s*
        cubicThetaFourierRadialTest h W s := by
  rw [cubicThetaCuspFourierObservable_coefficient hh W hs,cubicThetaFourierRadialTest,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  have hphase : (Real.fourierChar (tracePair 0 (cubicThetaRowFrequency h)):ℂ)=1 := by
    simp [tracePair]
  simp only [cubicThetaNonzeroFrequencyTerm,ite_eq_right hh,hphase,mul_one,Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))*
        (star (W v)*(v:ℂ)^s*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3)/
            Complex.Gamma s*cubicThetaFrequencyDirichlet h s := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaFrequencyQuotient_meromorphic {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) : MeromorphicAt (cubicThetaFrequencyQuotient h) s := by
  exact ((cubicThetaGamma_analytic_right (by linarith)).meromorphicAt.mul
    (cubicThetaCuspFourierObservable_meromorphic h cubicThetaRadialTestWeight hs)).div
      ((MeromorphicAt.const (Real.pi:ℂ) s).mul
        ((cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).analyticAt s).meromorphicAt)

lemma cubicThetaFrequencyQuotient_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3 < s.re)
    (hR : cubicThetaFourierRadialTest h cubicThetaRadialTestWeight s≠0) :
    cubicThetaFrequencyQuotient h s=cubicThetaFrequencyDirichlet h s := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  rw [cubicThetaFrequencyQuotient,cubicThetaCuspFourierObservable_normalized hh _ hs]
  field_simp

theorem cubicThetaFrequencyContinuation_meromorphic {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) : MeromorphicAt (cubicThetaFrequencyContinuation h) s := by
  by_cases hs3 : 3 < s.re
  · have hd : DifferentiableOn ℂ (cubicThetaFrequencyDirichlet h) {z : ℂ | 2<z.re} :=
      fun z hz => (cubicThetaFrequencyDirichlet_differentiableAt h hz).differentiableWithinAt
    have ha := hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 2 < s.re by linarith))
    apply ha.meromorphicAt.congr
    have hn : ∀ᶠ z in 𝓝 s, 3<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs3
    filter_upwards [nhdsWithin_le_nhds hn] with z hz
    exact (cubicThetaFrequencyContinuation_right h hz).symm
  · apply (cubicThetaFrequencyQuotient_meromorphic hh hs).congr
    filter_upwards [cubicThetaRadialTest_eventually_ne_zero hh s] with z hz
    unfold cubicThetaFrequencyContinuation
    split_ifs with hz3
    · exact cubicThetaFrequencyQuotient_right hh hz3 hz
    · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMeromorphicIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identity propagation for the actual meromorphic coefficient observations. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaCuspFourierObservable_continued {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaCuspFourierObservable h W =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaFourierRadialTest h W z) := by
  have hobs : MeromorphicOn (cubicThetaCuspFourierObservable h W) {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaCuspFourierObservable_meromorphic h W hz
  have hrhs : MeromorphicOn (fun z =>
      ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaFourierRadialTest h W z) {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt).mul
        (cubicThetaFrequencyContinuation_meromorphic hh hz)).mul
          ((cubicThetaFourierRadialTest_entire hh W).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hobs hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right h hz]
  exact cubicThetaCuspFourierObservable_normalized hh W hz

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic coefficient residue is a genuine Fourier observation
of the finite-rank spectral residue. No theta coefficient is assumed. -/
noncomputable section
open Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_residue {h : Eisenstein} (hh : h≠0)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaFrequencyContinuation h s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaArithmeticFourierResidue h σ)) := by
  have hG : ContinuousAt Complex.Gamma (σ:ℂ) :=
    (cubicThetaGamma_analytic_right (by simpa using lt_trans zero_lt_one hσ)).continuousAt
  have hR := (cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).continuous.continuousAt
    (x:=(σ:ℂ))
  have hRn : cubicThetaFourierRadialTest h cubicThetaRadialTestWeight (σ:ℂ)≠0 := by
    intro hz
    have hp := cubicThetaFourierRadialTest_real_pos hh σ
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hfactor : ContinuousAt (fun s : ℂ => Complex.Gamma s/
      ((Real.pi:ℂ)*cubicThetaFourierRadialTest h cubicThetaRadialTestWeight s)) (σ:ℂ) :=
    hG.div (continuousAt_const.mul hR) (mul_ne_zero hπ hRn)
  have ht := (hfactor.tendsto.mono_left nhdsWithin_le_nhds).mul
    (cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest h cubicThetaRadialTestWeight) hσ hσ2)
  apply ht.congr'
  have hn : ∀ᶠ s in 𝓝 (σ:ℂ), s.re<3 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simp; linarith)
  filter_upwards [nhdsWithin_le_nhds hn] with s hs
  simp only [cubicThetaFrequencyContinuation,ite_eq_right (not_lt.mpr hs.le),
    cubicThetaFrequencyQuotient,cubicThetaCuspFourierObservable]
  ring

theorem cubicThetaResidue_fourier_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    inner ℂ (cubicThetaCuspFourierTest h W)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))=
      ((Real.pi:ℂ)/Complex.Gamma (σ:ℂ))*cubicThetaArithmeticFourierResidue h σ*
        cubicThetaFourierRadialTest h W σ := by
  have hG : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/Complex.Gamma s) (σ:ℂ) :=
    continuousAt_const.div
      (cubicThetaGamma_analytic_right (by simpa using lt_trans zero_lt_one hσ)).continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using lt_trans zero_lt_one hσ))
  have hW := (cubicThetaFourierRadialTest_entire hh W).continuous.continuousAt (x:=(σ:ℂ))
  have ht := ((hG.tendsto.mono_left nhdsWithin_le_nhds).mul
    (cubicThetaFrequencyContinuation_residue hh hσ hσ2)).mul
      (hW.tendsto.mono_left nhdsWithin_le_nhds)
  have ho := cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest h W) hσ hσ2
  apply tendsto_nhds_unique ho
  apply ht.congr'
  filter_upwards [cubicThetaCuspFourierObservable_continued hh W (by simpa using hσ)] with s hs
  change cubicThetaCuspObservable (cubicThetaCuspFourierTest h W) s=_ at hs
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaCuspZeroObservable_normalized (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaCuspFourierObservable 0 W s=
      ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*cubicThetaZeroRadialTest W s := by
  rw [cubicThetaCuspFourierObservable_iterated 0 W hs,cubicThetaZeroRadialTest,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  rw [cubicThetaArithmetic_horizontal_zero hv.le (by linarith),
    cubicThetaEisensteinConstantMode_eq (by linarith) (by linarith),
    add_sub_cancel_left,cubicThetaConstantContinuation_right (by linarith),Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))/(s-1)*
        cubicThetaConstantContinuation s*(star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3) := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScatteringRegular
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In Re(s)>1 the explicit scattering coefficient has no possible pole
except s=4/3. The denominator is controlled by its convergent Euler product. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaConstantContinuation_regular {s : ℂ} (hs : 1 < s.re)
    (hne : s≠4/3) : AnalyticAt ℂ cubicThetaConstantContinuation s := by
  have hlin : 1<(3*s-2).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero]
    linarith
  have hnum0 : 3*s-3≠0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero,Complex.zero_re] at he
    linarith
  have hnum1 : 3*s-3≠1 := by
    intro hz
    apply hne
    linear_combination (1/3:ℂ)*hz
  have hden0 : 3*s-2≠0 := by
    intro hz
    rw [hz,Complex.zero_re] at hlin
    linarith
  have hden1 : 3*s-2≠1 := by
    intro hz
    rw [hz,Complex.one_re] at hlin
    linarith
  have hZn : AnalyticAt ℂ (fun z : ℂ => principalIdealZeta (3*z-3)) s :=
    (cubicTheta_principalZeta_analyticAt hnum0 hnum1).comp
      (f:=fun z : ℂ => 3*z-3) (x:=s) (by fun_prop)
  have hZd : AnalyticAt ℂ (fun z : ℂ => principalIdealZeta (3*z-2)) s :=
    (cubicTheta_principalZeta_analyticAt hden0 hden1).comp
      (f:=fun z : ℂ => 3*z-2) (x:=s) (by fun_prop)
  change AnalyticAt ℂ (fun z => (2*(3:ℂ)^(3-3*z)/(1-(3:ℂ)^(2-3*z)))*
    principalIdealZeta (3*z-3)/principalIdealZeta (3*z-2)) s
  exact ((((analyticAt_const.mul (cubicThetaRamifiedPower_analytic 3 s)).div
    (analyticAt_const.sub (cubicThetaRamifiedPower_analytic 2 s))
      (cubicThetaScattering_local_denominator hs)).mul hZn).div hZd
        (cubicTheta_principalZeta_right_ne_zero hlin))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial windows supported above height two retain the exact
constant-mode continuation. They will test the high annular forcing. -/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaCuspZeroWindow_continued (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaCuspFourierObservable 0 W =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*
        cubicThetaZeroRadialTest W z) := by
  have ho : MeromorphicOn (cubicThetaCuspFourierObservable 0 W) {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaCuspFourierObservable_meromorphic 0 W hz
  have hr : MeromorphicOn (fun z => ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*
      cubicThetaZeroRadialTest W z) {z : ℂ | 1<z.re} := by
    intro z _
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (analyticAt_id.sub analyticAt_const).meromorphicAt).mul
        (cubicThetaConstantContinuation_meromorphic z)).mul
          ((cubicThetaZeroRadialWindow_entire W hW).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity ho hr (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  exact cubicThetaCuspZeroObservable_normalized W hz

theorem cubicThetaSpectralResidue_window_zero_closed (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))=0 := by
  have hs1 : (σ:ℂ)-1≠0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  have hc : ContinuousAt (fun s : ℂ => ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*
      cubicThetaZeroRadialTest W s) (σ:ℂ) :=
    ((continuousAt_const.div (continuousAt_id.sub continuousAt_const) hs1).mul
      (cubicThetaConstantContinuation_regular (by simpa using hσ) hne).continuousAt).mul
        ((cubicThetaZeroRadialWindow_entire W hW).continuous.continuousAt (x:=(σ:ℂ)))
  have hs : Tendsto (fun s : ℂ => s-(σ:ℂ)) (𝓝[≠] (σ:ℂ)) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ => s-(σ:ℂ)) (σ:ℂ) :=
      continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun s : ℂ => (s-(σ:ℂ))*cubicThetaCuspFourierObservable 0 W s)
      (𝓝[≠] (σ:ℂ)) (𝓝 0) := by
    have hprod := hs.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
    simp only [zero_mul] at hprod
    apply hprod.congr'
    filter_upwards [cubicThetaCuspZeroWindow_continued W hW (by simpa using hσ)] with s hs
    rw [hs]
  exact tendsto_nhds_unique (cubicThetaCuspObservable_residue_closed
    (cubicThetaCuspFourierTest 0 W) hσ hσ2) ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaHighWindowPairing_energy (s : ℂ) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
        (cubicThetaCuspRestriction u) := by
  have hc : IsClosed {v : cubicThetaGlobalEnergySpace |
      inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaGlobalInclusion v)=
        inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
          (cubicThetaCuspRestriction v)} := isClosed_eq
    (continuous_const.inner cubicThetaGlobalInclusion.continuous)
    (continuous_const.inner cubicThetaCuspRestriction.continuous)
  have hr : range cubicThetaFiniteEnergyEmbedding⊆
      {v : cubicThetaGlobalEnergySpace |
        inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaGlobalInclusion v)=
          inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
            (cubicThetaCuspRestriction v)} := by
    rintro v ⟨F,rfl⟩
    change inner ℂ (cubicThetaHighWindowL2 s)
      (cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F))=_
    rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaCuspRestriction_finiteEnergy]
    exact cubicThetaHighWindowPairing_finiteEnergy s F
  exact (closure_minimal hr hc) (cubicThetaFiniteEnergyEmbedding_dense u)

theorem cubicThetaHighWindowPairing_residue_zero_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaHighWindowL2 σ)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))=0 := by
  rw [cubicThetaHighWindowPairing_energy]
  exact cubicThetaSpectralResidue_window_zero_closed (cubicThetaHighWindowWeight σ)
    (fun _ hv => cubicThetaHighWindowForcing_low σ hv) hσ hσ2 hne

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

lemma cubicThetaWindow_forcing_balance (σ : ℝ) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaHighWindowL2 σ) := by
  have hR := cubicThetaArithmeticResidueEnergy_weak σ
    (cubicThetaGlobalEnergyTest (cubicThetaIncomingWindowTest σ))
  rw [cubicThetaGlobalInclusion_test,cubicThetaGlobalEnergyGradient_test] at hR
  have hR' := congrArg (starRingEnd ℂ) hR
  simp only [map_add,map_mul,map_sub,map_zero,map_ofNat,inner_conj_symm,
    Complex.conj_ofReal] at hR'
  have hW := cubicThetaWindow_global_weak σ (cubicThetaArithmeticResidueEnergy σ)
  have hz : inner ℂ (cubicThetaGlobalEnergyGradient (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaGlobalGradient (cubicThetaIncomingWindowTest σ))+
      (σ:ℂ)*((σ:ℂ)-2)*inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
        (cubicThetaGlobalMass (cubicThetaIncomingWindowTest σ))=0 := by
    linear_combination hR'
  rw [hz,inner_sub_right] at hW
  exact (sub_eq_zero.mp hW.symm).symm

lemma cubicThetaResidue_forcing_orthogonal_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=0 := by
  rw [cubicThetaWindow_forcing_balance]
  have h := cubicThetaHighWindowPairing_residue_zero_closed hσ hσ2 hne
  rw [← inner_conj_symm, h, map_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueVanishing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact incoming window kills every spurious real residue of the
actual arithmetic family: only the theta parameter can contribute. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidueEnergy_vanishes_closed {σ : ℝ}
    (hσ : 1<σ) (hσ2 : σ≤2) (hne : (σ:ℂ)≠4/3) :
    cubicThetaArithmeticResidueEnergy σ=0 :=
  cubicThetaArithmeticResidueEnergy_eq_zero_of_orthogonal σ
    (cubicThetaResidue_forcing_orthogonal_closed hσ hσ2 hne)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEndpointRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint s=2 is included: the actual residue and its arithmetic
Fourier observations are removable there as well. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaForcedEnergy_removable_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2)
    (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → cubicThetaGlobalEnergySpace, AnalyticAt ℂ g (σ:ℂ) ∧
      (fun s => cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s)
        (cubicThetaForcingL2 s))=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  apply cubicThetaSimpleResidue_removable (cubicThetaForcedEnergy_meromorphic (by simpa using hσ))
  have ht := cubicThetaForcedEnergy_residue_closed hσ hσ2
  rwa [cubicThetaArithmeticResidueEnergy_vanishes_closed hσ hσ2 hne] at ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticPoleIsolation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic family has an analytic germ throughout Re(s)>1,
except for its already proved nonzero pole at 4/3. The representative supplied
by the inverse operator can differ at an isolated singular parameter. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaForcedEnergy_analytic_germ {s : ℂ} (hs : 1 < s.re)
    (hne : s≠4/3) :
    ∃ g : ℂ → cubicThetaGlobalEnergySpace, AnalyticAt ℂ g s ∧
      (fun z => cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter z)
        (cubicThetaForcingL2 z))=ᶠ[𝓝[≠] s] g := by
  by_cases hr : s.im≠0 ∨ 2 < s.re
  · exact ⟨_,cubicThetaForcedEnergy_analytic_regular hs hr,Filter.EventuallyEq.rfl⟩
  · have hi : s.im=0 := not_not.mp (not_or.mp hr).1
    have hle : s.re≤2 := le_of_not_gt (not_or.mp hr).2
    have he : (s.re:ℂ)=s := Complex.ext rfl (by simpa using hi.symm)
    simpa only [he] using cubicThetaForcedEnergy_removable_closed hs hle (he.symm ▸ hne)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierPoleIsolation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continued arithmetic Fourier coefficient has no artificial poles
from the initial fixed radial test. Its only possible pole in Re(s)>1
is the actual arithmetic pole at 4/3. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_analytic_germ {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) (hne : s≠4/3) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q s ∧
      cubicThetaFrequencyContinuation h=ᶠ[𝓝[≠] s] q := by
  obtain ⟨W,_,hW⟩ := cubicThetaComplexRadialTest_nonzero hh hs
  obtain ⟨g,hg,he⟩ := cubicThetaForcedEnergy_analytic_germ hs hne
  let L : cubicThetaGlobalEnergySpace →L[ℂ] ℂ :=
    (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp cubicThetaCuspRestriction
  let R := cubicThetaFourierRadialTest h W
  have hR : AnalyticAt ℂ R s := (cubicThetaFourierRadialTest_entire hh W).analyticAt s
  have hRn : R s≠0 := hW
  have hG := cubicThetaGamma_analytic_right (s:=s) (by linarith)
  have hGn := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hL : AnalyticAt ℂ (fun z => L (g z)) s :=
    (L.analyticAt (g s)).comp (f:=g) (x:=s) hg
  refine ⟨fun z => Complex.Gamma z/((Real.pi:ℂ)*R z)*L (g z),
    (hG.div (analyticAt_const.mul hR) (mul_ne_zero hπ hRn)).mul hL,?_⟩
  have hr : ∀ᶠ z in 𝓝 s, R z≠0 := hR.continuousAt.eventually_ne hRn
  have hγ : ∀ᶠ z in 𝓝 s, Complex.Gamma z≠0 := hG.continuousAt.eventually_ne hGn
  filter_upwards [cubicThetaCuspFourierObservable_continued hh W hs,he,
    nhdsWithin_le_nhds hr,nhdsWithin_le_nhds hγ] with z hz heg hrz hgz
  change inner ℂ (cubicThetaCuspFourierTest h W)
    (cubicThetaCuspRestriction (cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter z) (cubicThetaForcingL2 z)))=_ at hz
  rw [heg] at hz
  change L (g z)=((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*R z at hz
  rw [hz]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRegularizedFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single holomorphic representative of the pole-cleared arithmetic
Fourier coefficient on Re(s)>1, including its actual residue value. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaClearedFrequency_meromorphic {h : Eisenstein} (hh : h≠0) :
    MeromorphicOn (fun s => (s-4/3)*cubicThetaFrequencyContinuation h s) {s : ℂ | 1 < s.re} := by
  intro s hs
  exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
    (cubicThetaFrequencyContinuation_meromorphic hh hs)

theorem cubicThetaRegularizedFrequency_analytic {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedFrequency h) {s : ℂ | 1 < s.re} := by
  apply regularized_analytic (cubicThetaClearedFrequency_meromorphic hh)
  intro s hs
  by_cases he : s=4/3
  · subst s
    have ht := cubicThetaFrequencyContinuation_residue hh (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,smul_eq_mul] at ht
    have hf := cubicThetaClearedFrequency_meromorphic hh (4/3) (by norm_num)
    exact hf.meromorphicOrderAt_nonneg_iff.mp
      ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).mp ⟨_,ht⟩)
  · obtain ⟨g,hg,hfg⟩ := cubicThetaFrequencyContinuation_analytic_germ hh hs he
    refine ⟨fun z => (z-4/3)*g z,(analyticAt_id.sub analyticAt_const).mul hg,?_⟩
    filter_upwards [hfg] with z hz
    rw [hz]

theorem cubicThetaRegularizedFrequency_germ {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) :
    cubicThetaRegularizedFrequency h=ᶠ[𝓝[≠] s]
      (fun z => (z-4/3)*cubicThetaFrequencyContinuation h z) :=
  (cubicThetaClearedFrequency_meromorphic hh).toMeromorphicNFOn_eq_self_on_nhdsNE hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeFreeContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic continuation of the pole-cleared square-class twist,
constructed from the actual arithmetic Fourier family. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaRegularizedFrequency_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRegularizedFrequency h s=(s-4/3)*cubicThetaFrequencyDirichlet h s := by
  have hs1 : 1 < s.re := by linarith
  have hleft := (cubicThetaRegularizedFrequency_analytic hh s hs1).continuousAt
  have hright : ContinuousAt (fun z : ℂ => (z-4/3)*cubicThetaFrequencyDirichlet h z) s :=
    (continuousAt_id.sub continuousAt_const).mul
      (cubicThetaFrequencyDirichlet_differentiableAt h (by linarith)).continuousAt
  have hn : ∀ᶠ z : ℂ in 𝓝 s, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have he : cubicThetaRegularizedFrequency h=ᶠ[𝓝[≠] s]
      (fun z => (z-4/3)*cubicThetaFrequencyDirichlet h z) := by
    filter_upwards [cubicThetaRegularizedFrequency_germ hh hs1,nhdsWithin_le_nhds hn]
      with z hz hz3
    rw [hz,cubicThetaFrequencyContinuation_right _ hz3]
  exact tendsto_nhds_unique ((hleft.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hright.tendsto.mono_left nhdsWithin_le_nhds)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergyOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cubed-prime Hecke correspondence on the completed global
energy space. The extension is determined by its literal action
on the dense finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaCubeFinite_addGroup
lemma cubicThetaPrimeCubeHeckeRawEnergy_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaPrimeCubeHeckeRawEnergy hp F‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyEmbedding F‖^2 := by
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq]
  change ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F)‖^2+
      ‖cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp F)‖^2≤
    ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*
      (‖cubicThetaFiniteEnergyValue F‖^2+‖cubicThetaFiniteEnergyGradient F‖^2)
  calc
    _ ≤ ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyValue F‖^2+
        ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyGradient F‖^2 :=
      add_le_add (cubicThetaPrimeCubeHeckeFinite_value_bound hp F)
        (cubicThetaPrimeCubeHeckeFinite_gradient_bound hp F)
    _ = _ := by ring

lemma cubicThetaPrimeCubeHeckeRawEnergy_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaPrimeCubeHeckeRawEnergy hp F‖≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  apply _root_.le_of_sq_le_sq _ (mul_nonneg (Nat.cast_nonneg _) (_root_.norm_nonneg _))
  simpa only [mul_pow] using cubicThetaPrimeCubeHeckeRawEnergy_norm_sq hp F

lemma cubicThetaPrimeCubeHeckeEnergy_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeHeckeEnergy hp (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaPrimeCubeHeckeRawEnergy hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeCubeHeckeRawEnergy hp) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense
    ⟨((cubicThetaPrimeIwahori (p^3)).index:ℝ),cubicThetaPrimeCubeHeckeRawEnergy_bound hp⟩ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionFiniteCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion on finite-energy sections agrees with the
already constructed involution on the completed global energy space. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.inversionFinite_addGroup
lemma cubicThetaInversionFiniteExtension_eq (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInversionFiniteExtension u=cubicThetaInversionEnergy u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq cubicThetaInversionFiniteExtension.continuous cubicThetaInversionEnergy.continuous) ?_
  intro F
  change cubicThetaInversionFiniteExtension (cubicThetaGlobalEnergyTest F)=_
  rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaInversionFiniteExtension_finite]
  change cubicThetaInversionRawEnergy (cubicThetaSmoothToFiniteEnergy F)=
    cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F)
  rw [cubicThetaInversionEnergy_test]
  rfl

theorem cubicThetaInversionEnergy_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaFiniteEnergyEmbedding (cubicThetaInversionFinite F) := by
  rw [←cubicThetaInversionFiniteExtension_eq,cubicThetaInversionFiniteExtension_finite]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric inversion on the actual automorphic mass completion. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.inversionMass_smoothGroup
lemma cubicThetaInversionSmooth_mass_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalMassClosure (cubicThetaInversionSmooth F)‖=
      ‖cubicThetaGlobalMassClosure F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  exact cubicThetaInversion_test_mass_norm F

def cubicThetaInversionMass : cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaAutomorphicL2 :=
  (cubicThetaGlobalMassClosure.comp cubicThetaInversionSmoothLinear).extendOfIsometry
    cubicThetaGlobalMassClosure_dense cubicThetaInversionSmooth_mass_norm

lemma cubicThetaInversionMass_smooth (F : cubicThetaSmoothTests) :
    cubicThetaInversionMass (cubicThetaGlobalMassClosure F)=
      cubicThetaGlobalMassClosure (cubicThetaInversionSmooth F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverted-cusp scalar coefficient has the same residue as the
principal cusp. This assertion concerns scalar scattering coefficients;
it does not identify the nonconstant automorphic residues. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaInvertedConstantContinuation_factor (s : ℂ) :
    cubicThetaInvertedConstantContinuation s=
      cubicThetaInvertedScatteringFactor s*cubicThetaConstantContinuation s := by
  have hpow : (3:ℂ)^(3*s-3)*(3:ℂ)^(3-3*s)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0),show 3*s-3+(3-3*s)=0 by ring]
    simp
  unfold cubicThetaInvertedConstantContinuation cubicThetaInvertedScatteringFactor
    cubicThetaConstantContinuation
  symm
  calc
    _ = (((3:ℂ)^(3*s-3)*(3:ℂ)^(3-3*s)-(3:ℂ)^(3-3*s))/
        (1-(3:ℂ)^(2-3*s)))*principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2) := by ring
    _ = _ := by rw [hpow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedLowContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue the literal three low ramified rows by the cubic
identity. Their value at the pole is kept as a residue difference. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaRegularizedRamifiedLow_analytic {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedRamifiedLow h) {s : ℂ | 1 < s.re} := by
  intro s hs
  exact (cubicThetaRegularizedFrequency_analytic
    (mul_ne_zero (pow_ne_zero 3 lambdaE_prime.ne_zero) hh) s hs).sub
      ((cubicThetaRamifiedCubeFactor_analytic s).mul
        (cubicThetaRegularizedFrequency_analytic hh s hs))

theorem cubicThetaRegularizedRamifiedLow_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRegularizedRamifiedLow h s=(s-4/3)*cubicThetaRamifiedLowDirichlet s h := by
  unfold cubicThetaRegularizedRamifiedLow cubicThetaRamifiedCubeFactor
  rw [cubicThetaRegularizedFrequency_right
    (mul_ne_zero (pow_ne_zero 3 lambdaE_prime.ne_zero) hh) hs,
    cubicThetaRegularizedFrequency_right hh hs,
    cubicThetaFrequencyDirichlet_ramified_cube (by linarith)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimaryContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue the actual middle primary twist by dividing the explicit
ramified correction. Its residue is derived from actual Fourier residues. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaRegularizedPrimaryOne_analytic {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimaryOne h) {s : ℂ | 1 < s.re} := by
  intro s hs
  exact (cubicThetaRegularizedRamifiedLow_analytic hh s hs).div
    ((cubicThetaRamifiedCubeFactor_analytic s).mul analyticAt_const)
    (mul_ne_zero (cubicThetaRamifiedCubeFactor_ne_zero s) (cubicThetaRamifiedTrace_ne_zero h))

theorem cubicThetaRegularizedPrimaryOne_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRegularizedPrimaryOne h s=(s-4/3)*cubicThetaPrimaryFourierSeries 1 1 s h := by
  unfold cubicThetaRegularizedPrimaryOne
  rw [cubicThetaRegularizedRamifiedLow_right hh hs,cubicThetaRamifiedLowDirichlet_factor]
  have hq := cubicThetaRamifiedCubeFactor_ne_zero s
  have ht := cubicThetaRamifiedTrace_ne_zero h
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded global observation of the inverted Eisenstein series.
The literal strip integral is evaluated by the previously proved physical mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInvertedWindowObservable_meromorphic {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt cubicThetaInvertedWindowObservable s :=
  cubicThetaArithmeticDistribution_meromorphic _ cubicThetaInvertedWindowTest.property.2 hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Fourier observations at the inverted cusp, with their
literal initial values and the now identified full spectral residue. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaInvertedForcedCusp (s : ℂ) : CubicThetaStripL2 :=
  cubicThetaCuspRestriction (cubicThetaInversionEnergy (cubicThetaContinuedEnergyLift
    (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)))

def cubicThetaInvertedCuspObservable (T : CubicThetaStripL2) (s : ℂ) : ℂ :=
  inner ℂ T (cubicThetaInvertedForcedCusp s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

def cubicThetaInvertedFourierObservable (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  cubicThetaInvertedCuspObservable (cubicThetaCuspFourierTest h W) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfilePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact radial Poincaré profile supported above two pairs with the
actual constant cusp observation, including on the completed energy space. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaRadialProfilePairing_energy (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaCuspFourierTest 0 (W))
        (cubicThetaCuspRestriction u) := by
  have hc : IsClosed {v : cubicThetaGlobalEnergySpace |
      inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaGlobalInclusion v)=
        inner ℂ (cubicThetaCuspFourierTest 0 (W))
          (cubicThetaCuspRestriction v)} := isClosed_eq
    (continuous_const.inner cubicThetaGlobalInclusion.continuous)
    (continuous_const.inner cubicThetaCuspRestriction.continuous)
  have hr : range cubicThetaFiniteEnergyEmbedding⊆
      {v : cubicThetaGlobalEnergySpace |
        inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaGlobalInclusion v)=
          inner ℂ (cubicThetaCuspFourierTest 0 (W))
            (cubicThetaCuspRestriction v)} := by
    rintro v ⟨F,rfl⟩
    change inner ℂ (cubicThetaRadialProfileL2 W hW)
      (cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F))=_
    rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaCuspRestriction_finiteEnergy]
    exact cubicThetaRadialProfilePairing_finiteEnergy W hW F
  exact (closure_minimal hr hc) (cubicThetaFiniteEnergyEmbedding_dense u)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindowKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaKernel_long_window_balance (H : ℝ) (hH : 2≤H)
    (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 (4/3))=
      inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaRadialProfileL2 (cubicThetaLongForcingWeight H (by linarith) (4/3))
          (cubicThetaLongForcingWeight_low_two hH (4/3))) := by
  have hR := cubicThetaEnergyPencil_inner (cubicThetaGlobalSpectralParameter (4/3:ℂ))
    (cubicThetaGlobalEnergyTest (cubicThetaLongWindowTest H hH (4/3))) v
  rw [hv,inner_zero_right,cubicThetaGlobalInclusion_test,cubicThetaGlobalEnergyGradient_test] at hR
  have hR' := congrArg (starRingEnd ℂ) hR
  simp only [map_add,map_mul,map_sub,map_zero,map_one,map_ofNat,inner_conj_symm,
    cubicThetaGlobalSpectralParameter] at hR'
  norm_num [starRingEnd_apply] at hR'
  have hW := cubicThetaLongWindow_global_weak H hH (4/3) v
  have hz : inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalGradient (cubicThetaLongWindowTest H hH (4/3)))+
      (4/3:ℂ)*((4/3:ℂ)-2)*inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalMass (cubicThetaLongWindowTest H hH (4/3)))=0 := by
    norm_num at hR' ⊢
    linear_combination -hR'
  rw [hz,inner_sub_right] at hW
  exact (sub_eq_zero.mp hW.symm).symm

theorem cubicThetaResidue_long_kernel_pairing (H : ℝ) (hH : 2≤H)
    (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3))=
      (17/6:ℂ)*star (inner ℂ
        (cubicThetaCuspFourierTest 0 (cubicThetaLongForcingWeight H (by linarith) (4/3)))
        (cubicThetaCuspRestriction v)) := by
  rw [cubicThetaResidue_kernel_pairing v hv,cubicThetaKernel_long_window_balance H hH v hv,
    ←inner_conj_symm,cubicThetaRadialProfilePairing_energy]
  norm_num [cubicThetaGlobalSpectralParameter]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Hecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The C1 trace is the literal cubed-prime Hecke operator, and its
three geometric pullbacks have the required finite gradient integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Hecke_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaPointC1Hecke hp (cubicThetaSectionPointC1 F hF)=
      cubicThetaSectionPointC1 (cubicThetaPrimeCubeHecke hp F) (cubicThetaPrimeCubeHecke_c1 hp F hF) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rw [show (cubicThetaPointC1Hecke hp (cubicThetaSectionPointC1 F hF)).val x=
    (cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) (cubicThetaSectionPointC1 F hF))).val x from rfl,
    cubicThetaPointC1Trace_apply]
  exact (cubicThetaPrimeCubeHecke_apply hp F x).symm

lemma cubicThetaPointC1_atkin_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x
      (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp)
        (cubicThetaSectionPointC1 F.val F.property.1))‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  rw [cubicThetaPointC1_atkin_dilation]
  rw [←cubicThetaInversionPointC1]
  exact cubicThetaPointC1_dilation_integrable hp (cubicThetaInversionFinite F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeDerivativeAdjoint
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative adjoint of the literal cubed-prime correspondence.
It uses the same inversion conjugate as the mass adjoint. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1_trace_atkin_section {p : Eisenstein} (hp : primaryPrime p)
    (G : CubicThetaSection)
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp)
      (cubicThetaSectionPointC1 G hG))=
    cubicThetaSectionPointC1 (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G))
      (cubicThetaPrimeCubeHecke_c1 hp _ (cubicThetaInversionSection_c1 G hG)) := by
  rw [cubicThetaPointC1_atkin_dilation,←cubicThetaInversionPointC1]
  exact cubicThetaPointC1Hecke_section hp _ _

theorem cubicThetaPrimeCubeHecke_gradient_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaFiniteEnergySections) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaSectionGradient G.val x)
        (cubicThetaSectionGradient (cubicThetaPrimeCubeHecke hp F.val) x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaSectionGradient (cubicThetaInversionSection
        (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G.val))) x)
        (cubicThetaSectionGradient F.val x) ∂cubicThetaPointMeasure := by
  let F₀ := cubicThetaSectionPointC1 F.val F.property.1
  let G₀ := cubicThetaSectionPointC1 G.val G.property.1
  let S := cubicThetaFullComplex cubicThetaFullInversion
  let W := cubicThetaPrimeCubeAtkinMatrix hp
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let X := cubicThetaPointC1Pullback W G₀
  have hSF : cubicThetaPointC1Pullback S F₀=
      cubicThetaSectionPointC1 (cubicThetaInversionFinite F).val (cubicThetaInversionFinite F).property.1 :=
    (cubicThetaInversionPointC1 F.val F.property.1).symm
  have hTrX := cubicThetaPointC1_trace_atkin_section hp G.val G.property.1
  have hFG (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      F₀.val (g • x)=cubicThetaKubotaValue g*F₀.val x := F.val.property g x
  have hGG (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      G₀.val (g • x)=cubicThetaKubotaValue g*G₀.val x := G.val.property g x
  have hSFG (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      (cubicThetaPointC1Pullback S F₀).val (g • x)=
        cubicThetaKubotaValue g*(cubicThetaPointC1Pullback S F₀).val x :=
    cubicThetaPointC1Inversion_covariance F₀ hFG g x
  have hTX (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      (cubicThetaPointC1Trace hp X).val (g • x)=
        cubicThetaKubotaValue g*(cubicThetaPointC1Trace hp X).val x := by
    change (cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback W G₀)).val (g • x)=_
    rw [hTrX]
    exact (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G.val)).property g x
  have hXint := cubicThetaPointC1_atkin_integrable hp G
  have hSFint : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F₀)‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
    rw [hSF]
    exact cubicThetaPointC1_section_cover_integrable hp (cubicThetaInversionFinite F)
  have he :
      (∫ x in cubicThetaFundamentalDomain,
        inner ℂ (cubicThetaPointC1Gradient x G₀)
          (cubicThetaPointC1Gradient x (cubicThetaPointC1Hecke hp F₀)) ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaFundamentalDomain,
        inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S (cubicThetaPointC1Trace hp X)))
          (cubicThetaPointC1Gradient x F₀) ∂cubicThetaPointMeasure := by
    calc
      _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
          inner ℂ (cubicThetaPointC1Gradient x G₀)
            (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback D F₀)) ∂cubicThetaPointMeasure :=
        cubicThetaPointC1Trace_gradient_integral hp _ G₀
          (fun g => cubicThetaPointC1_covariance G₀ g (hGG g))
          (cubicThetaPointC1_dilation_integrable hp F) (cubicThetaPointC1_section_cover_integrable hp G)
      _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
          inner ℂ (cubicThetaPointC1Gradient x X)
            (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F₀)) ∂cubicThetaPointMeasure := by
        change (∫ x in cubicThetaPrimeCubeCoverDomain p,
          inner ℂ (cubicThetaPointC1Gradient x G₀) (cubicThetaPointC1Gradient x
            (cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) F₀))
          ∂cubicThetaPointMeasure)=_
        rw [cubicThetaPointC1_dilation_atkin]
        exact cubicThetaPointC1Atkin_gradient_pairing hp _ G₀
          (fun g => hSFG g.val) (fun g => hGG g.val)
      _ = ∫ x in cubicThetaFundamentalDomain,
          inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp X))
            (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F₀)) ∂cubicThetaPointMeasure :=
        (cubicThetaPointC1Trace_gradient_integral_left hp X _
          (fun g => cubicThetaPointC1_covariance _ g (hSFG g)) hXint hSFint).symm
      _ = _ := cubicThetaPointC1Inversion_gradient_pairing F₀ _ hFG hTX
  dsimp [F₀,G₀,X] at he
  rw [cubicThetaPointC1Hecke_section,hTrX,←cubicThetaInversionPointC1] at he
  simpa only [cubicThetaSectionPointC1_gradient] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFiniteAdjoint
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same literal inversion conjugate is the adjoint for the mass
and gradient forms on finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHeckeFinite_mass_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyValue G)
      (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F))=
    inner ℂ (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeAdjointFinite hp G))
      (cubicThetaFiniteEnergyValue F) := by
  rw [cubicThetaFiniteEnergyValue_pairing,cubicThetaFiniteEnergyValue_pairing]
  change (∫ x in cubicThetaFundamentalDomain,
    inner ℂ (G.val.val x) ((cubicThetaPrimeCubeHecke hp F.val).val x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,inner ℂ
      ((cubicThetaInversionSection (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G.val))).val x)
      (F.val.val x) ∂cubicThetaPointMeasure
  simpa only [RCLike.inner_apply',Complex.star_def] using
    cubicThetaPrimeCubeHecke_mass_adjoint hp F.val G.val
      (cubicThetaPrimeCubeFinite_mass_domain F) (cubicThetaPrimeCubeFinite_mass_domain G)

lemma cubicThetaPrimeCubeHeckeFinite_gradient_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyGradient G)
      (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp F))=
    inner ℂ (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeAdjointFinite hp G))
      (cubicThetaFiniteEnergyGradient F) := by
  rw [cubicThetaFiniteEnergyGradient_pairing,cubicThetaFiniteEnergyGradient_pairing]
  exact cubicThetaPrimeCubeHecke_gradient_adjoint hp F G

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeCompletedAdjoint
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both finite pairings extend to the completed global energy
space. The adjoint is the actual inversion-conjugated correspondence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHeckeAdjoint_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeHeckeAdjoint hp (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaFiniteEnergyEmbedding (cubicThetaPrimeCubeAdjointFinite hp F) := by
  change cubicThetaInversionEnergy (cubicThetaPrimeCubeHeckeEnergy hp
    (cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding F)))=_
  rw [cubicThetaInversionEnergy_finite,cubicThetaPrimeCubeHeckeEnergy_finite]
  change cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding
    (cubicThetaPrimeCubeHeckeFinite hp (cubicThetaInversionFinite F)))=_
  exact cubicThetaInversionEnergy_finite _

theorem cubicThetaPrimeCubeHeckeEnergy_mass_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion (cubicThetaPrimeCubeHeckeEnergy hp v))=
      inner ℂ (cubicThetaGlobalInclusion (cubicThetaPrimeCubeHeckeAdjoint hp u)) (cubicThetaGlobalInclusion v) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaGlobalInclusion.continuous.inner continuous_const)
      ((cubicThetaGlobalInclusion.continuous.comp (cubicThetaPrimeCubeHeckeAdjoint hp).continuous).inner
        continuous_const)) ?_
  intro F
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on v
    (isClosed_eq (continuous_const.inner (cubicThetaGlobalInclusion.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      (continuous_const.inner cubicThetaGlobalInclusion.continuous)) ?_
  intro G
  rw [cubicThetaPrimeCubeHeckeEnergy_finite,cubicThetaPrimeCubeHeckeAdjoint_finite]
  change inner ℂ (cubicThetaFiniteEnergyValue F)
      (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp G))=
    inner ℂ (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeAdjointFinite hp F))
      (cubicThetaFiniteEnergyValue G)
  exact cubicThetaPrimeCubeHeckeFinite_mass_adjoint hp G F

theorem cubicThetaPrimeCubeHeckeEnergy_gradient_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient u)
      (cubicThetaGlobalEnergyGradient (cubicThetaPrimeCubeHeckeEnergy hp v))=
    inner ℂ (cubicThetaGlobalEnergyGradient (cubicThetaPrimeCubeHeckeAdjoint hp u))
      (cubicThetaGlobalEnergyGradient v) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaGlobalEnergyGradient.continuous.inner continuous_const)
      ((cubicThetaGlobalEnergyGradient.continuous.comp (cubicThetaPrimeCubeHeckeAdjoint hp).continuous).inner
        continuous_const)) ?_
  intro F
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on v
    (isClosed_eq (continuous_const.inner (cubicThetaGlobalEnergyGradient.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      (continuous_const.inner cubicThetaGlobalEnergyGradient.continuous)) ?_
  intro G
  rw [cubicThetaPrimeCubeHeckeEnergy_finite,cubicThetaPrimeCubeHeckeAdjoint_finite]
  change inner ℂ (cubicThetaFiniteEnergyGradient F)
      (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp G))=
    inner ℂ (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeAdjointFinite hp F))
      (cubicThetaFiniteEnergyGradient G)
  exact cubicThetaPrimeCubeHeckeFinite_gradient_adjoint hp G F

theorem cubicThetaPrimeCubeHeckeEnergy_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaPrimeCubeHeckeEnergy hp v)=inner ℂ (cubicThetaPrimeCubeHeckeAdjoint hp u) v := by
  rw [cubicThetaGlobalEnergy_inner,cubicThetaGlobalEnergy_inner,
    cubicThetaPrimeCubeHeckeEnergy_mass_adjoint,cubicThetaPrimeCubeHeckeEnergy_gradient_adjoint]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSelfAdjoint
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mass, gradient, and completed energy pairings are symmetric
for the cubed-prime correspondence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAdjointFinite_eq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeAdjointFinite hp F=cubicThetaPrimeCubeHeckeFinite hp F := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeHecke_inversion_adjoint hp F.val

theorem cubicThetaPrimeCubeHeckeAdjoint_eq {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeHeckeAdjoint hp=cubicThetaPrimeCubeHeckeEnergy hp := by
  apply ContinuousLinearMap.ext
  intro u
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaPrimeCubeHeckeAdjoint hp).continuous
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeAdjoint_finite,cubicThetaPrimeCubeHeckeEnergy_finite,
    cubicThetaPrimeCubeAdjointFinite_eq]
  rfl

theorem cubicThetaPrimeCubeHecke_symmetric {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaPrimeCubeHeckeEnergy hp v)=inner ℂ (cubicThetaPrimeCubeHeckeEnergy hp u) v := by
  rw [cubicThetaPrimeCubeHeckeEnergy_adjoint,cubicThetaPrimeCubeHeckeAdjoint_eq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeMassOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same cubed-prime correspondence on the actual automorphic mass
space. It agrees with the energy operator and is self-adjoint there. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubeMass_finiteGroup
theorem cubicThetaPrimeCubeHeckeMass_energy {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalEnergyValueMap u)=
      cubicThetaGlobalEnergyValueMap (cubicThetaPrimeCubeHeckeEnergy hp u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeHeckeMass hp).continuous.comp
      cubicThetaGlobalEnergyValueMap.continuous)
      (cubicThetaGlobalEnergyValueMap.continuous.comp (cubicThetaPrimeCubeHeckeEnergy hp).continuous)) ?_
  intro F
  change cubicThetaPrimeCubeHeckeMass hp (cubicThetaFiniteMassClosure F)=_
  rw [cubicThetaPrimeCubeHeckeMass_finite,cubicThetaPrimeCubeHeckeEnergy_finite]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRadialPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeRadialPairing_energy {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(p:ℂ)‖^3, W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
        (cubicThetaCuspRestriction (cubicThetaPrimeCubeHeckeEnergy hp u))=
      inner ℂ (cubicThetaCuspFourierTest 0
        (cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3) (by
          have := cubicThetaPrimeCube_height_ge_one hp; linarith) W))
        (cubicThetaCuspRestriction u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (continuous_const.inner (cubicThetaCuspRestriction.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      (continuous_const.inner cubicThetaCuspRestriction.continuous)) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeEnergy_finite]
  change inner ℂ (cubicThetaCuspFourierTest 0 W)
    (cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding (cubicThetaPrimeCubeHeckeFinite hp F)))=_
  rw [cubicThetaCuspRestriction_finiteEnergy,cubicThetaCuspRestriction_finiteEnergy]
  exact cubicThetaPrimeCubeRadialPairing_finite hp F W hW

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaThetaObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual weighted Fourier observations of the theta residue. The
arithmetic value of the nonzero Whittaker coefficient remains to be identified. -/
noncomputable section
open Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaResidue_zero_observation (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
      (3*Real.pi:ℂ)*cubicThetaScatteringResidue*cubicThetaZeroRadialTest W (4/3) := by
  have hc : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/(s-1)*cubicThetaZeroRadialTest W s) (4/3) :=
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)).mul
      ((cubicThetaZeroRadialWindow_entire W hW).continuous.continuousAt (x:=(4/3:ℂ)))
  have ht := (hc.tendsto.mono_left nhdsWithin_le_nhds).mul cubicThetaConstantContinuation_residue
  change Tendsto (fun s : ℂ => ((Real.pi:ℂ)/(s-1)*cubicThetaZeroRadialTest W s)*
      ((s-4/3)*cubicThetaConstantContinuation s)) (𝓝[≠] (4/3:ℂ))
      (𝓝 (((Real.pi:ℂ)/((4/3:ℂ)-1)*cubicThetaZeroRadialTest W (4/3))*
        cubicThetaScatteringResidue)) at ht
  have hp : Tendsto (fun s : ℂ => (s-4/3)*cubicThetaCuspFourierObservable 0 W s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 ((3*Real.pi:ℂ)*cubicThetaScatteringResidue*cubicThetaZeroRadialTest W (4/3))) := by
    have he : ((Real.pi:ℂ)/((4/3:ℂ)-1)*cubicThetaZeroRadialTest W (4/3))*
        cubicThetaScatteringResidue=
        (3*Real.pi:ℂ)*cubicThetaScatteringResidue*cubicThetaZeroRadialTest W (4/3) := by ring
    rw [he] at ht
    apply ht.congr'
    filter_upwards [cubicThetaCuspZeroWindow_continued W hW (s:=(4/3:ℂ)) (by norm_num)] with s hs
    rw [hs]
    ring
  have hr := cubicThetaCuspObservable_residue (cubicThetaCuspFourierTest 0 W)
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hr
  exact tendsto_nhds_unique hr hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRadialResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCube_residue_radial_observation {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaPrimeCubeHeckeEnergy hp
        (cubicThetaArithmeticResidueEnergy (4/3))))=
      ((norm p)^2+norm p:ℂ)*inner ℂ (cubicThetaCuspFourierTest 0 W)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))) := by
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    apply hW
    have := cubicThetaPrimeCube_height_ge_one hp
    nlinarith
  rw [cubicThetaPrimeCubeRadialPairing_energy hp _ W hW,
    cubicThetaResidue_zero_observation _ (cubicThetaPrimeCubeRadialWeight_low hp W hW),
    cubicThetaPrimeCube_zeroRadialTest hp W hW,cubicThetaResidue_zero_observation W hW2]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeWeakEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cubed-prime correspondence preserves the full global
weak spectral equation, by its common mass and energy adjoint. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeEnergyPencil_pairing {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaEnergyPencil z (cubicThetaPrimeCubeHeckeEnergy hp v))=
      inner ℂ (cubicThetaPrimeCubeHeckeAdjoint hp u) (cubicThetaEnergyPencil z v) := by
  rw [cubicThetaGlobalEnergyPencil_pairing,cubicThetaGlobalEnergyPencil_pairing,
    cubicThetaPrimeCubeHeckeEnergy_adjoint,cubicThetaPrimeCubeHeckeEnergy_mass_adjoint]

theorem cubicThetaPrimeCubeHeckeEnergy_kernel {p : Eisenstein} (hp : primaryPrime p)
    (z : ℂ) (v : cubicThetaGlobalEnergySpace) (hv : cubicThetaEnergyPencil z v=0) :
    cubicThetaEnergyPencil z (cubicThetaPrimeCubeHeckeEnergy hp v)=0 := by
  apply ext_inner_left ℂ
  intro u
  rw [cubicThetaPrimeCubeEnergyPencil_pairing,hv,inner_zero_right,inner_zero_right]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeResidueEigenvalue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic residue is a cubed-prime Hecke eigenvector.
The proof uses its two computed moments and self-adjointness. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment


theorem cubicThetaArithmeticResidueEnergy_hecke {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeHeckeEnergy hp (cubicThetaArithmeticResidueEnergy (4/3))=
      ((norm p)^2+norm p:ℂ) • cubicThetaArithmeticResidueEnergy (4/3) := by
  let r := ‖(p:ℂ)‖^3
  have hr1 : 1 ≤ r := cubicThetaPrimeCube_height_ge_one hp
  have hr : 0 < r := by linarith
  let H := 2*r^2
  have hH : 2≤H := by dsimp [H]; nlinarith
  let W := cubicThetaLongForcingWeight H (by linarith) (4/3)
  let V := cubicThetaRadialHeckeWeight r hr W
  let R := cubicThetaArithmeticResidueEnergy (4/3)
  let T := cubicThetaPrimeCubeHeckeEnergy hp
  let lam : ℂ := (norm p)^2+norm p
  have hlam : star lam=lam := by
    have he : lam=(((norm p)^2+norm p:ℝ):ℂ) := by
      dsimp only [lam]
      push_cast
      rfl
    rw [he]
    exact Complex.conj_ofReal _
  have hW : ∀ v≤2*r, W v=0 := by
    intro v hv
    apply cubicThetaLongForcingWeight_low
    change v≤2*r^2
    nlinarith
  have hV : ∀ v≤2*r, V v=0 := by
    apply cubicThetaRadialHeckeWeight_low hr1 (by positivity)
    intro v hv
    apply cubicThetaLongForcingWeight_low
    change v≤2*r^2
    nlinarith
  let obs : cubicThetaGlobalEnergySpace → ℂ := fun u =>
    inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaCuspRestriction u)
  have ho1 : obs (T R)=lam*obs R :=
    cubicThetaPrimeCube_residue_radial_observation hp W hW
  have ho2 : obs (T (T R))=lam^2*obs R := by
    change inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaCuspRestriction (T (T R)))=_
    rw [cubicThetaPrimeCubeRadialPairing_energy hp (T R) W hW]
    change inner ℂ (cubicThetaCuspFourierTest 0 V) (cubicThetaCuspRestriction (T R))=_
    rw [cubicThetaPrimeCube_residue_radial_observation hp V hV]
    change lam*inner ℂ (cubicThetaCuspFourierTest 0 V) (cubicThetaCuspRestriction R)=_
    rw [←cubicThetaPrimeCubeRadialPairing_energy hp R W hW]
    change lam*obs (T R)=_
    rw [ho1]
    ring
  have hR : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) R=0 := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using cubicThetaArithmeticResidueEnergy_kernel (4/3)
  have hTR := cubicThetaPrimeCubeHeckeEnergy_kernel hp _ R hR
  have hTTR := cubicThetaPrimeCubeHeckeEnergy_kernel hp _ (T R) hTR
  have hpair (u : cubicThetaGlobalEnergySpace)
      (hu : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) u=0) :
      inner ℂ u R=(17/6:ℂ)*star (obs u) :=
    cubicThetaResidue_long_kernel_pairing H hH u hu
  have h1 : inner ℂ (T R) R=lam*inner ℂ R R := by
    rw [hpair _ hTR,hpair _ hR,ho1,star_mul,hlam]
    ring
  have h2 : inner ℂ (T (T R)) R=lam^2*inner ℂ R R := by
    rw [hpair _ hTTR,hpair _ hR,ho2,star_mul,star_pow,hlam]
    ring
  exact cubicThetaSelfAdjoint_two_moments T (cubicThetaPrimeCubeHecke_symmetric hp) R lam hlam h1 h2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubeRootLift_smoothGroup
lemma cubicThetaPrimeCubeRootLiftL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeCubeRootNormalizedRestriction hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCuspLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility of the actual cubic-root restriction with the original
energy-space cusp observation. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootCuspRestriction_lift {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeRootCuspRestriction hp
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap u))=
      ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
        cubicThetaCuspRestriction u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootCuspRestriction hp).continuous.comp
      ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp cubicThetaGlobalEnergyValueMap.continuous))
      ((continuous_const (y:=((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ))).smul
        cubicThetaCuspRestriction.continuous)) ?_
  intro F
  change cubicThetaPrimeCubeRootCuspRestriction hp
    (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F)))=_
  rw [cubicThetaGlobalEnergyValueMap_test,cubicThetaPrimeCubeRootLiftL2_smooth]
  change cubicThetaPrimeCubeRootCuspRestriction hp
    (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))=_
  rw [map_smul,cubicThetaPrimeCubeRootCuspRestriction_finite,
    cubicThetaPrimeCubeRootFiniteCuspRestriction_smooth]
  congr 1
  change cubicThetaFiniteCuspRestriction (cubicThetaSmoothToFiniteEnergy F)=
    cubicThetaCuspRestriction (cubicThetaGlobalEnergyTest F)
  rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaCuspRestriction_finiteEnergy]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeRoot_observation_dilation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeRootObservation hp (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W)
      (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalEnergyValueMap u))=
      ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
        ((‖(p:ℂ)‖^3:ℝ):ℂ)^2*inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspRestriction u) := by
  let L := (cubicThetaPrimeCubeRootObservation hp (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W)).comp
    ((cubicThetaPrimeCubeRootDilationL2 hp).toContinuousLinearMap.comp cubicThetaGlobalEnergyValueMap)
  let R := (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
    ((‖(p:ℂ)‖^3:ℝ):ℂ)^2) • (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp cubicThetaCuspRestriction
  change L u=R u
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq L.continuous R.continuous) ?_
  intro F
  change cubicThetaPrimeCubeRootObservation hp (p^3*h) _
    (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F)))=_
  rw [cubicThetaGlobalEnergyValueMap_test,cubicThetaPrimeCubeRootDilationL2_smooth]
  change cubicThetaPrimeCubeRootObservation hp (p^3*h) _
    (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F))=_
  rw [map_smul,cubicThetaPrimeCubeRootFinite_observation_dilation hp h W hW F]
  change _=(((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
    ((‖(p:ℂ)‖^3:ℝ):ℂ)^2)*inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaGlobalEnergyTest F))
  rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaCuspRestriction_finiteEnergy]
  simp only [smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylGlobal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual twice-cubically-dilated global branch and its invariance
under all cubic-scale translations. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootWeyl_lift_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootTranslateL2 hp x
      (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))=
        cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
      ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp (cubicThetaPrimeCubeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp (cubicThetaPrimeCubeRootLiftL2 hp).continuous)) ?_
  intro F
  simp only [cubicThetaPrimeCubeRootLiftL2_smooth,cubicThetaPrimeCubeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeCubeRootWeylL2_finite,
    cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootWeyl_finite_translate]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unit-branch transport on the cubic-scale Hilbert completion.
There is no arithmetic-residue or Hecke-eigenvector hypothesis here. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootWeyl_mass_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootWeylL2 hp
      (cubicThetaPrimeCubeRootTranslateL2 hp y (cubicThetaPrimeCubeRootLiftL2 hp u))=
      cubicThetaPrimeCubeRootTranslateL2 hp (-x)
        (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass u)) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp
      ((cubicThetaPrimeCubeRootTranslateL2 hp y).continuous.comp (cubicThetaPrimeCubeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeCubeRootTranslateL2 hp (-x)).continuous.comp
        ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp cubicThetaInversionMass.continuous))) ?_
  intro F
  simp only [cubicThetaInversionMass_smooth,cubicThetaPrimeCubeRootLiftL2_smooth,
    cubicThetaPrimeCubeRootNormalizedRestriction,LinearMap.smul_apply,LinearMap.comp_apply,
    map_smul,cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootWeylL2_finite,
    cubicThetaPrimeCubeRootFinite_bruhat hp x y hxy]


theorem cubicThetaPrimeCubeRoot_unit_correlation {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp y (cubicThetaPrimeCubeRootLiftL2 hp v))=
    inner ℂ (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass v)) := by
  have hw := (cubicThetaPrimeCubeRootWeylL2 hp).inner_map_map
    (cubicThetaPrimeCubeRootLiftL2 hp u)
    (cubicThetaPrimeCubeRootTranslateL2 hp y (cubicThetaPrimeCubeRootLiftL2 hp v))
  rw [cubicThetaPrimeCubeRootWeyl_mass_bruhat hp x y hxy] at hw
  have ht := (cubicThetaPrimeCubeRootTranslateL2 hp x).inner_map_map
    (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
    (cubicThetaPrimeCubeRootTranslateL2 hp (-x)
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass v)))
  rw [cubicThetaPrimeCubeRootWeyl_lift_translate,←cubicThetaPrimeCubeRootTranslateL2_add,
    add_neg_cancel,cubicThetaPrimeCubeRootTranslateL2_zero] at ht
  exact hw.symm.trans ht.symm

theorem cubicThetaPrimeCubeRoot_unit_residue_correlation {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : IsUnit r) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp v))=
    inner ℂ (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass v)) :=
  cubicThetaPrimeCubeRoot_unit_correlation hp
    (residueRepresentative (p^3) (cubicThetaPrimeRootReciprocal (p^3) r))
    (residueRepresentative (p^3) r) (cubicThetaPrimeCubeRootReciprocal_pair hp r hr) u v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhatMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each nonzero Bruhat branch acts by its actual cubic multiplier
on the completed global mass space. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_mass_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootWeylL2 hp
      (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp u))=
      (cubicSymbol p 3*cubicResidueChar p hp r) •
        cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)
          (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass u)) := by
  let L := (cubicThetaPrimeRootWeylL2 hp).toContinuousLinearMap.comp
    ((cubicThetaPrimeRootResidueL2 hp r).toContinuousLinearMap.comp
      (cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap)
  let R := (cubicSymbol p 3*cubicResidueChar p hp r) •
    (cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)).toContinuousLinearMap.comp
      ((cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap.comp cubicThetaInversionMass.toContinuousLinearMap)
  change L u=R u
  refine cubicThetaGlobalMassClosure_dense.induction_on u (isClosed_eq L.continuous R.continuous) ?_
  intro F
  change cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootResidueL2 hp r
    (cubicThetaPrimeRootLiftL2 hp (cubicThetaGlobalMassClosure F)))=
    (cubicSymbol p 3*cubicResidueChar p hp r) •
      cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)
        (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass (cubicThetaGlobalMassClosure F)))
  simp only [cubicThetaInversionMass_smooth,cubicThetaPrimeRootLiftL2_smooth,
    cubicThetaPrimeRootNormalizedRestriction,LinearMap.smul_apply,LinearMap.comp_apply,
    map_smul,cubicThetaPrimeRootResidueL2_finite,cubicThetaPrimeRootWeylL2_finite]
  have he := congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
    (cubicThetaPrimeRootFinite_bruhat hp r hr F)
  simp only [map_smul] at he
  rw [he]
  module

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootOrbitOrthogonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct fractional translates of the original global space are
orthogonal, and all are orthogonal to its Weyl translate. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootLift_translate_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : r≠0) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
      (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  classical
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  calc
    _ = inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
        (cubicThetaPrimeRootWeylL2 hp
          (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v))) :=
            ((cubicThetaPrimeRootWeylL2 hp).inner_map_map _ _).symm
    _ = inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
        ((cubicSymbol p 3*cubicResidueChar p hp r) •
          cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)
            (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass v))) := by
              rw [cubicThetaPrimeRootWeyl_mass_bruhat hp r (isUnit_iff_ne_zero.mpr hr)]
    _ = 0 := by
      rw [inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp),
        cubicThetaPrimeRootWeyl_translate_pair_zero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootTranslationIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-level Hilbert orthogonality, expressed as its literal
fundamental-domain integral for finite-cover transport. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeRoot_translation_integral_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x)
    (F G : cubicThetaSmoothTests) :
    (∫ z in cubicThetaPrimeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  let r : Residues p := Ideal.Quotient.mk (modulus p) x
  have hr : r≠0 := by
    intro he
    exact hx (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
  let c : ℂ := ((Real.sqrt ((cubicThetaPrimeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)
  have hc : c≠0 := by
    change ((Real.sqrt ((cubicThetaPrimeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)≠0
    exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (cubicThetaPrimeRootCoverDegree_pos hp)))
  have he := cubicThetaPrimeRootLift_translate_pair_zero hp r hr
    (cubicThetaGlobalMassClosure F) (cubicThetaGlobalMassClosure G)
  simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeRootResidueL2_finite] at he
  change inner ℂ (c • cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F))
    (c • cubicThetaPrimeRootFiniteEmbedding hp
      (cubicThetaPrimeRootFiniteResidue hp r (cubicThetaPrimeRootSmoothRestriction hp G)))=0 at he
  rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp),
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp)] at he
  have hs : starRingEnd ℂ c≠0 := by simpa only [starRingEnd_apply] using star_ne_zero.mpr hc
  have hz := (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)).resolve_left hc
  rw [cubicThetaPrimeRootSectionPairing_L2,cubicThetaPrimeRootSectionPairing_unfold] at hz
  change (∫ z in cubicThetaPrimeRootCoverDomain hp,star (F.val.val z)*
    (cubicThetaPrimeRootResidueOperator hp r
      (cubicThetaPrimeRootSectionRestrict G.val)).val z ∂cubicThetaPointMeasure)=0 at hz
  rw [show r=Ideal.Quotient.mk (modulus p) x from rfl,cubicThetaPrimeRootResidueOperator_mk] at hz
  exact hz

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFirstIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeRoot_first_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : cubicThetaSmoothTests) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  have he := cubicThetaFiniteCover_integral (cubicThetaFirstRootCover hp)
    (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRoot_le_first hp)
    (cubicThetaPrimeCubeRootCoverDomain hp)
    (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure)
    (f:=fun z => star (F.val.val z)*G.val.val (cubicThetaPrimeRootElement hp x • z))
    (cubicThetaPrimeRoot_translate_pair_invariant hp x F.val G.val)
  change (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
    G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=_
    at he
  rw [show (∫ z in (cubicThetaFirstRootCover hp).domain,star (F.val.val z)*
      G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=0 from
        cubicThetaPrimeRoot_translation_integral_zero hp x hx F G,smul_zero] at he
  exact he

theorem cubicThetaPrimeCubeRoot_square_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : cubicThetaSmoothTests) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeCubeRootElement hp (p^2*x) • z) ∂cubicThetaPointMeasure)=0 := by
  rw [cubicThetaPrimeCubeRootElement_square]
  exact cubicThetaPrimeCubeRoot_first_integral_zero hp x hx F G

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootNonunitCorrelation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both intermediate valuation classes vanish in the actual completed
cube-root correlation, by the proved integral identities and density. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_translate_zero_of_integral {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein)
    (h : ∀ F G : cubicThetaSmoothTests,
      (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
        G.val.val (cubicThetaPrimeCubeRootElement hp x • z) ∂cubicThetaPointMeasure)=0)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootLiftL2 hp v))=0 := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootLiftL2 hp v))=0) ?_ ?_ u v
  · apply isClosed_eq _ continuous_const
    exact ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp continuous_fst).inner
      ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
        ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp continuous_snd))
  · intro F G
    simp only [cubicThetaPrimeCubeRootLiftL2_smooth,cubicThetaPrimeCubeRootNormalizedRestriction,
      LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeCubeRootTranslateL2_finite]
    rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),
      inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),
      cubicThetaPrimeCubeRootFinite_pairing]
    change _*(_*(∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeCubeRootElement hp x • z) ∂cubicThetaPointMeasure))=0
    rw [h F G,mul_zero,mul_zero]

theorem cubicThetaPrimeCubeRoot_single_correlation_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp (p*x) (cubicThetaPrimeCubeRootLiftL2 hp v))=0 :=
  cubicThetaPrimeCubeRoot_translate_zero_of_integral hp (p*x)
    (fun F G => cubicThetaPrimeCubeRoot_single_integral_zero hp x hx F.val G.val) u v

theorem cubicThetaPrimeCubeRoot_square_correlation_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp (p^2*x) (cubicThetaPrimeCubeRootLiftL2 hp v))=0 :=
  cubicThetaPrimeCubeRoot_translate_zero_of_integral hp (p^2*x)
    (fun F G => cubicThetaPrimeCubeRoot_square_integral_zero hp x hx F G) u v

theorem cubicThetaPrimeCubeRoot_nonunit_correlation_zero {p : Eisenstein}
    (hp : primaryPrime p) (r : Residues (p^3)) (hr : ¬IsUnit r) (hr0 : r≠0)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp v))=0 := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective r
  have hx : p∣x := by
    by_contra h
    exact hr (residue_isUnit_of_isCoprime (hp.2.coprime_iff_not_dvd.mpr h).pow_left)
  obtain ⟨a,rfl⟩ := hx
  rw [cubicThetaPrimeCubeRootResidueL2_mk]
  by_cases ha : p∣a
  · obtain ⟨b,rfl⟩ := ha
    have hb : ¬p∣b := by
      rintro ⟨c,rfl⟩
      apply hr0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.mem_span_singleton.mpr
      exact ⟨c,by ring⟩
    simpa only [←mul_assoc,←pow_two] using cubicThetaPrimeCubeRoot_square_correlation_zero hp b hb u v
  · exact cubicThetaPrimeCubeRoot_single_correlation_zero hp a ha u v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCorrelationFormula
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact projection norm is determined by the actual common unit
correlation and the literal local Gauss sum. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootUnitCorrelation {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) : ℂ :=
  inner ℂ (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
    (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass u))

theorem cubicThetaPrimeCubeRoot_norm_gauss {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (u : cubicThetaAutomorphicL2) :
    (‖cubicThetaPrimeCubeRootFourierL2 hp (Ideal.Quotient.mk (modulus (p^3)) h)
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℂ)=
    (norm (p^3):ℂ)⁻¹*((‖u‖^2:ℂ)+cubicThetaPrimeCubeRootUnitCorrelation hp u*
      star (cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 h)) := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let k := Ideal.Quotient.mk (modulus (p^3)) h
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  let w := fun r : Residues (p^3) => cubicSymbol (p^3) (residueRepresentative (p^3) r)
  let C := cubicThetaPrimeCubeRootUnitCorrelation hp u
  have ht (r : Residues (p^3)) :
      star (ψ (k*r))*inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
        (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp u))=
      (if r=0 then (‖u‖^2:ℂ) else 0)+C*star (w r*ψ (k*r)) := by
    by_cases hr0 : r=0
    · subst r
      rw [cubicThetaPrimeCubeRootResidueL2_zero,
        inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (cubicThetaPrimeCubeRootLiftL2 hp u),
        (cubicThetaPrimeCubeRootLiftL2 hp).norm_map]
      simp only [mul_zero,AddChar.map_zero_eq_one,star_one,one_mul,ite_true, if_true,w,
        cubicThetaPrimeCubeRoot_weight_zero hp,zero_mul,star_zero,mul_zero,add_zero]
      rfl
    · rw [ite_eq_right hr0]
      by_cases hr : IsUnit r
      · rw [cubicThetaPrimeCubeRoot_unit_residue_correlation hp r hr]
        change star (ψ (k*r))*C=0+C*star (w r*ψ (k*r))
        rw [show w r=1 from cubicThetaPrimeCubeRoot_weight_unit hp r hr,one_mul,zero_add,mul_comm]
      · rw [cubicThetaPrimeCubeRoot_nonunit_correlation_zero hp r hr hr0]
        change star (ψ (k*r))*0=0+C*star (w r*ψ (k*r))
        rw [show w r=0 from cubicThetaPrimeCubeRoot_weight_nonunit hp r hr,
          zero_mul,star_zero,mul_zero,mul_zero,add_zero]
  rw [cubicThetaPrimeCubeRootFourierL2_norm_correlation]
  change (norm (p^3):ℂ)⁻¹*(∑ r : Residues (p^3),star (ψ (k*r))*
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp u)))=_
  simp_rw [ht]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←star_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  simp only [cubicThetaLocalPrimePowerGauss,tsum_fintype]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootNormBalance
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact elimination of the common unit correlation between the zero
and square-frequency projection norms. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_zero_norm_identity {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    (norm p:ℂ)^3*(‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℂ)=
    (‖u‖^2:ℂ)+((norm p:ℂ)^3-(norm p:ℂ)^2)*cubicThetaPrimeCubeRootUnitCorrelation hp u := by
  have he := cubicThetaPrimeCubeRoot_norm_gauss hp 0 u
  rw [map_zero,cubicThetaPrimeCubeRoot_gauss_zero hp,eisenstein_norm_pow,Complex.ofReal_pow,
    star_sub,star_pow,star_pow] at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [he,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 3 hq),one_mul]
  ring

lemma cubicThetaPrimeCubeRoot_square_norm_identity {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (u : cubicThetaAutomorphicL2) :
    (norm p:ℂ)^3*(‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℂ)=
    (‖u‖^2:ℂ)-(norm p:ℂ)^2*cubicThetaPrimeCubeRootUnitCorrelation hp u := by
  have he := cubicThetaPrimeCubeRoot_norm_gauss hp (p^2*h) u
  rw [cubicThetaPrimeCubeRoot_ramanujan hp h hh,eisenstein_norm_pow,Complex.ofReal_pow,
    star_neg,star_pow] at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [he,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 3 hq),one_mul]
  ring

theorem cubicThetaPrimeCubeRoot_norm_balance {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (u : cubicThetaAutomorphicL2) :
    (norm p)^2*‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2+
    ((norm p)^3-(norm p)^2)*‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2=‖u‖^2 := by
  have h0 := cubicThetaPrimeCubeRoot_zero_norm_identity hp u
  have h1 := cubicThetaPrimeCubeRoot_square_norm_identity hp h hh u
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have he : (((norm p)^2*‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2+
    ((norm p)^3-(norm p)^2)*‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp u)‖^2:ℝ):ℂ)=(‖u‖^2:ℂ) := by
    push_cast
    apply mul_left_cancel₀ hq
    linear_combination h0+((norm p:ℂ)-1)*h1
  exact_mod_cast he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootTraceNormalized
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact normalized trace pairing. No Hecke eigenvalue or local
coefficient relation is postulated in constructing this identity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootTrace_normalized_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalMassClosure F))
      (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalMassClosure G))=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*
        inner ℂ (cubicThetaGlobalMassClosure F)
          (cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalMassClosure G)) := by
  rw [cubicThetaPrimeCubeRootLiftL2_smooth,cubicThetaPrimeCubeRootDilationL2_smooth]
  simp only [cubicThetaPrimeCubeRootNormalizedRestriction,cubicThetaPrimeCubeRootNormalizedDilation,
    LinearMap.smul_apply,LinearMap.comp_apply]
  rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),starRingEnd_apply,
    cubicThetaPrimeCubeRootTrace_finite]
  change star (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
    ((((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
      (((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℂ)*
        inner ℂ (cubicThetaGlobalMassClosure F)
          (cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalMassClosure G))))=_
  rw [←mul_assoc,←mul_assoc,cubicThetaPrimeCubeRootTrace_scalar]

theorem cubicThetaPrimeCubeRootTrace_normalized {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v)=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*
        inner ℂ u (cubicThetaPrimeCubeHeckeMass hp v) := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v)=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*inner ℂ u (cubicThetaPrimeCubeHeckeMass hp v)) ?_ ?_ u v
  · apply isClosed_eq
    · exact ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp continuous_fst).inner
        ((cubicThetaPrimeCubeRootDilationL2 hp).continuous.comp continuous_snd)
    · exact continuous_const.mul (continuous_fst.inner
        ((cubicThetaPrimeCubeHeckeMass hp).continuous.comp continuous_snd))
  · exact cubicThetaPrimeCubeRootTrace_normalized_smooth hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueSourceOrbit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual residue applied to the full positive-cutoff source orbit.
The scalar recurrence here is derived from its proved Hecke eigenvalue. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaArithmeticResidueL2_hecke {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeHeckeMass hp cubicThetaArithmeticResidueL2=
      ((norm p)^2+norm p:ℂ) • cubicThetaArithmeticResidueL2 := by
  have he : cubicThetaArithmeticResidueL2=
      cubicThetaGlobalEnergyValueMap (cubicThetaArithmeticResidueEnergy (4/3)) := rfl
  rw [he,cubicThetaPrimeCubeHeckeMass_energy,cubicThetaArithmeticResidueEnergy_hecke,map_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootResidueOverlap
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The once-cubic overlap of the actual arithmetic residue follows
from the proved Hecke eigenvalue and exact trace normalization. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootResidue_overlap {p : Eisenstein} (hp : primaryPrime p) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)
      (cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2)=
      (norm p:ℂ)⁻¹*(‖cubicThetaArithmeticResidueL2‖^2:ℂ) := by
  rw [cubicThetaPrimeCubeRootTrace_normalized,cubicThetaArithmeticResidueL2_hecke,
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2),←mul_assoc,
    cubicThetaPrimeCubeRootHecke_ratio hp]
  exact congrArg (fun z : ℂ => (norm p:ℂ)⁻¹*z)
    (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) cubicThetaArithmeticResidueL2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootResidueAverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Hecke overlap forces a lower bound for the zero-frequency
component of the arithmetic residue on the cubic root cover. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootResidue_average_pairing {p : Eisenstein} (hp : primaryPrime p) :
    inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2))
      (cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2)=
    (norm p:ℂ)⁻¹*(‖cubicThetaArithmeticResidueL2‖^2:ℂ) := by
  rw [cubicThetaPrimeCubeRootDilationL2_average_pairing,cubicThetaPrimeCubeRootResidue_overlap]

theorem cubicThetaPrimeCubeRootResidue_average_norm_lower {p : Eisenstein} (hp : primaryPrime p) :
    (norm p)⁻¹*‖cubicThetaArithmeticResidueL2‖≤
      ‖cubicThetaPrimeCubeRootFourierL2 hp 0
        (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖ := by
  let a := cubicThetaPrimeCubeRootFourierL2 hp 0
    (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)
  let b := cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2
  let n : ℝ := ‖cubicThetaArithmeticResidueL2‖
  have he := norm_inner_le_norm (𝕜:=ℂ) a b
  rw [cubicThetaPrimeCubeRootResidue_average_pairing,
    (cubicThetaPrimeCubeRootDilationL2 hp).norm_map] at he
  change ‖(norm p:ℂ)⁻¹*(n:ℂ)^2‖≤‖a‖*n at he
  rw [norm_mul,norm_inv,Complex.norm_of_nonneg (norm_nonneg p),norm_pow,
    Complex.norm_of_nonneg (_root_.norm_nonneg cubicThetaArithmeticResidueL2)] at he
  change (norm p)⁻¹*n≤‖a‖
  by_cases hn : n=0
  · rw [hn,mul_zero]
    exact _root_.norm_nonneg a
  · have hnpos : 0<n := lt_of_le_of_ne (_root_.norm_nonneg cubicThetaArithmeticResidueL2) (Ne.symm hn)
    apply (mul_le_mul_iff_of_pos_right hnpos).mp
    nlinarith [he]

theorem cubicThetaPrimeCubeRootResidue_average_mass_lower {p : Eisenstein} (hp : primaryPrime p) :
    (norm p)^2*‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖^2≥
      ‖cubicThetaArithmeticResidueL2‖^2 := by
  have he := cubicThetaPrimeCubeRootResidue_average_norm_lower hp
  have hq : 0<norm p := norm_pos_of_ne_zero hp.2.ne_zero
  have hs := mul_le_mul_of_nonneg_left he hq.le
  rw [←mul_assoc,mul_inv_cancel₀ hq.ne',one_mul] at hs
  have ht := mul_self_le_mul_self (_root_.norm_nonneg cubicThetaArithmeticResidueL2) hs
  simpa only [←pow_two,mul_pow] using ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCriticalSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and the actual Hecke overlap force the missing square
frequency to vanish for the arithmetic residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidue_square_projection_zero {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)=0 := by
  have he := cubicThetaPrimeCubeRoot_norm_balance hp h hh cubicThetaArithmeticResidueL2
  have hlo := cubicThetaPrimeCubeRootResidue_average_mass_lower hp
  have hq : 1<norm p := cubicThetaPrimaryPrime_norm_gt_one hp
  have hpos : 0<(norm p)^3-(norm p)^2 := by
    have ht := mul_pos (sq_pos_of_pos (lt_trans zero_lt_one hq)) (sub_pos.mpr hq)
    nlinarith
  have hz : ‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖^2=0 := by
    have hp : ((norm p)^3-(norm p)^2)*‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖^2≤0 := by linarith
    apply le_antisymm ?_ (sq_nonneg _)
    by_contra hn
    have ht := mul_pos hpos (lt_of_not_ge hn)
    linarith
  apply norm_eq_zero.mp
  nlinarith [hz]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAverageIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Saturation of the actual trace bound identifies the zero-frequency
residue with its once-cubic dilation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidue_average_identity {p : Eisenstein} (hp : primaryPrime p) :
    (norm p:ℂ) • cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)=
    cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2 := by
  let P := cubicThetaPrimeCubeRootFourierL2 hp 0
    (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)
  let A := cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2
  let N := ‖cubicThetaArithmeticResidueL2‖^2
  have h1 : ¬p∣(1:Eisenstein) := fun hd => hp.2.not_isUnit (isUnit_iff_dvd_one.mpr hd)
  have hn := cubicThetaPrimeCubeRoot_norm_balance hp 1 h1 cubicThetaArithmeticResidueL2
  rw [cubicThetaArithmeticResidue_square_projection_zero hp 1 h1,norm_zero,
    zero_pow (by decide : 2≠0),mul_zero,add_zero] at hn
  have hnP : ‖(norm p:ℂ) • P‖^2=N := by
    rw [norm_smul,Complex.norm_of_nonneg (norm_nonneg p),mul_pow]
    exact hn
  have hnA : ‖A‖^2=N := by
    dsimp only [A,N]
    rw [(cubicThetaPrimeCubeRootDilationL2 hp).norm_map]
  have hi : inner ℂ ((norm p:ℂ) • P) A=(N:ℂ) := by
    rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),starRingEnd_apply]
    change star (norm p:ℂ)*inner ℂ P A=(N:ℂ)
    rw [show inner ℂ P A=(norm p:ℂ)⁻¹*(N:ℂ) from
      by simpa only [P,A,N,Complex.ofReal_pow] using
        cubicThetaPrimeCubeRootResidue_average_pairing hp]
    simp only [Complex.star_def,Complex.conj_ofReal]
    rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne')]
  have hs := norm_sub_sq (𝕜:=ℂ) ((norm p:ℂ) • P) A
  rw [hnP,hnA,hi] at hs
  change ‖(norm p:ℂ) • P-A‖^2=N-2*N+N at hs
  have hz : ‖(norm p:ℂ) • P-A‖=0 := by nlinarith [hs]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAverageObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading the saturated zero-frequency identity through actual cusp
observations, with the covering normalization cancelled. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_observation_lift {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeRootObservation hp h W
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap u))=
      ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
        inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspRestriction u) := by
  change inner ℂ _ (cubicThetaPrimeCubeRootCuspRestriction hp _)=_
  rw [cubicThetaPrimeCubeRootCuspRestriction_lift,inner_smul_right]

theorem cubicThetaArithmeticResidue_average_observation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    (norm p:ℂ)*inner ℂ (cubicThetaCuspFourierTest (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W))
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
    ((‖(p:ℂ)‖^3:ℝ):ℂ)^2*inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))) := by
  let V := cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
    (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W
  have he := congrArg (cubicThetaPrimeCubeRootObservation hp (p^3*h) V)
    (cubicThetaArithmeticResidue_average_identity hp)
  have hk : Ideal.Quotient.mk (modulus (p^3)) (p^3*h)=0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem,modulus,Ideal.mem_span_singleton]
    exact dvd_mul_right (p^3) h
  rw [map_smul,cubicThetaPrimeCubeRoot_observation_projection,ite_eq_left hk] at he
  change (norm p:ℂ)*cubicThetaPrimeCubeRootObservation hp (p^3*h) V
    (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap
      (cubicThetaArithmeticResidueEnergy (4/3))))=
      cubicThetaPrimeCubeRootObservation hp (p^3*h) V
        (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalEnergyValueMap
          (cubicThetaArithmeticResidueEnergy (4/3)))) at he
  rw [cubicThetaPrimeCubeRoot_observation_lift,
    cubicThetaPrimeCubeRoot_observation_dilation hp h W hW] at he
  have hc : (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ))≠0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (cubicThetaPrimeCubeRootCoverDegree_pos hp)).ne')
  apply mul_left_cancel₀ hc
  linear_combination he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeResiduePeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic periodicity of the actual arithmetic Fourier residues follows
from the saturated finite-cover averaging identity. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  let W := cubicThetaPrimeCubeResidueTestWeight hp
  let V := cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
    (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W
  have hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0 := fun _ hv => cubicThetaPrimeCubeResidueTestWeight_low hp hv
  have he := cubicThetaArithmeticResidue_average_observation hp h W hW
  have h3 := cubicThetaResidue_fourier_observation (mul_ne_zero (pow_ne_zero 3 hp.2.ne_zero) hh)
    V (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  have h0 := cubicThetaResidue_fourier_observation hh W (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at h3 h0
  have hscale : cubicThetaFourierRadialTest (p^3*h) V (4/3)=
      (norm p:ℂ)^2*cubicThetaFourierRadialTest h W (4/3) := by
    have hs := cubicThetaPoleRadialTest_scale (pow_ne_zero 3 hp.2.ne_zero) hh W (by
      intro v hv
      apply hW v
      simpa only [Subalgebra.coe_pow,norm_pow] using hv)
    rw [cubicThetaPrimeCube_pole_scale hp] at hs
    simpa only [Subalgebra.coe_pow,norm_pow] using hs
  have hn : ((‖(p:ℂ)‖^3:ℝ):ℂ)^2=(norm p:ℂ)^3 := by
    rw [show norm p=‖(p:ℂ)‖^2 from Complex.normSq_eq_norm_sq _,Complex.ofReal_pow,Complex.ofReal_pow]
    ring
  change (norm p:ℂ)*inner ℂ (cubicThetaCuspFourierTest (p^3*h) V)
    (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=_ at he
  rw [h3,h0,hscale,hn] at he
  have hf : (norm p:ℂ)^3*((Real.pi:ℂ)/Complex.Gamma (4/3))*
      cubicThetaFourierRadialTest h W (4/3)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne')
      · exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
          (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
    · exact cubicThetaPrimeCubeResidueTestWeight_radial_ne_zero hp hh
  apply mul_left_cancel₀ hf
  linear_combination he

end CubicFirstMoment

end

end OAI
end


