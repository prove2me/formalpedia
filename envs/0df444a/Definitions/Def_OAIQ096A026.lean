-- Prove2me | Definitions.Def_OAIQ096A026
-- name    : OAIQ096A026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T04:20:05.916561+00:00
-- url     : https://prove2.me/theorems/07ea662e-a492-4bab-b552-b4007258359f
-- title:
--   Definitions bundle OAIQ096A026 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 14 definitions and 91 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaArithmeticModelSection`, `OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass`, `OAI.CubicFirstMoment.cubicThetaNormalizedPrimaryProjection`, `OAI.CubicFirstMoment.cubicThetaNormalizedSeriesSection`, `OAI.CubicFirstMoment.cubicThetaNormalizedStabilizer`, `OAI.CubicFirstMoment.heckeLogSquaredConstant`, `OAI.CubicFirstMoment.heckePairLogConstant`, `OAI.CubicFirstMoment.heckePairZeroFreeError`, `OAI.CubicFirstMoment.heckeZeroFreeWidth`, `OAI.CubicFirstMoment.primeContourDecay`, `OAI.CubicFirstMoment.primeSmoothingParameter`, `OAI.CubicFirstMoment.primeSmoothingRate`, `OAI.CubicFirstMoment.principalPoleConstant`, `OAI.CubicFirstMoment.principalPoleRadius`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Estimates_HeckeDiskGrowth`, `CubicMoment_Estimates_HeckePrimeScales`, `CubicMoment_Estimates_HeckeUniformLogDerivative`, `CubicMoment_Estimates_HeckeZeroFreePair`, `CubicMoment_Estimates_PrimeSmoothingScale`, `CubicMoment_Estimates_PrincipalZetaLogDerivative`, `CubicMoment_Estimates_PrincipalZetaPole`, `CubicMoment_Theta_CubicThetaActualProjection`, `CubicMoment_Theta_CubicThetaArithmeticModelSection`, `CubicMoment_Theta_CubicThetaBorelRestriction`, `CubicMoment_Theta_CubicThetaCoefficientPrimaryReduction`, `CubicMoment_Theta_CubicThetaCoefficientScalar`, `CubicMoment_Theta_CubicThetaExtendedAutomorphy`, `CubicMoment_Theta_CubicThetaForcedResidue`, `CubicMoment_Theta_CubicThetaFourierParity`, `CubicMoment_Theta_CubicThetaInversionRestriction`, `CubicMoment_Theta_CubicThetaInvertedCusp`, `CubicMoment_Theta_CubicThetaInvertedFiniteFourier`, `CubicMoment_Theta_CubicThetaInvertedFourierObservable`, `CubicMoment_Theta_CubicThetaInvertedWindowContinuation`, `CubicMoment_Theta_CubicThetaModelGlobalL2`, `CubicMoment_Theta_CubicThetaModelRankinLimit`, `CubicMoment_Theta_CubicThetaNormalizedRamified`, `CubicMoment_Theta_CubicThetaNormalizedSeries`, `CubicMoment_Theta_CubicThetaPositiveFourierObservable`, `CubicMoment_Theta_CubicThetaPositiveModelIdentity`, `CubicMoment_Theta_CubicThetaPositiveModelObservation`, `CubicMoment_Theta_CubicThetaPositiveResidueObservation`, `CubicMoment_Theta_CubicThetaPositiveStripPairing`, `CubicMoment_Theta_CubicThetaPositiveZeroWindow`, `CubicMoment_Theta_CubicThetaPrimaryResidue`, `CubicMoment_Theta_CubicThetaPrimaryResidueIdentification`, `CubicMoment_Theta_CubicThetaPrimaryUnitResidue`, `CubicMoment_Theta_CubicThetaPrimeHeckeContinuation`, `CubicMoment_Theta_CubicThetaPrimeResidueObstruction`, `CubicMoment_Theta_CubicThetaPrimeSquareResidueZero`, `CubicMoment_Theta_CubicThetaRamifiedCoefficientScaling`, `CubicMoment_Theta_CubicThetaRamifiedForcingPhase`, `CubicMoment_Theta_CubicThetaRamifiedMissingCoefficient`, `CubicMoment_Theta_CubicThetaRamifiedMissingResidue`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryResidue`, `CubicMoment_Theta_CubicThetaRamifiedResidueFormula`, `CubicMoment_Theta_CubicThetaRamifiedResiduePeriodicity`, `CubicMoment_Theta_CubicThetaRamifiedResidueSystem`, `CubicMoment_Theta_CubicThetaRamifiedThreeTwists`, `CubicMoment_Theta_CubicThetaRegularizedFourier`, `CubicMoment_Theta_CubicThetaResidueInversion`, `CubicMoment_Theta_CubicThetaResidueKernelPairing`, `CubicMoment_Theta_CubicThetaResiduePrimarySupport`, `CubicMoment_Theta_CubicThetaScaledCoefficientReduction`, `CubicMoment_Theta_CubicThetaSquarefreeResidue`, `CubicMoment_Theta_CubicThetaWeightedResidue`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A024` and `OAIQ096A025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A030` and `OAIQ096A031`; the statements `OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold`, `OAI_CubicFirstMoment_cubicThetaFullDual_radial_voronoi`, `OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity`, `OAI_CubicFirstMoment_cubicThetaProjectedDirichlet_initial`, `OAI_CubicFirstMoment_cubicThetaProjectedDirichlet_right_bound`, `OAI_CubicFirstMoment_cubicThetaSelectedDirichlet_gamma`, `OAI_CubicFirstMoment_cubicThetaSelectedDirichlet_initial`, `OAI_CubicFirstMoment_cubicThetaSelectedDirichlet_left_bound`, `OAI_CubicFirstMoment_cubicThetaSelectedDirichlet_right_bound`, `OAI_CubicFirstMoment_cubicThetaSelected_radial_voronoi`, `OAI_CubicFirstMoment_cubicThetaSelected_voronoi`, `OAI_CubicFirstMoment_cubicTheta_completed_voronoi`, `OAI_CubicFirstMoment_cubicTheta_height_voronoi`, `OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_analytic_pair`, `OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_square_disk`, `OAI.CubicFirstMoment.hecke_zero_free_log_from_analytic_pair` and `OAI.CubicFirstMoment.hecke_zero_free_log_from_square_disk`; the proofs of `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_dilated_long_mean`, `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_dilated_negative_long_mean`, `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_radial_mean`, `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq`, `OAI.CubicFirstMoment.cubicThetaArithmeticRankinMass_unfold`, `OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity`, `OAI_CubicFirstMoment_cubicThetaProjectedDirichlet_right_bound`, `OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi`, `OAI.CubicFirstMoment.cubicThetaResidue_voronoi`, `OAI_CubicFirstMoment_cubicThetaScalarRankinKernel_residue`, `OAI_CubicFirstMoment_cubicThetaSelectedDirichlet_left_bound`, `OAI_CubicFirstMoment_cubicThetaSelectedDirichlet_right_bound`, `OAI_CubicFirstMoment_cubicThetaSelected_voronoi`, `OAI_CubicFirstMoment_cubicTheta_completed_voronoi`, `OAI_CubicFirstMoment_cubicTheta_height_voronoi`, `OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean`, `OAI.CubicFirstMoment.cubicTheta_radial_remainder_tail_mean`, `OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_analytic_pair`, `OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_square_disk`, `OAI.CubicFirstMoment.hecke_zero_free_log_from_analytic_pair`, `OAI.CubicFirstMoment.hecke_zero_free_log_from_square_disk`, `OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive`, `OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate` and `OAI_CubicFirstMoment_uniform_cubicTheta_radial_remainder_low`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A024
import Definitions.Def_OAIQ096A025

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

lemma principalZetaRegularFactor_one_ne_zero : principalZetaRegularFactor 1 ≠ 0 := by
  rw [principalZetaRegularFactor_one]
  exact div_ne_zero principalThetaConstant_ne_zero (Complex.ofReal_ne_zero.mpr
    (residueHeckeScale_pos (q := 1) one_ne_zero).ne')

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaLogDerivative
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pole contribution to the logarithmic derivative of the actual
principal ideal zeta function, with a bounded analytic remainder. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma principalIdealZeta_logDeriv_near_one :
    logDeriv principalIdealZeta =ᶠ[𝓝[≠] (1:ℂ)] fun s =>
      logDeriv principalZetaRegularFactor s-1/(s-1) := by
  have heq : principalIdealZeta =ᶠ[𝓝[≠] (1:ℂ)] fun s =>
      principalZetaRegularFactor s/(s-1) := by
    filter_upwards [(eventually_ne_nhds (one_ne_zero : (1:ℂ) ≠ 0)).filter_mono
      (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1),self_mem_nhdsWithin] with s hs hs1
    rw [principalZetaRegularFactor_eq hs hs1]
    exact (mul_div_cancel_left₀ (principalIdealZeta s) (sub_ne_zero.mpr hs1)).symm
  have hd := principalZetaRegularFactor_analyticAt_one.eventually_analyticAt.filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)
  have hn := (principalZetaRegularFactor_analyticAt_one.continuousAt.eventually
    (eventually_ne_nhds principalZetaRegularFactor_one_ne_zero)).filter_mono
      (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)
  filter_upwards [logDeriv_congr_nhdsNE heq,hd,hn,self_mem_nhdsWithin]
    with s he hd hn hs
  rw [he,logDeriv_div (f := principalZetaRegularFactor) (g := fun s : ℂ => s-1)
    s hn (sub_ne_zero.mpr hs) hd.differentiableAt (by fun_prop)]
  simp only [logDeriv_apply,deriv_sub_const,deriv_id'']

theorem principalIdealZeta_logDeriv_pole_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s in 𝓝[≠] (1:ℂ),
      ‖logDeriv principalIdealZeta s+1/(s-1)‖ ≤ C := by
  let C : ℝ := ‖logDeriv principalZetaRegularFactor 1‖+1
  have hcont : ContinuousAt (logDeriv principalZetaRegularFactor) 1 := by
    exact principalZetaRegularFactor_analyticAt_one.deriv.continuousAt.div
      principalZetaRegularFactor_analyticAt_one.continuousAt
      principalZetaRegularFactor_one_ne_zero
  have hb : ∀ᶠ s in 𝓝 (1:ℂ), ‖logDeriv principalZetaRegularFactor s‖ < C :=
    hcont.norm.eventually (eventually_lt_nhds (by dsimp [C]; linarith))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [principalIdealZeta_logDeriv_near_one,
    hb.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)] with s he hb
  rw [he,sub_add_cancel]
  exact hb.le

theorem principalIdealZeta_real_logDeriv_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1+δ →
      (-logDeriv principalIdealZeta (σ:ℂ)).re ≤ 1/(σ-1)+C := by
  obtain ⟨C,hC,hb⟩ := principalIdealZeta_logDeriv_pole_bound
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp hb
  refine ⟨C,δ,hC,hδ,?_⟩
  intro σ hσ hσδ
  have hmem : (σ:ℂ) ∈ Metric.ball (1:ℂ) δ ∩ {(1:ℂ)}ᶜ := by
    constructor
    · simp only [Metric.mem_ball,dist_eq_norm]
      have he : (σ:ℂ)-1=((σ-1:ℝ):ℂ) := by push_cast; rfl
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hσ)]
      linarith
    · simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
      exact_mod_cast hσ.ne'
  have he := (Complex.abs_re_le_norm _).trans (hδb hmem)
  have hr : (logDeriv principalIdealZeta (σ:ℂ)+1/((σ:ℂ)-1)).re=
      (logDeriv principalIdealZeta (σ:ℂ)).re+1/(σ-1) := by
    have hp : ((1/(σ-1):ℝ):ℂ)=1/((σ:ℂ)-1) := by push_cast; rfl
    rw [Complex.add_re,←hp,Complex.ofReal_re]
  rw [hr] at he
  simp only [Complex.neg_re]
  linarith [(abs_le.mp he).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeroFreePair
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-free step for a nonreal character and its square. The inputs
are the actual entire continuations and proved disk bounds; no prime-sum
or zero-free assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

def principalPoleConstant : ℝ := principalIdealZeta_real_logDeriv_bound.choose

def principalPoleRadius : ℝ := principalIdealZeta_real_logDeriv_bound.choose_spec.choose

def heckePairZeroFreeError (B B2 : ℝ) : ℝ :=
  1+3*principalPoleConstant+
    4*((diskLogDerivativeConstant/3)*Real.log B)+
    (diskLogDerivativeConstant/3)*Real.log B2+1/principalPoleRadius

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDiskGrowth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial and logarithmic conductor-height bounds for the actual
normalized Hecke disks. The constants depend only on the fixed ideal lattice. -/
noncomputable section
namespace CubicFirstMoment

def heckePairLogConstant : ℝ :=
  (1+3*principalPoleConstant+1/principalPoleRadius+
    5*(diskLogDerivativeConstant/3)*Real.log heckeDiskPolynomialConstant)/Real.log 10+
      20*diskLogDerivativeConstant

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeUniformLogDerivative
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single logarithmic width and a log-squared bound for an entire finite
Hecke contour. All zero-free information is derived from the analytic pair. -/
noncomputable section
namespace CubicFirstMoment

def heckeZeroFreeWidth (u : ℝ) : ℝ :=
  1/(32*(1+heckePairLogConstant)*(1+Real.log u))

def heckeLogSquaredConstant : ℝ :=
  ((diskLogDerivativeConstant+192*(1+heckePairLogConstant)/
    Real.log ((7/8:ℝ)/(3/4:ℝ)))/3)*(Real.log heckeDiskPolynomialConstant+12)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckePrimeScales
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete height and conductor scales for the prime contour. -/
noncomputable section
namespace CubicFirstMoment

def primeContourDecay : ℝ :=
  1/(64*(1+heckePairLogConstant)*(2+Real.log 32))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSmoothingScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing a cutoff width after its finite derivative order is known.
The same exponential saving absorbs the cutoff cost and the contour tail. -/
noncomputable section
namespace CubicFirstMoment

def primeSmoothingRate (d : ℕ) : ℝ := min primeContourDecay 1/(2*((d:ℝ)+1))
def primeSmoothingParameter (d : ℕ) (Q X : ℝ) : ℝ :=
  Real.exp (primeSmoothingRate d*(Real.log X/primeContourDenominator Q X))

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

theorem cubicThetaForcedEnergy_residue {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) •
      cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s))
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaArithmeticResidueEnergy σ)) :=
  cubicThetaForcedEnergy_residue_closed hσ hσ2.le

theorem cubicThetaForcedResolvent_residue_closed {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedResolvent s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))) := by
  have h := (cubicThetaGlobalInclusion.continuous.tendsto _).comp
    (cubicThetaForcedEnergy_residue_closed hσ hσ2)
  have hu : ∀ᶠ s : ℂ in 𝓝[≠] (σ:ℂ),
      IsUnit (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s)) :=
    (cubicThetaSpectralParameter_punctured hσ).eventually
      (cubicThetaEnergyPencil_eventually_unit (cubicThetaGlobalSpectralParameter_below_threshold
        (by simpa using hσ)))
  have he : (fun s : ℂ => cubicThetaGlobalInclusion ((s-(σ:ℂ)) •
      cubicThetaContinuedEnergyLift (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)))=ᶠ[𝓝[≠] (σ:ℂ)]
      (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedResolvent s) := by
    filter_upwards [hu] with s hs
    rw [map_smul,cubicThetaContinuedEnergyLift_value hs]
    rfl
  exact h.congr' he

theorem cubicThetaForcedResolvent_residue {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) :
    Tendsto (fun s : ℂ => (s-(σ:ℂ)) • cubicThetaForcedResolvent s)
      (𝓝[≠] (σ:ℂ)) (𝓝 (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))) :=
  cubicThetaForcedResolvent_residue_closed hσ hσ2.le

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

theorem cubicThetaRegularizedFrequency_residue {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedFrequency h (4/3)=cubicThetaArithmeticFourierResidue h (4/3) := by
  have ha := cubicThetaRegularizedFrequency_analytic hh (4/3) (by norm_num)
  have ht := cubicThetaFrequencyContinuation_residue hh (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat,smul_eq_mul] at ht
  have hg := cubicThetaRegularizedFrequency_germ hh (s:=(4/3:ℂ)) (by norm_num)
  exact tendsto_nhds_unique (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (ht.congr' hg.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierParity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evenness of the literal finite-row coefficients propagates to their
arithmetic continuation and to the actual theta residue. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_neg_germ {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) :
    cubicThetaFrequencyContinuation (-h)=ᶠ[𝓝[≠] s] cubicThetaFrequencyContinuation h := by
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic (neg_ne_zero.mpr hh) hz)
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic hh hz)
    (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
    (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz,cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_neg h z

theorem cubicThetaArithmeticFourierResidue_neg {h : Eisenstein} (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (-h) (4/3)=cubicThetaArithmeticFourierResidue h (4/3) := by
  have hn := cubicThetaFrequencyContinuation_residue (neg_ne_zero.mpr hh)
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  have hp := cubicThetaFrequencyContinuation_residue hh
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hn hp
  have he : (fun z : ℂ => (z-4/3)*cubicThetaFrequencyContinuation (-h) z)=ᶠ[𝓝[≠] (4/3:ℂ)]
      (fun z => (z-4/3)*cubicThetaFrequencyContinuation h z) := by
    filter_upwards [cubicThetaFrequencyContinuation_neg_germ hh (s:=(4/3:ℂ)) (by norm_num)]
      with z hz
    rw [hz]
  exact tendsto_nhds_unique (hn.congr' he) hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeHeckeContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaFrequencyContinuation_primeHecke_germ {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaFrequencyContinuation (p^3*h)=ᶠ[𝓝[≠] s]
      (fun z => (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaFrequencyContinuation h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaFrequencyContinuation (p*h) z) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hph : p*h≠0 := mul_ne_zero hp.2.ne_zero hh0
  have hp3h : p^3*h≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hh0
  have hrhs : MeromorphicOn (fun z =>
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaFrequencyContinuation h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaFrequencyContinuation (p*h) z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (((analyticAt_const.add (analyticAt_const.mul
        ((cubicThetaPrimeNormPower_analytic hp z).pow 3))).meromorphicAt.mul
          (cubicThetaFrequencyContinuation_meromorphic hh0 hz)).sub
      ((cubicThetaPrimeFirstFactor_analytic hp h z).meromorphicAt.mul
        (cubicThetaFrequencyContinuation_meromorphic hph hz)))
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic hp3h hz)
    hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz,cubicThetaFrequencyContinuation_right _ hz,
    cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_primeHecke hp (by linarith) h hh

theorem cubicThetaRegularizedFrequency_primeHecke {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaRegularizedFrequency (p^3*h) s=
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-s))^3)*cubicThetaRegularizedFrequency h s-
        cubicThetaPrimeFirstFactor p s h*cubicThetaRegularizedFrequency (p*h) s := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hph : p*h≠0 := mul_ne_zero hp.2.ne_zero hh0
  have hp3h : p^3*h≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hh0
  have he : cubicThetaRegularizedFrequency (p^3*h)=ᶠ[𝓝[≠] s]
      (fun z => (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaRegularizedFrequency h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaRegularizedFrequency (p*h) z) := by
    filter_upwards [cubicThetaRegularizedFrequency_germ hp3h hs,
      cubicThetaRegularizedFrequency_germ hh0 hs,cubicThetaRegularizedFrequency_germ hph hs,
      cubicThetaFrequencyContinuation_primeHecke_germ hp h hh hs] with z hz3 hz0 hz1 hz
    rw [hz3,hz0,hz1,hz]
    ring
  have hleft := (cubicThetaRegularizedFrequency_analytic hp3h s hs).continuousAt
  have hright : AnalyticAt ℂ (fun z =>
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-z))^3)*cubicThetaRegularizedFrequency h z-
        cubicThetaPrimeFirstFactor p z h*cubicThetaRegularizedFrequency (p*h) z) s :=
    ((analyticAt_const.add (analyticAt_const.mul
      ((cubicThetaPrimeNormPower_analytic hp s).pow 3))).mul
      (cubicThetaRegularizedFrequency_analytic hh0 s hs)).sub
    ((cubicThetaPrimeFirstFactor_analytic hp h s).mul
      (cubicThetaRegularizedFrequency_analytic hph s hs))
  exact tendsto_nhds_unique ((hleft.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

theorem cubicThetaArithmeticFourierResidue_primeHecke {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p ∣ h) :
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      (1+(norm p:ℂ)^3*((norm p:ℂ)^(-(4/3:ℂ)))^3)*
        cubicThetaArithmeticFourierResidue h (4/3)-
      cubicThetaPrimeFirstFactor p (4/3) h*cubicThetaArithmeticFourierResidue (p*h) (4/3) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hph : p*h≠0 := mul_ne_zero hp.2.ne_zero hh0
  have hp3h : p^3*h≠0 := mul_ne_zero (pow_ne_zero _ hp.2.ne_zero) hh0
  simpa only [cubicThetaRegularizedFrequency_residue hh0,
    cubicThetaRegularizedFrequency_residue hph,cubicThetaRegularizedFrequency_residue hp3h] using
      cubicThetaRegularizedFrequency_primeHecke hp h hh (s:=(4/3:ℂ)) (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPositiveFourierObservable_residue (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaPositiveFourierObservable h W hε hW s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) := by
  let P := cubicThetaPositiveFourierProfileL2 h W hε hW
  have ht := ((innerSL ℂ P).continuous.tendsto _).comp
    (cubicThetaForcedResolvent_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num))
  have hd : Tendsto (fun s : ℂ => (s-4/3)*
      cubicThetaArithmeticDistribution (cubicThetaPositiveFourierProfileSection h W hε hW)
        (cubicThetaPositiveFourierProfileSection_compact h W hε hW) s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (inner ℂ P
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) := by
    simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
      Complex.ofReal_div,Complex.ofReal_ofNat,cubicThetaArithmeticDistribution,
      P,cubicThetaPositiveFourierProfileL2] using ht
  have hi := (cubicThetaIncomingCompactIntegral_differentiable h W hε hW).continuous
    |>.continuousAt (x:=(4/3:ℂ))
  have hzero : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    have hz : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub_const _
    simpa only [sub_self] using hz.tendsto.mono_left nhdsWithin_le_nhds
  have hz' : Tendsto (fun s : ℂ => (s-4/3)*
      ∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s
        ∂cubicThetaPointMeasure) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using hzero.mul (hi.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [cubicThetaPositiveFourierObservable,mul_add,add_zero,P] using hd.add hz'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveResidueObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic normalization of the residue against every positive
compact Fourier test. The full low-height incoming correction is entire. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveFourierObservable_continued {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    {s : ℂ} (hs : 1 < s.re) :
    cubicThetaPositiveFourierObservable h W hε hW =ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaPositiveRadialTest h W ε z) := by
  have hobs : MeromorphicOn (cubicThetaPositiveFourierObservable h W hε hW)
      {z : ℂ | 1<z.re} := fun z hz => cubicThetaPositiveFourierObservable_meromorphic h W hε hW hz
  have hrhs : MeromorphicOn (fun z =>
      ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaFrequencyContinuation h z*
        cubicThetaPositiveRadialTest h W ε z) {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt).mul
        (cubicThetaFrequencyContinuation_meromorphic hh hz)).mul
          ((cubicThetaPositiveRadialTest_entire hh W hε).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hobs hrhs (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right h hz]
  exact cubicThetaPositiveFourierObservable_normalized hh W hε hW hz

theorem cubicThetaPositiveResidue_fourier_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=
      ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaArithmeticFourierResidue h (4/3)*
        cubicThetaPositiveRadialTest h W ε (4/3) := by
  have hG : ContinuousAt (fun s : ℂ => (Real.pi:ℂ)/Complex.Gamma s) (4/3:ℂ) :=
    continuousAt_const.div (cubicThetaGamma_analytic_right (by norm_num)).continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hR := (cubicThetaPositiveRadialTest_entire hh W hε).continuous.continuousAt (x:=(4/3:ℂ))
  have hF := cubicThetaFrequencyContinuation_residue hh (σ:=(4/3:ℝ))
    (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hF
  have ht := ((hG.tendsto.mono_left nhdsWithin_le_nhds).mul hF).mul
    (hR.tendsto.mono_left nhdsWithin_le_nhds)
  apply tendsto_nhds_unique (cubicThetaPositiveFourierObservable_residue h W hε hW)
  apply ht.congr'
  filter_upwards [cubicThetaPositiveFourierObservable_continued hh W hε hW
    (s:=(4/3:ℂ)) (by norm_num)] with s hs
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueKernelPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual residue pairs with any vector in the theta eigenspace
through the incoming forcing. Its compact-window equation reduces that
pairing to the constant cusp observation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaResidue_orthogonal_of_zero_cusp_mean (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0)
    (hmean : inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
      (cubicThetaCuspRestriction v)=0) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3))=0 := by
  rw [cubicThetaResidue_kernel_pairing v hv,cubicThetaKernel_window_balance v hv,
    ←inner_conj_symm,cubicThetaHighWindowPairing_energy,hmean,map_zero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeResidueObstruction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The critical local image condition is exactly the two missing
unramified residue identities. Neither identity is assumed here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeResidueVector_line_iff_cube {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p∣h) :
    (cubicThetaPrimeResidueVector p h 1=
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0) ↔
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  have hc := hp.2.coprime_iff_not_dvd.mpr hh
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hg := cubicThetaPrimeAdditiveGauss_product hp h hc
  have hG : cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ)≠0 :=
    div_ne_zero (cubicThetaPrimeCriticalGauss_ne_zero hp h hc) hq
  have he := cubicThetaArithmeticFourierResidue_primeHecke hp h hh
  rw [cubicThetaPrimeCubeFactor_pole hp,cubicThetaPrimeFirstFactor_critical hp h hc] at he
  have hidentity : cubicThetaArithmeticFourierResidue (p^3*h) (4/3)-
      cubicThetaArithmeticFourierResidue h (4/3)=
      -(cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ))*
        (cubicThetaPrimeResidueVector p h 1-
          (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0) := by
    rw [he]
    simp only [cubicThetaPrimeResidueVector,Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp
    linear_combination -(cubicThetaArithmeticFourierResidue h (4/3))*hg
  conv_rhs => rw [←sub_eq_zero,hidentity]
  simp only [mul_eq_zero,neg_eq_zero,hG,false_or,sub_eq_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeSquareResidueZero
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vanishing square projection is a vanishing of the actual
arithmetic Fourier residue, via a nonzero positive radial test. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_square_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaArithmeticFourierResidue (p^2*h) (4/3)=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hk0 : p^2*h≠0 := mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh0
  have hz := congrArg (cubicThetaPrimeCubeRootObservation hp (p^2*h) cubicThetaRadialTestWeight)
    (cubicThetaArithmeticResidue_square_projection_zero hp h hh)
  rw [map_zero,cubicThetaPrimeCubeRoot_observation_projection,ite_eq_left rfl] at hz
  change inner ℂ (cubicThetaCuspFourierTest (p^2*h) cubicThetaRadialTestWeight)
    (cubicThetaPrimeCubeRootCuspRestriction hp
      (cubicThetaPrimeCubeRootLiftL2 hp
        (cubicThetaGlobalEnergyValueMap (cubicThetaArithmeticResidueEnergy (4/3)))))=0 at hz
  rw [cubicThetaPrimeCubeRootCuspRestriction_lift,inner_smul_right] at hz
  have hc : (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ))≠0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (cubicThetaPrimeCubeRootCoverDegree_pos hp)).ne')
  have ho := (mul_eq_zero.mp hz).resolve_left hc
  have he := cubicThetaResidue_fourier_observation hk0 cubicThetaRadialTestWeight
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
  rw [ho] at he
  have hrad : cubicThetaFourierRadialTest (p^2*h) cubicThetaRadialTestWeight (4/3)≠0 := by
    have hp := cubicThetaFourierRadialTest_real_pos hk0 (4/3)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hp
    intro hz
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hgamma : (Real.pi:ℂ)/Complex.Gamma (4/3)≠0 :=
    div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hrad)).resolve_left hgamma

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightedResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unramified coefficient laws for the actual arithmetic residue in
the Whittaker normalization. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaWeightedFourierResidue_prime {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaWeightedFourierResidue (p*h)=
      (cubicSymbol p h*star (gauss p)/(Real.sqrt (norm p):ℂ))*
        cubicThetaWeightedFourierResidue h := by
  have hc := hp.2.coprime_iff_not_dvd.mpr hh
  have he := (cubicThetaPrimeResidueVector_line_iff_cube hp h hh).mpr
    (cubicThetaArithmeticFourierResidue_cube hp h (fun hz => hh (hz ▸ dvd_zero p)))
  change cubicThetaPrimeCriticalScale p*cubicThetaArithmeticFourierResidue (p*h) (4/3)=
    (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*
      cubicThetaArithmeticFourierResidue h (4/3) at he
  rw [cubicThetaPrimeAdditiveGauss_two hp h hc,cubicThetaPrimeAdditiveGauss_one hp h hc,
    star_mul,star_mul,star_star] at he
  have hs : star (Real.sqrt (norm p):ℂ)=(Real.sqrt (norm p):ℂ) := by simp
  rw [hs] at he
  have hn : (norm p:ℂ)=(Real.sqrt (norm p):ℂ)^2 := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (norm_nonneg p)]
  have hs0 : (Real.sqrt (norm p):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hp.2.ne_zero)).ne'
  have hnorm : (norm (p*h):ℂ)^(-(1/3:ℂ))=
      (norm p:ℂ)^(-(1/3:ℂ))*(norm h:ℂ)^(-(1/3:ℂ)) := by
    rw [norm_mul_eq,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg h)]
  unfold cubicThetaWeightedFourierResidue
  rw [hnorm]
  calc
    _ = (norm h:ℂ)^(-(1/3:ℂ))*(cubicThetaPrimeCriticalScale p*
        cubicThetaArithmeticFourierResidue (p*h) (4/3)) := by
      unfold cubicThetaPrimeCriticalScale
      ring
    _ = _ := by
      rw [he,hn]
      field_simp

lemma cubicThetaWeightedFourierResidue_square_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) : cubicThetaWeightedFourierResidue (p^2*h)=0 := by
  rw [cubicThetaWeightedFourierResidue,cubicThetaArithmeticFourierResidue_square_zero hp h hh,mul_zero]

lemma cubicThetaWeightedFourierResidue_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : h≠0) :
    cubicThetaWeightedFourierResidue (p^3*h)=
      (norm p:ℂ)⁻¹*cubicThetaWeightedFourierResidue h := by
  unfold cubicThetaWeightedFourierResidue
  rw [norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg (p^3)) (norm_nonneg h),cubicThetaNorm_cube_cpow,
    cubicThetaArithmeticFourierResidue_cube hp h hh]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSquarefreeResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime coefficient relations determine every primary squarefree
coefficient, retaining its one scalar base residue explicitly. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaWeightedFourierResidue_squarefree {b : Eisenstein}
    (hb : primary b) (hs : Squarefree b) :
    cubicThetaWeightedFourierResidue b=
      star (gauss b)/(Real.sqrt (norm b):ℂ)*cubicThetaWeightedFourierResidue 1 := by
  revert hs
  refine primary_induction (P:=fun b => Squarefree b →
    cubicThetaWeightedFourierResidue b=
      star (gauss b)/(Real.sqrt (norm b):ℂ)*cubicThetaWeightedFourierResidue 1) ?_ ?_ hb
  · intro _
    simp only [gauss_one,star_one,norm_one_eq,Real.sqrt_one,Complex.ofReal_one,div_one,one_mul]
  · intro p b hp hb ih hs
    have hc : IsCoprime p b := isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hs)
    have hpb : ¬p∣b := hp.2.coprime_iff_not_dvd.mp hc
    rw [cubicThetaWeightedFourierResidue_prime hp b hpb,ih hs.of_mul_right,
      gauss_mul hp.1 hb,star_mul,star_mul,star_star,cubic_reciprocity hb hp.1,
      norm_mul_eq,Real.sqrt_mul (norm_nonneg p),Complex.ofReal_mul]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete primary squarefree/cube coefficient identification, up to
the actual scalar base residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_primary_cube {d : Eisenstein}
    (hd : primary d) (h : Eisenstein) (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (d^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  revert h
  refine primary_induction (P:=fun d => ∀ h : Eisenstein, h≠0 →
    cubicThetaArithmeticFourierResidue (d^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3)) ?_ ?_ hd
  · intro h _
    simp only [one_pow,one_mul]
  · intro p d hp hd ih h hh
    rw [show (p*d)^3*h=p^3*(d^3*h) by ring,
      cubicThetaArithmeticFourierResidue_cube hp (d^3*h)
        (mul_ne_zero (pow_ne_zero 3 (primary_ne_zero hd)) hh)]
    exact ih h hh

theorem cubicThetaWeightedFourierResidue_primary_cube {d : Eisenstein}
    (hd : primary d) (h : Eisenstein) (hh : h≠0) :
    cubicThetaWeightedFourierResidue (d^3*h)=
      (norm d:ℂ)⁻¹*cubicThetaWeightedFourierResidue h := by
  unfold cubicThetaWeightedFourierResidue
  rw [norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg (d^3)) (norm_nonneg h),
    cubicThetaNorm_cube_cpow,cubicThetaArithmeticFourierResidue_primary_cube hd h hh]
  ring

theorem cubicThetaWeightedFourierResidue_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaWeightedFourierResidue (c*d^3)=
      star (gauss c)/((Real.sqrt (norm c):ℂ)*(norm d:ℂ))*
        cubicThetaWeightedFourierResidue 1 := by
  rw [mul_comm c (d^3),cubicThetaWeightedFourierResidue_primary_cube hd c (primary_ne_zero hc),
    cubicThetaWeightedFourierResidue_squarefree hc hs]
  ring

theorem cubicThetaWeightedFourierResidue_theta_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaWeightedFourierResidue (c*d^3)=
      (cubicThetaArithmeticCoefficient (lambdaE*c*d^3)/81)*
        cubicThetaWeightedFourierResidue 1 := by
  rw [cubicThetaWeightedFourierResidue_primary hc hd hs,
    cubicThetaArithmeticCoefficient_primary hc hd hs]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResiduePrimarySupport
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero primary residue has genuine squarefree/cube support.
Repeated prime cubes are removed by the proved arithmetic periodicity. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaWeightedFourierResidue_supported {b : Eisenstein}
    (hb : primary b) (hR : cubicThetaWeightedFourierResidue b≠0) :
    ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ b=c*d^3 := by
  have H : ∀ n : ℕ, ∀ b : Eisenstein, normNat b=n → primary b →
      cubicThetaWeightedFourierResidue b≠0 →
        ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ b=c*d^3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hn hb hR
      by_cases hs : Squarefree b
      · exact ⟨b,1,hb,primary_one,hs,by simp⟩
      obtain ⟨p,hp,hpp⟩ := exists_primary_prime_square_dvd hb hs
      by_cases h3 : p^3∣b
      · obtain ⟨d,rfl⟩ := h3
        have hd : primary d := primary_of_mul (cubicTheta_primary_cube hp.1) hb
        have hdR : cubicThetaWeightedFourierResidue d≠0 := by
          intro hz
          rw [cubicThetaWeightedFourierResidue_cube hp d (primary_ne_zero hd),hz,mul_zero] at hR
          exact hR rfl
        have hNp : 1<normNat p := by
          have he := cubicThetaPrimaryPrime_norm_gt_one hp
          rwa [←normNat_cast,Nat.one_lt_cast] at he
        have hNd : 0<normNat d := Nat.pos_of_ne_zero (normNat_ne_zero (primary_ne_zero hd))
        have hlt : normNat d<n := by
          rw [←hn,normNat_mul,show normNat (p^3)=(normNat p)^3 from map_pow normNatHom p 3]
          have hpow : 1<(normNat p)^3 := one_lt_pow₀ hNp (by decide : (3:ℕ)≠0)
          nlinarith
        obtain ⟨c,e,hc,he,hs,hde⟩ := ih (normNat d) hlt d rfl hd hdR
        refine ⟨c,p*e,hc,primary_mul hp.1 he,hs,?_⟩
        rw [hde]
        ring
      · obtain ⟨d,hbd⟩ := hpp
        have hd : ¬p∣d := by
          rintro ⟨e,he⟩
          apply h3
          refine ⟨e,?_⟩
          rw [hbd,he]
          ring
        have hz : cubicThetaWeightedFourierResidue b=0 := by
          rw [hbd,←pow_two,cubicThetaWeightedFourierResidue_square_zero hp d hd]
        exact (hR hz).elim
  exact H (normNat b) b rfl hb hR

theorem cubicThetaWeightedFourierResidue_primary_all {b : Eisenstein} (hb : primary b) :
    cubicThetaWeightedFourierResidue b=
      (cubicThetaArithmeticCoefficient (lambdaE*b)/81)*cubicThetaWeightedFourierResidue 1 := by
  by_cases hR : cubicThetaWeightedFourierResidue b=0
  · by_cases hc : Nonempty (CubicThetaCoordinates (lambdaE*b))
    · have hc' : Nonempty (CubicThetaCoordinates ((1:Eisensteinˣ)*lambdaE^1*b)) := by
        simpa only [Units.val_one,one_mul,pow_one] using hc
      obtain ⟨c,d,hpc,hpd,hsc,hb'⟩ := (cubicThetaCoordinates_primary_power_iff hb 1 1).mp hc'
      subst b
      simpa only [mul_assoc] using cubicThetaWeightedFourierResidue_theta_primary hpc hpd hsc
    · rw [cubicThetaArithmeticCoefficient,dite_eq_right hc,zero_div,zero_mul,hR]
  · obtain ⟨c,d,hc,hd,hs,hb'⟩ := cubicThetaWeightedFourierResidue_supported hb hR
    subst b
    simpa only [mul_assoc] using cubicThetaWeightedFourierResidue_theta_primary hc hd hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal inverted cusp restriction extends continuously from
finite-energy sections and agrees with inversion on the energy completion. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instAddCommGroupSubtypeContinuousMapCubicThetaPointComplexMemSubmoduleCubicThetaSectionCubicThetaFiniteEnergySections
lemma cubicThetaInvertedFiniteExtension_test (F : cubicThetaSmoothTests) :
    cubicThetaInvertedFiniteExtension (cubicThetaGlobalEnergyTest F)=
      cubicThetaCuspRestriction (cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F)) := by
  calc
    _ = cubicThetaInvertedFiniteRestriction (cubicThetaSmoothToFiniteEnergy F) := by
      rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaInvertedFiniteExtension_finite]
    _ = _ := by
      rw [cubicThetaInversionEnergy_test,
        ←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaCuspRestriction_finiteEnergy]
      rfl

theorem cubicThetaInvertedFiniteExtension_eq (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInvertedFiniteExtension u=
      cubicThetaCuspRestriction (cubicThetaInversionEnergy u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq cubicThetaInvertedFiniteExtension.continuous
      (cubicThetaCuspRestriction.continuous.comp cubicThetaInversionEnergy.continuous)) ?_
  exact cubicThetaInvertedFiniteExtension_test

theorem cubicThetaCuspRestriction_inversion_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaCuspRestriction (cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding F))=
      cubicThetaInvertedFiniteRestriction F :=
  (cubicThetaInvertedFiniteExtension_eq _).symm.trans (cubicThetaInvertedFiniteExtension_finite F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFiniteFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaRegularizedInvertedFrequency_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRegularizedPrimaryOne h s=(s-4/3)*cubicThetaInvertedFrequencyDirichlet h s := by
  rw [cubicThetaInvertedFrequencyDirichlet_eq]
  exact cubicThetaRegularizedPrimaryOne_right hh hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedWindowContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The computed inverted cusp mean continues as the bounded global
window observation. Its residue is the observation of the inverted residue. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaInvertedWindow_continued {s : ℂ} (hs : 1 < s.re) :
    cubicThetaInvertedWindowObservable =ᶠ[𝓝[≠] s]
      (fun z => cubicThetaInvertedScatteringFactor z*
        cubicThetaCuspFourierObservable 0 (cubicThetaHighWindowWeight (4/3)) z) := by
  have hL : MeromorphicOn cubicThetaInvertedWindowObservable {z : ℂ | 1<z.re} :=
    fun _ hz => cubicThetaInvertedWindowObservable_meromorphic hz
  have hR : MeromorphicOn (fun z => cubicThetaInvertedScatteringFactor z*
      cubicThetaCuspFourierObservable 0 (cubicThetaHighWindowWeight (4/3)) z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (cubicThetaInvertedScatteringFactor_analytic z).meromorphicAt.mul
      (cubicThetaCuspFourierObservable_meromorphic _ _ hz)
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaInvertedWindowObservable_normalized hz,
    cubicThetaCuspZeroObservable_normalized _ hz,cubicThetaInvertedConstantContinuation_factor]
  ring

theorem cubicThetaInvertedWindowObservable_residue :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedWindowObservable s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ (cubicThetaHighWindowL2 (4/3))
        (cubicThetaGlobalInclusion
          (cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3)))))) := by
  let T := (cubicThetaCompactSection_memLp cubicThetaInvertedWindowTest
    cubicThetaInvertedWindowTest.property.2).toLp (cubicThetaSectionRepresentative cubicThetaInvertedWindowTest)
  have h := ((innerSL ℂ T).continuous.tendsto _).comp
    (cubicThetaForcedResolvent_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num))
  have he : inner ℂ T (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=
      inner ℂ (cubicThetaHighWindowL2 (4/3))
        (cubicThetaGlobalInclusion
          (cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3)))) := by
    change inner ℂ (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest
      (cubicThetaInversionSmooth (cubicThetaHighWindowTest (4/3)))))
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=_
    rw [←cubicThetaInversionEnergy_test]
    exact cubicThetaInversionEnergy_mass_flip
      (cubicThetaGlobalEnergyTest (cubicThetaHighWindowTest (4/3))) _
  change Tendsto (fun s : ℂ => inner ℂ T ((s-((4/3:ℝ):ℂ)) • cubicThetaForcedResolvent s))
    (𝓝[≠] ((4/3:ℝ):ℂ)) (𝓝 (inner ℂ T
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))))) at h
  rw [he] at h
  simpa only [inner_smul_right,Complex.ofReal_div,Complex.ofReal_ofNat,
    cubicThetaInvertedWindowObservable,cubicThetaArithmeticDistribution,T] using h

theorem cubicThetaResidue_inverted_window_pairing :
    inner ℂ (cubicThetaHighWindowL2 (4/3))
      (cubicThetaGlobalInclusion
        (cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3))))=
    inner ℂ (cubicThetaHighWindowL2 (4/3))
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))) := by
  have hO := cubicThetaCuspObservable_residue
    (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hO
  have hF := (cubicThetaInvertedScatteringFactor_analytic (4/3:ℂ)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ))
  have ht := hF.mul hO
  simp only [cubicThetaInvertedScatteringFactor_pole,one_mul] at ht
  have hlim : Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedWindowObservable s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))))) := by
    apply ht.congr'
    filter_upwards [cubicThetaInvertedWindow_continued (s:=(4/3:ℂ)) (by norm_num)] with s hs
    change cubicThetaInvertedScatteringFactor s*
      ((s-4/3)*cubicThetaCuspFourierObservable 0 (cubicThetaHighWindowWeight (4/3)) s)=_
    rw [hs]
    ring
  exact (tendsto_nhds_unique cubicThetaInvertedWindowObservable_residue hlim).trans
    (cubicThetaHighWindowPairing_energy _ _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The equality of the physical cusp residues, together with the
spectral projection identity, forces inversion invariance of the full residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidueEnergy_inversion :
    cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3))=
      cubicThetaArithmeticResidueEnergy (4/3) := by
  let R := cubicThetaArithmeticResidueEnergy (4/3)
  have hR : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) R=0 := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      cubicThetaArithmeticResidueEnergy_kernel (4/3)
  have hU := cubicThetaInversionEnergy_kernel _ R hR
  have hD : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ))
      (R-cubicThetaInversionEnergy R)=0 := by rw [map_sub,hR,hU,sub_self]
  have hmean : inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
      (cubicThetaCuspRestriction (R-cubicThetaInversionEnergy R))=0 := by
    rw [map_sub,inner_sub_right,←cubicThetaHighWindowPairing_energy,
      ←cubicThetaHighWindowPairing_energy]
    exact sub_eq_zero.mpr cubicThetaResidue_inverted_window_pairing.symm
  have ho := cubicThetaResidue_orthogonal_of_zero_cusp_mean _ hD hmean
  change inner ℂ (R-cubicThetaInversionEnergy R) R=0 at ho
  rw [inner_sub_left] at ho
  have hc : inner ℂ (cubicThetaInversionEnergy R) R=inner ℂ R R :=
    (sub_eq_zero.mp ho).symm
  have hc' : inner ℂ R (cubicThetaInversionEnergy R)=inner ℂ R R := by
    exact (inner_conj_symm (𝕜:=ℂ) R (cubicThetaInversionEnergy R)).symm.trans
      ((congrArg (starRingEnd ℂ) hc).trans (inner_self_conj (𝕜:=ℂ) R))
  have hz : inner ℂ (R-cubicThetaInversionEnergy R) (R-cubicThetaInversionEnergy R)=0 := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hc,hc',
      cubicThetaInversionEnergy.inner_map_map]
    ring
  exact (sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp hz)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaInvertedForcedCusp_meromorphic {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt cubicThetaInvertedForcedCusp s :=
  cubicThetaMeromorphic_clm
    (cubicThetaCuspRestriction.comp cubicThetaInversionEnergy.toContinuousLinearMap)
    (cubicThetaForcedEnergy_meromorphic hs)

lemma cubicThetaInvertedForcedCusp_right {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedForcedCusp s=
      cubicThetaInvertedFiniteRestriction (cubicThetaArithmeticFiniteEnergy s hs) := by
  rw [cubicThetaInvertedForcedCusp,←cubicThetaArithmeticEnergy_eq_continued hs,
    ←cubicThetaArithmeticFiniteEnergy_embedding s hs,cubicThetaCuspRestriction_inversion_finite]

lemma cubicThetaInvertedForcedCusp_coe {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedForcedCusp s =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)]
      (fun p : CubicThetaPoint => cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s) := by
  rw [cubicThetaInvertedForcedCusp_right hs]
  have he := (cubicThetaSection_strip_memLp
    (cubicThetaInversionSection (cubicThetaArithmeticFiniteEnergy s hs))
    (cubicThetaInversionSection_memLp _ (cubicThetaArithmeticFiniteEnergy s hs).property.2.1)).coeFn_toLp
  filter_upwards [he,ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp hstrip
  have hv : (cubicThetaInvertedFiniteRestriction (cubicThetaArithmeticFiniteEnergy s hs)) p=
      cubicThetaArithmeticRemainder
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s := hp
  exact hv.trans (cubicThetaArithmeticRemainder_inverted
    (by have h:=hstrip.1; change 2<p.val.2 at h; linarith) s)

theorem cubicThetaInvertedForcedCusp_residue :
    Tendsto (fun s : ℂ => (s-4/3) • cubicThetaInvertedForcedCusp s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))) := by
  have h := ((cubicThetaCuspRestriction.comp
      cubicThetaInversionEnergy.toContinuousLinearMap).continuous.tendsto _).comp
    (cubicThetaForcedEnergy_residue (σ:=(4/3:ℝ)) (by norm_num) (by norm_num))
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    map_smul,Complex.ofReal_div,Complex.ofReal_ofNat,cubicThetaInvertedForcedCusp,
    cubicThetaArithmeticResidueEnergy_inversion] using h

theorem cubicThetaInvertedCuspObservable_meromorphic (T : CubicThetaStripL2)
    {s : ℂ} (hs : 1 < s.re) : MeromorphicAt (cubicThetaInvertedCuspObservable T) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ T) (cubicThetaInvertedForcedCusp_meromorphic hs)

theorem cubicThetaInvertedCuspObservable_residue (T : CubicThetaStripL2) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedCuspObservable T s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (inner ℂ T (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))))) := by
  have h := ((innerSL ℂ T).continuous.tendsto _).comp cubicThetaInvertedForcedCusp_residue
  simpa only [Function.comp_def,innerSL_apply_apply,inner_smul_right,
    cubicThetaInvertedCuspObservable] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaInvertedFourier_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W) (cubicThetaInvertedForcedCusp s)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    cubicThetaInvertedForcedCusp_coe hs] with p hp hE
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) _=_
  rw [hp,hE,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaInvertedFourierObservable_right (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedFourierObservable h W s=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaInvertedFourierObservable,cubicThetaInvertedCuspObservable,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    cubicThetaInvertedForcedCusp_coe hs] with p hp hE
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p) _=_
  rw [hp,hE,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
  ring

lemma cubicThetaInvertedFourierObservable_iterated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedFourierObservable h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaEisenstein
              (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s := by
  rw [cubicThetaInvertedFourierObservable_right h W hs]
  have hf := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y) s)
    (cubicThetaInvertedFourier_integrable h W hs)
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
    ∂cubicThetaPointMeasure)=_ at hf
  rw [hf]
  apply integral_congr_ae
  filter_upwards with v
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [star_mul]
  ring

theorem cubicThetaInvertedFourierObservable_normalized {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedFourierObservable h W s=
      ((Real.pi:ℂ)/Complex.Gamma s)*cubicThetaInvertedFrequencyDirichlet h s*
        cubicThetaFourierRadialTest h W s := by
  rw [cubicThetaInvertedFourierObservable_iterated h W hs,cubicThetaFourierRadialTest,
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaInverted_horizontal_coefficient (by have h:=hv; change 2<v at h; linarith)
    (by linarith) hh]
  have hphase : (Real.fourierChar (tracePair 0 (cubicThetaRowFrequency h)):ℂ)=1 := by simp [tracePair]
  simp only [cubicThetaInvertedNonzeroTerm,ite_eq_right hh,hphase,mul_one,Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))*
        (star (W v)*(v:ℂ)^s*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3)/
            Complex.Gamma s*cubicThetaInvertedFrequencyDirichlet h s := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryResidueIdentification
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The middle primary twist has the actual theta residue. This follows
from inversion of the global residue and actual Fourier observations. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaInvertedFourier_regularized_germ {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {s : ℂ} (hs : 1 < s.re) :
    (fun z => (z-4/3)*cubicThetaInvertedFourierObservable h W z)=ᶠ[𝓝[≠] s]
      (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*cubicThetaRegularizedPrimaryOne h z*
        cubicThetaFourierRadialTest h W z) := by
  have hL : MeromorphicOn (fun z => (z-4/3)*cubicThetaInvertedFourierObservable h W z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).meromorphicAt.mul
      (cubicThetaInvertedCuspObservable_meromorphic _ hz)
  have hR : MeromorphicOn (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedPrimaryOne h z*cubicThetaFourierRadialTest h W z)
      {z : ℂ | 1<z.re} := by
    intro z hz
    change 1<z.re at hz
    exact (((MeromorphicAt.const (Real.pi:ℂ) z).div
      (cubicThetaGamma_analytic_right (by linarith)).meromorphicAt).mul
      (cubicThetaRegularizedPrimaryOne_analytic hh z hz).meromorphicAt).mul
      ((cubicThetaFourierRadialTest_entire hh W).analyticAt z).meromorphicAt
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaInvertedFourierObservable_normalized hh W hz,
    cubicThetaRegularizedInvertedFrequency_right hh hz]
  ring

theorem cubicThetaInvertedFourier_residue {h : Eisenstein} (hh : h≠0) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
      ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaRegularizedPrimaryOne h (4/3)*
        cubicThetaFourierRadialTest h W (4/3) := by
  have hc : ContinuousAt (fun z => ((Real.pi:ℂ)/Complex.Gamma z)*
      cubicThetaRegularizedPrimaryOne h z*cubicThetaFourierRadialTest h W z) (4/3:ℂ) :=
    ((continuousAt_const.div (cubicThetaGamma_analytic_right (by norm_num : (0:ℝ)<(4/3:ℂ).re)).continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))).mul
      (cubicThetaRegularizedPrimaryOne_analytic hh (4/3) (by norm_num)).continuousAt).mul
      ((cubicThetaFourierRadialTest_entire hh W).analyticAt (4/3)).continuousAt
  have ht : Tendsto (fun z : ℂ => (z-4/3)*cubicThetaInvertedFourierObservable h W z)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (((Real.pi:ℂ)/Complex.Gamma (4/3))*
        cubicThetaRegularizedPrimaryOne h (4/3)*cubicThetaFourierRadialTest h W (4/3))) := by
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact (cubicThetaInvertedFourier_regularized_germ hh W (s:=(4/3:ℂ)) (by norm_num)).symm
  exact tendsto_nhds_unique
    (cubicThetaInvertedCuspObservable_residue (cubicThetaCuspFourierTest h W)) ht

theorem cubicThetaRegularizedPrimaryOne_residue_eq {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedPrimaryOne h (4/3)=cubicThetaArithmeticFourierResidue h (4/3) := by
  have hI := cubicThetaInvertedFourier_residue hh cubicThetaRadialTestWeight
  have hR := cubicThetaResidue_fourier_observation hh cubicThetaRadialTestWeight
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hR
  have hB : cubicThetaFourierRadialTest h cubicThetaRadialTestWeight (4/3:ℂ)≠0 := by
    intro hz
    have hp := cubicThetaFourierRadialTest_real_pos hh (4/3)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hp
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hK : (Real.pi:ℂ)/Complex.Gamma (4/3)≠0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  exact mul_left_cancel₀ hK (mul_right_cancel₀ hB (hI.symm.trans hR))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResiduePeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ramified cube periodicity of the actual arithmetic residue,
deduced from the identified primary residue. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaRegularizedPrimaryOne_lambda_cube {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) :
    cubicThetaRegularizedPrimaryOne (lambdaE^3*h) s=cubicThetaRegularizedPrimaryOne h s := by
  have h3 : lambdaE^3*h≠0 := mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh
  have he : cubicThetaRegularizedPrimaryOne (lambdaE^3*h)=ᶠ[𝓝[≠] s]
      cubicThetaRegularizedPrimaryOne h := by
    apply cubicThetaMeromorphic_identity
      (fun z hz => (cubicThetaRegularizedPrimaryOne_analytic h3 z hz).meromorphicAt)
      (fun z hz => (cubicThetaRegularizedPrimaryOne_analytic hh z hz).meromorphicAt)
      (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ)) (by norm_num) hs
    have hn : ∀ᶠ z in 𝓝 (4:ℂ), 3<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hn] with z hz
    rw [cubicThetaRegularizedPrimaryOne_right h3 hz,cubicThetaRegularizedPrimaryOne_right hh hz,
      cubicThetaPrimaryFourierSeries_lambda_cube]
  exact tendsto_nhds_unique
    (((cubicThetaRegularizedPrimaryOne_analytic h3 s hs).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' he)
    ((cubicThetaRegularizedPrimaryOne_analytic hh s hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

theorem cubicThetaArithmeticFourierResidue_lambda_cube {h : Eisenstein} (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (lambdaE^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  rw [←cubicThetaRegularizedPrimaryOne_residue_eq
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh),
    ←cubicThetaRegularizedPrimaryOne_residue_eq hh]
  exact cubicThetaRegularizedPrimaryOne_lambda_cube hh (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMissingResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first absent ramified class is absent from the actual continued
coefficient and its spectral residue, not merely from a formal model. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_lambda_missing_germ
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaFrequencyContinuation (lambdaE*h)=ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic
      (mul_ne_zero lambdaE_prime.ne_zero hh0) hz)
    (fun _ _ => analyticAt_const.meromorphicAt)
    (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
    (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_lambda_missing (by linarith) hh

theorem cubicThetaRegularizedFrequency_lambda_missing
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaRegularizedFrequency (lambdaE*h) s=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  have he : cubicThetaRegularizedFrequency (lambdaE*h)=ᶠ[𝓝[≠] s] (fun _ => 0) := by
    filter_upwards [cubicThetaRegularizedFrequency_germ
      (mul_ne_zero lambdaE_prime.ne_zero hh0) hs,
      cubicThetaFrequencyContinuation_lambda_missing_germ hh hs] with z hz hz0
    rw [hz,hz0,mul_zero]
  exact tendsto_nhds_unique
    (((cubicThetaRegularizedFrequency_analytic
      (mul_ne_zero lambdaE_prime.ne_zero hh0) s hs).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds).congr' he) tendsto_const_nhds

theorem cubicThetaArithmeticFourierResidue_lambda_missing
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaArithmeticFourierResidue (lambdaE*h) (4/3)=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  rw [← cubicThetaRegularizedFrequency_residue (mul_ne_zero lambdaE_prime.ne_zero hh0)]
  exact cubicThetaRegularizedFrequency_lambda_missing hh (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedThreeTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All three primary lambda twists inherit actual holomorphic
pole-cleared continuations by cycling the nonzero frequency. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaRegularizedPrimaryTwist_analytic (j : Fin 3)
    {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimaryTwist j h) {s : ℂ | 1 < s.re} :=
  cubicThetaRegularizedPrimaryOne_analytic
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh)

theorem cubicThetaRegularizedPrimaryTwist_right (j : Fin 3)
    {h : Eisenstein} (hh : h≠0) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRegularizedPrimaryTwist j h s=
      (s-4/3)*cubicThetaPrimaryFourierSeries 1 (j:ℕ) s h := by
  unfold cubicThetaRegularizedPrimaryTwist
  rw [cubicThetaRegularizedPrimaryOne_right
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh) hs,
    cubicThetaPrimaryFourierSeries_lambda_pow]
  congr 1
  fin_cases j
  · simpa only [Nat.reduceAdd,Nat.reduceMod] using
      cubicThetaPrimaryFourierSeries_period 1 0 s h
  · rfl
  · rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResidueSystem
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaRamifiedShortContinuation_analytic {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (cubicThetaRamifiedShortContinuation h) s := by
  unfold cubicThetaRamifiedShortContinuation
  simp only [tsum_fintype]
  apply Finset.analyticAt_fun_sum
  intro e _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (cubicThetaRamifiedFactor_analytic e j h s).mul
    (cubicThetaRegularizedPrimaryTwist_analytic j (mul_ne_zero hh e.ne_zero) s hs)

lemma cubicThetaRamifiedShortContinuation_right {h : Eisenstein} (hh : h≠0)
    (hM : ∀ n : ℕ, 3≤n → ¬lambdaE^n∣h) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaRamifiedShortContinuation h s=cubicThetaRegularizedFrequency h s := by
  rw [cubicThetaRegularizedFrequency_right hh hs,
    cubicThetaFrequencyDirichlet_primary_finite (by linarith) h 3 hM,
    cubicThetaRamifiedShortContinuation,tsum_fintype,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [cubicThetaRegularizedPrimaryTwist_right _ (mul_ne_zero hh e.ne_zero) hs,
    ←cubicThetaPrimaryFourierSeries_unit]
  simp only [Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  ring

theorem cubicThetaRamifiedShortContinuation_eq {h : Eisenstein} (hh : h≠0)
    (hM : ∀ n : ℕ, 3≤n → ¬lambdaE^n∣h) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaRamifiedShortContinuation h s=cubicThetaRegularizedFrequency h s := by
  have he : cubicThetaRamifiedShortContinuation h=ᶠ[𝓝[≠] s]
      cubicThetaRegularizedFrequency h := by
    apply cubicThetaMeromorphic_identity
      (fun z hz => (cubicThetaRamifiedShortContinuation_analytic hh hz).meromorphicAt)
      (fun z hz => (cubicThetaRegularizedFrequency_analytic hh z hz).meromorphicAt)
      (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
      (by change 1<(4:ℂ).re; norm_num) hs
    have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hn] with z hz
    exact cubicThetaRamifiedShortContinuation_right hh hM hz
  exact tendsto_nhds_unique
    (((cubicThetaRamifiedShortContinuation_analytic hh hs).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' he)
    ((cubicThetaRegularizedFrequency_analytic hh s hs).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)

theorem cubicThetaArithmeticFourierResidue_ramified_finite {h : Eisenstein} (hh : h≠0)
    (hM : ∀ n : ℕ, 3≤n → ¬lambdaE^n∣h) :
    cubicThetaArithmeticFourierResidue h (4/3)=
      ∑' e : Eisensteinˣ, ∑ j : Fin 3, cubicThetaRamifiedFactor e j (4/3) h*
        cubicThetaArithmeticFourierResidue (lambdaE^(((j:ℕ)+2)%3)*(h*(e:Eisenstein))) (4/3) := by
  rw [←cubicThetaRegularizedFrequency_residue hh,
    ←cubicThetaRamifiedShortContinuation_eq hh hM (by norm_num)]
  unfold cubicThetaRamifiedShortContinuation cubicThetaRegularizedPrimaryTwist
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro j _
  rw [cubicThetaRegularizedPrimaryOne_residue_eq
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) (mul_ne_zero hh e.ne_zero))]

theorem cubicThetaArithmeticFourierResidue_lambda_square_system
    {h : Eisenstein} (hh : ¬lambdaE∣h) :
    cubicThetaArithmeticFourierResidue (lambdaE^2*h) (4/3)=
      ∑' e : Eisensteinˣ,
        (cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*h)*
          cubicThetaArithmeticFourierResidue (lambdaE^2*(h*(e:Eisenstein))) (4/3)+
         cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*h)*
          cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  have hM (n : ℕ) (hn : 3≤n) : ¬lambdaE^n∣lambdaE^2*h := by
    intro hd
    have ht := (pow_dvd_pow lambdaE hn).trans hd
    rw [show (3:ℕ)=2+1 by omega,pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero 2 lambdaE_prime.ne_zero)] at ht
    exact hh ht
  rw [cubicThetaArithmeticFourierResidue_ramified_finite
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh0) hM]
  apply tsum_congr
  intro e
  have he0 : h*(e:Eisenstein)≠0 := mul_ne_zero hh0 e.ne_zero
  have hecop : ¬lambdaE∣h*(e:Eisenstein) := by
    intro hd
    rcases lambdaE_prime.dvd_mul.mp hd with hd | hd
    · exact hh hd
    · exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd e.isUnit)
  have hzero : cubicThetaArithmeticFourierResidue
      (lambdaE^2*(lambdaE^2*h*(e:Eisenstein))) (4/3)=0 := by
    rw [show lambdaE^2*(lambdaE^2*h*(e:Eisenstein))=
      lambdaE^3*(lambdaE*(h*(e:Eisenstein))) by ring,
      cubicThetaArithmeticFourierResidue_lambda_cube (mul_ne_zero lambdaE_prime.ne_zero he0),
      cubicThetaArithmeticFourierResidue_lambda_missing hecop]
  have hcube : cubicThetaArithmeticFourierResidue
      (lambdaE*(lambdaE^2*h*(e:Eisenstein))) (4/3)=
      cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3) := by
    rw [show lambdaE*(lambdaE^2*h*(e:Eisenstein))=lambdaE^3*(h*(e:Eisenstein)) by ring,
      cubicThetaArithmeticFourierResidue_lambda_cube he0]
  simp only [Fin.sum_univ_three,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.reduceAdd,
    Nat.reduceMod,pow_zero,one_mul,pow_one,hzero,hcube,mul_zero,zero_add]
  rw [mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMissingCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Agreement of the actual and prescribed coefficients in the first
absent ramified class. The frequency index is exactly -lambda*h. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNormalizedObservedCoefficient_lambda_missing
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) :
    cubicThetaNormalizedObservedCoefficient (lambdaE*h)=0 := by
  simp only [cubicThetaNormalizedObservedCoefficient,cubicThetaObservedWhittakerCoefficient,
    cubicThetaArithmeticFourierResidue_lambda_missing hh,mul_zero,zero_mul,zero_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimaryResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed-primary selection rule holds for the actual residue and
matches the prescribed coefficient on the same arithmetic frequency. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaFrequencyContinuation_primary_support_germ
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h))
    {s : ℂ} (hs : 1 < s.re) :
    cubicThetaFrequencyContinuation h=ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  apply cubicThetaMeromorphic_identity
    (fun z hz => cubicThetaFrequencyContinuation_meromorphic hh0 hz)
    (fun _ _ => analyticAt_const.meromorphicAt)
    (convex_halfSpace_re_gt 1).isPreconnected (z₀:=(4:ℂ))
    (by change 1<(4:ℂ).re; norm_num) hs
  have hn : ∀ᶠ z : ℂ in 𝓝 4, 3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  rw [cubicThetaFrequencyContinuation_right _ hz]
  exact cubicThetaFrequencyDirichlet_primary_support (by linarith) hh hpos hneg

theorem cubicThetaArithmeticFourierResidue_primary_support
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaArithmeticFourierResidue h (4/3)=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero lambdaE)
  have ht := cubicThetaFrequencyContinuation_residue hh0
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at ht
  have he : (fun z : ℂ => (z-4/3)*cubicThetaFrequencyContinuation h z)=ᶠ[𝓝[≠] (4/3:ℂ)]
      (fun _ => 0) := by
    filter_upwards [cubicThetaFrequencyContinuation_primary_support_germ hh hpos hneg
      (s:=(4/3:ℂ)) (by norm_num)] with z hz
    rw [hz,mul_zero]
  exact tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds

theorem cubicThetaNormalizedObservedCoefficient_primary_support_eq
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaNormalizedObservedCoefficient h=cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [cubicThetaArithmeticCoefficient_signed_primary_support hh hpos hneg]
  simp only [cubicThetaNormalizedObservedCoefficient,cubicThetaObservedWhittakerCoefficient,
    cubicThetaArithmeticFourierResidue_primary_support hh hpos hneg,
    mul_zero,zero_mul,zero_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryUnitResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base residue on the six-unit orbit of a primary frequency is
supported precisely on the two signed primary representatives. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_primary_unit {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)=
      if e=1 ∨ e=-1 then cubicThetaArithmeticFourierResidue h (4/3) else 0 := by
  by_cases he : e=1 ∨ e=-1
  · rw [ite_eq_left he]
    rcases he with he | he
    · subst e
      simp
    · subst e
      simpa using cubicThetaArithmeticFourierResidue_neg (primary_ne_zero hh)
  · rw [ite_eq_right he]
    have hn : ¬lambdaE∣h*(e:Eisenstein) := by
      intro hd
      rcases lambdaE_prime.dvd_mul.mp hd with hd | hd
      · exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hh).isRelPrime hd dvd_rfl)
      · exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd e.isUnit)
    apply cubicThetaArithmeticFourierResidue_primary_support hn
    · intro hp
      exact he (Or.inl ((cubicThetaPrimary_mul_unit_iff hh e).mp hp))
    · intro hp
      have hneg : primary (h*((-e:Eisensteinˣ):Eisenstein)) := by simpa using hp
      have hu := (cubicThetaPrimary_mul_unit_iff hh (-e)).mp hneg
      exact he (Or.inr (neg_eq_iff_eq_neg.mp hu))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedForcingPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The forcing in the actual ramified unit system is the same explicit
modulus-nine phase, multiplied by the primary base residue. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaRamifiedForcing_phase {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    (∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
        cubicThetaArithmeticFourierResidue (h*omegaE^(j:ℕ)*(e:Eisenstein)) (4/3))=
      ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3) := by
  let d : Eisensteinˣ := cubicThetaOmegaUnit^(j:ℕ)
  have hd : (d:Eisenstein)=omegaE^(j:ℕ) := by
    simp only [d,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne]
  let F (e : Eisensteinˣ) :=
    cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
      cubicThetaArithmeticFourierResidue (h*omegaE^(j:ℕ)*(e:Eisenstein)) (4/3)
  have hpos : F (d⁻¹)=0 := by
    have hi : ((d⁻¹:Eisensteinˣ):Eisenstein)=omegaE^(cubicThetaInverseUnitIndex j:ℕ) := by
      have he := cubicThetaNegativeInverseUnit_power j
      change -((d⁻¹:Eisensteinˣ):Eisenstein)=_ at he
      exact neg_inj.mp he
    have hz := cubicThetaRamifiedTopFactor_positive_zero (d⁻¹)
      (cubicThetaLambda_dvd_primary_omega_sub_one hh j)
      (hi ▸ cubicThetaLambda_dvd_omega_pow_sub_one (cubicThetaInverseUnitIndex j))
    dsimp only [F]
    rw [hz,zero_mul]
  have hneg : F (-(d⁻¹))=
      ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3) := by
    dsimp only [F]
    rw [cubicThetaRamifiedTop_negative_inverse hh j]
    have he : h*omegaE^(j:ℕ)*((-(d⁻¹):Eisensteinˣ):Eisenstein)=-h := by
      rw [←hd,Units.val_neg,mul_neg,mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,mul_one]
    rw [he,cubicThetaArithmeticFourierResidue_neg (primary_ne_zero hh)]
  have hzero (e : Eisensteinˣ) (he : e≠d⁻¹) (he' : e≠-(d⁻¹)) : F e=0 := by
    have hunit : ¬(d*e=1 ∨ d*e=-1) := by
      rintro (hu | hu)
      · apply he
        calc e=d⁻¹*(d*e) := by group
             _=d⁻¹ := by rw [hu,mul_one]
      · apply he'
        calc e=d⁻¹*(d*e) := by group
             _=-(d⁻¹) := by rw [hu,mul_neg,mul_one]
    dsimp only [F]
    have hx : h*omegaE^(j:ℕ)*(e:Eisenstein)=h*((d*e:Eisensteinˣ):Eisenstein) := by
      rw [Units.val_mul,hd,mul_assoc]
    rw [hx,cubicThetaArithmeticFourierResidue_primary_unit hh,ite_eq_right hunit,mul_zero]
  have hp (e : Eisensteinˣ) : F e=if e=-(d⁻¹) then F (-(d⁻¹)) else 0 := by
    by_cases he : e=-(d⁻¹)
    · subst e
      exact (ite_eq_left rfl).symm
    · rw [ite_eq_right he]
      by_cases he' : e=d⁻¹
      · rw [he',hpos]
      · exact hzero e he' he
  change (∑' e : Eisensteinˣ, F e)=_
  rw [show (∑' e : Eisensteinˣ, F e)=∑' e : Eisensteinˣ,
      (if e=-(d⁻¹) then F (-(d⁻¹)) else 0) from tsum_congr hp,tsum_ite_eq]
  exact hneg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResidueFormula
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaRamifiedPhaseCandidate_system {h : Eisenstein} (hh : primary h)
    (d : Eisensteinˣ) :
    cubicThetaRamifiedPhaseCandidate h d=
      cubicThetaRamifiedUnitOperator 1 h (cubicThetaRamifiedPhaseCandidate h) d+
      cubicThetaRamifiedUnitOperator 2 h
        (fun e => cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)) d := by
  have hpos (j : Fin 3) : cubicThetaRamifiedPhaseCandidate h (cubicThetaOmegaUnit^(j:ℕ))=
      cubicThetaRamifiedUnitOperator 1 h (cubicThetaRamifiedPhaseCandidate h)
        (cubicThetaOmegaUnit^(j:ℕ))+
      cubicThetaRamifiedUnitOperator 2 h
        (fun e => cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3))
        (cubicThetaOmegaUnit^(j:ℕ)) := by
    let u : Eisensteinˣ := cubicThetaOmegaUnit^(j:ℕ)
    have hu : (u:Eisenstein)=omegaE^(j:ℕ) := by
      simp only [u,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne]
    have hm : cubicThetaRamifiedUnitOperator 1 h
        (fun e => cubicThetaNinePhase ((e:Eisenstein)^2*h)) u=
        (2/3:ℂ)*cubicThetaNinePhase ((u:Eisenstein)^2*h) := by
      simpa only [cubicThetaRamifiedUnitOperator,Units.val_mul,hu] using
        cubicThetaRamifiedMiddle_phase_eigen hh j
    have hb : cubicThetaRamifiedUnitOperator 2 h
        (fun e => cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)) u=
        ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((u:Eisenstein)^2*h)*
          cubicThetaArithmeticFourierResidue h (4/3) := by
      simpa only [cubicThetaRamifiedUnitOperator,Units.val_mul,hu,mul_assoc] using
        cubicThetaRamifiedForcing_phase hh j
    change cubicThetaRamifiedPhaseCandidate h u= _
    unfold cubicThetaRamifiedPhaseCandidate
    rw [cubicThetaRamifiedUnitOperator_mul_left,cubicThetaRamifiedUnitOperator_mul_right,hm,hb]
    ring
  obtain ⟨j,hj | hj⟩ := cubicThetaUnit_signed_power d
  · have he : d=cubicThetaOmegaUnit^(j:ℕ) := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using hj
    rw [he]
    exact hpos j
  · have he : d=-(cubicThetaOmegaUnit^(j:ℕ)) := by
      apply Units.ext
      simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using hj
    rw [he,cubicThetaRamifiedPhaseCandidate_neg,cubicThetaRamifiedUnitOperator_neg,
      cubicThetaRamifiedUnitOperator_neg]
    exact hpos j

theorem cubicThetaArithmeticFourierResidue_lambda_square_unit {h : Eisenstein}
    (hh : primary h) (d : Eisensteinˣ) :
    cubicThetaArithmeticFourierResidue (lambdaE^2*(h*(d:Eisenstein))) (4/3)=
      (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase ((d:Eisenstein)^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3)) := by
  let f (e : Eisensteinˣ) := cubicThetaArithmeticFourierResidue
    (lambdaE^2*(h*(e:Eisenstein))) (4/3)
  let b (e : Eisensteinˣ) := cubicThetaRamifiedUnitOperator 2 h
    (fun u => cubicThetaArithmeticFourierResidue (h*(u:Eisenstein)) (4/3)) e
  have hf (e : Eisensteinˣ) : f e=(∑' u : Eisensteinˣ,
      cubicThetaRamifiedFactor u 1 (4/3) (lambdaE^2*(h*(e:Eisenstein)))*f (e*u))+b e := by
    have hc : ¬lambdaE∣h*(e:Eisenstein) := by
      intro hd
      rcases lambdaE_prime.dvd_mul.mp hd with hd | hd
      · exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hh).isRelPrime hd dvd_rfl)
      · exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd e.isUnit)
    dsimp only [f,b,cubicThetaRamifiedUnitOperator]
    rw [cubicThetaArithmeticFourierResidue_lambda_square_system hc,
      ←Summable.tsum_add Summable.of_finite Summable.of_finite]
    apply tsum_congr
    intro u
    rw [Units.val_mul,mul_assoc]
  have hg (e : Eisensteinˣ) : cubicThetaRamifiedPhaseCandidate h e=(∑' u : Eisensteinˣ,
      cubicThetaRamifiedFactor u 1 (4/3) (lambdaE^2*(h*(e:Eisenstein)))*
        cubicThetaRamifiedPhaseCandidate h (e*u))+b e :=
    cubicThetaRamifiedPhaseCandidate_system hh e
  have he := cubicThetaRamifiedUnitSystem_unique (cubicThetaLambda_dvd_primary_sub_one hh)
    b f (cubicThetaRamifiedPhaseCandidate h) hf hg
  exact congrFun he d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedRamified
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit ramified residue solution in the normalized Whittaker
coefficient used by the Patterson theta expansion. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNormalizedObservedCoefficient_lambda_square_unit {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^2*(h*(e:Eisenstein)))=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*h)*cubicThetaNormalizedObservedCoefficient h := by
  have h0 := primary_ne_zero hh
  have hu : lambdaE^2*(e:Eisenstein)≠0 :=
    mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) e.ne_zero
  have hU : lambdaE^2*(h*(e:Eisenstein))=(lambdaE^2*(e:Eisenstein))*h := by ring
  have hN : norm (lambdaE^2*(e:Eisenstein))=9 := by
    rw [norm_mul_eq,norm_of_isUnit e.isUnit,mul_one,cubicThetaNorm_lambda_pow]
    norm_num
  have hw := cubicThetaPoleWeight_mul hu h0
  rw [hN] at hw
  have hR : cubicThetaArithmeticFourierResidue ((lambdaE^2*(e:Eisenstein))*h) (4/3)=
      (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase ((e:Eisenstein)^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3)) := by
    rw [←hU]
    exact cubicThetaArithmeticFourierResidue_lambda_square_unit hh e
  let K : ℂ := cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
    ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)/
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  have hL : cubicThetaNormalizedObservedCoefficient (lambdaE^2*(h*(e:Eisenstein)))=
      K*((Complex.ofReal ((9:ℝ)^(-(1/3:ℝ))))*(3:ℂ)^(-(1/3:ℂ)))*
        cubicThetaNinePhase ((e:Eisenstein)^2*h)*cubicThetaArithmeticFourierResidue h (4/3) := by
    unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    rw [hU,hw,hR]
    dsimp only [K]
    push_cast
    ring
  have hB : cubicThetaNormalizedObservedCoefficient h=K*cubicThetaArithmeticFourierResidue h (4/3) := by
    unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    dsimp only [K]
    ring
  rw [hL,hB,cubicThetaRamifiedWhittaker_scale]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCoefficientScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified cube scaling agrees with the normalization of the
published arithmetic coefficient on every positive ramified order. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaNormalizedObservedCoefficient_lambda_cube {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^3*h)=
      (1/3:ℂ)*cubicThetaNormalizedObservedCoefficient h := by
  have hN : norm lambdaE=3 := by simpa only [pow_one] using cubicThetaNorm_lambda_pow 1
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
  rw [cubicThetaArithmeticFourierResidue_lambda_cube hh,
    cubicThetaPoleWeight_cube_mul lambdaE_prime.ne_zero hh,hN]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientPrimaryReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaNormalizedObservedCoefficient_neg {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient (-h)=cubicThetaNormalizedObservedCoefficient h := by
  have hn : norm (-1:Eisenstein)=1 := by
    change Complex.normSq (-1:ℂ)=1
    norm_num
  have hw := cubicThetaPoleWeight_mul (u:=(-1:Eisenstein)) (by norm_num) hh
  rw [hn] at hw
  simp only [neg_one_mul,Real.one_rpow,one_mul] at hw
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
  rw [cubicThetaArithmeticFourierResidue_neg hh,hw]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScaledCoefficientReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary-to-global reduction also preserves one common
scalar normalization of the nonconstant Fourier coefficients. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScaledAgreement_lambda_cube (A : ℂ) {h : Eisenstein} (hh : h≠0)
    (he : cubicThetaNormalizedObservedCoefficient h=A*cubicThetaArithmeticCoefficient (-lambdaE*h)) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^3*h)=
      A*cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^3*h)) := by
  rw [cubicThetaNormalizedObservedCoefficient_lambda_cube hh,he,
    show -lambdaE*(lambdaE^3*h)=lambdaE^3*(-lambdaE*h) by ring,
    cubicThetaArithmeticCoefficient_lambdaCube (show lambdaE∣-lambdaE*h from ⟨-h,by ring⟩)]
  ring

lemma cubicThetaScaledAgreement_lambda_cube_pow (A : ℂ) {h : Eisenstein} (hh : h≠0)
    (he : cubicThetaNormalizedObservedCoefficient h=A*cubicThetaArithmeticCoefficient (-lambdaE*h))
    (k : ℕ) :
    cubicThetaNormalizedObservedCoefficient (lambdaE^(3*k)*h)=
      A*cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^(3*k)*h)) := by
  induction k with
  | zero => simpa only [mul_zero,pow_zero,one_mul] using he
  | succ k ih =>
    have ht : lambdaE^(3*(k+1))*h=lambdaE^3*(lambdaE^(3*k)*h) := by
      rw [Nat.mul_add,pow_add]
      ring
    rw [ht]
    exact cubicThetaScaledAgreement_lambda_cube A
      (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hh) ih

theorem cubicThetaScaledCoefficientAgreement_primary (A : ℂ)
    (H : ∀ h : Eisenstein, primary h → cubicThetaNormalizedObservedCoefficient h=
      A*cubicThetaArithmeticCoefficient (-lambdaE*h)) :
    ∀ h : Eisenstein, h≠0 → cubicThetaNormalizedObservedCoefficient h=
      A*cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  have H0 (h : Eisenstein) (hh : ¬lambdaE∣h) :
      cubicThetaNormalizedObservedCoefficient h=A*cubicThetaArithmeticCoefficient (-lambdaE*h) := by
    by_cases hp : primary h
    · exact H h hp
    by_cases hn : primary (-h)
    · have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero lambdaE)
      rw [←cubicThetaNormalizedObservedCoefficient_neg h0,H (-h) hn,
        show -lambdaE*(-h)=-(-lambdaE*h) by ring,cubicThetaArithmeticCoefficient_even]
    · rw [cubicThetaNormalizedObservedCoefficient_primary_support_eq hh hp hn,
        cubicThetaArithmeticCoefficient_signed_primary_support hh hp hn,mul_zero]
  have H2 (h : Eisenstein) (hh : ¬lambdaE∣h) :
      cubicThetaNormalizedObservedCoefficient (lambdaE^2*h)=
        A*cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^2*h)) := by
    obtain ⟨a,e,ha,he⟩ := cubicThetaPrimaryRepresentative hh
    rw [he,cubicThetaNormalizedObservedCoefficient_lambda_square_unit ha,
      cubicThetaArithmeticCoefficient_ramified_signed ha,H a ha]
    ring
  intro h hh
  obtain ⟨k,u,hu,he⟩ := WfDvdMonoid.max_power_factor hh lambdaE_prime.irreducible
  have hu0 : u≠0 := fun hz => by rw [hz,mul_zero] at he; exact hh he
  have hr : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
  rw [he,show lambdaE^k*u=lambdaE^(3*(k/3))*(lambdaE^(k%3)*u) by
    rw [←mul_assoc,←pow_add]; congr 2; omega]
  apply cubicThetaScaledAgreement_lambda_cube_pow A
    (mul_ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero) hu0)
  rcases hr with hr | hr | hr
  · simpa only [hr,pow_zero,one_mul] using H0 u hu
  · simp only [hr,pow_one,cubicThetaNormalizedObservedCoefficient_lambda_missing hu,
      show -lambdaE*(lambdaE*u)=-(lambdaE^2*u) by ring,
      cubicThetaArithmeticCoefficient_even,cubicThetaArithmeticCoefficient_ramified_two hu,mul_zero]
  · simpa only [hr] using H2 u hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientScalar
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonconstant coefficient of the actual arithmetic residue is
now the explicit Patterson coefficient times a single scalar. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoefficientScalar_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticBaseScalar*cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [cubicThetaNormalizedObservedCoefficient_weighted (primary_ne_zero hh),
    cubicThetaWeightedFourierResidue_primary_all hh]
  rw [neg_mul,cubicThetaArithmeticCoefficient_even]
  unfold cubicThetaArithmeticBaseScalar
  rw [cubicThetaNormalizedObservedCoefficient_one]
  ring

theorem cubicThetaCoefficientScalar {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient h=
      cubicThetaArithmeticBaseScalar*cubicThetaArithmeticCoefficient (-lambdaE*h) :=
  cubicThetaScaledCoefficientAgreement_primary cubicThetaArithmeticBaseScalar
    (fun _ hb => cubicThetaCoefficientScalar_primary hb) h hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveZeroWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPositiveResidue_zero_observation (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 0 W hε hW)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)))=
      (3*Real.pi:ℂ)*cubicThetaScatteringResidue*mellin (star W) (-(4/3:ℂ)) := by
  have hm := (cubicThetaPositiveWindow_entire W hε hW).continuous
  have hA : ContinuousAt (fun s : ℂ =>
      ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (s-2)) (4/3) :=
    continuousAt_const.mul (hm.continuousAt.comp (continuousAt_id.sub_const 2))
  have hB : ContinuousAt (fun s : ℂ =>
      (Real.pi:ℂ)/(s-1)*mellin (star W) (-s)) (4/3) :=
    (continuousAt_const.div (continuousAt_id.sub_const 1) (by norm_num)).mul
      (hm.continuousAt.comp continuousAt_id.neg)
  have hz : Tendsto (fun s : ℂ => s-4/3) (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    have hc : ContinuousAt (fun s : ℂ => s-4/3) (4/3:ℂ) :=
      continuousAt_id.sub_const _
    simpa only [sub_self] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (hz.mul (hA.tendsto.mono_left nhdsWithin_le_nhds)).add
    ((hB.tendsto.mono_left nhdsWithin_le_nhds).mul cubicThetaConstantContinuation_residue)
  change Tendsto _ _ (𝓝 ((0:ℂ)*
    (((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) ((4/3:ℂ)-2))+
    ((Real.pi:ℂ)/((4/3:ℂ)-1)*mellin (star W) (-(4/3:ℂ)))*
      cubicThetaScatteringResidue)) at ht
  have hl : (0:ℂ)*(((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) ((4/3:ℂ)-2))+
      ((Real.pi:ℂ)/((4/3:ℂ)-1)*mellin (star W) (-(4/3:ℂ)))*cubicThetaScatteringResidue=
      (3*Real.pi:ℂ)*cubicThetaScatteringResidue*mellin (star W) (-(4/3:ℂ)) := by ring
  rw [hl] at ht
  apply tendsto_nhds_unique (cubicThetaPositiveFourierObservable_residue 0 W hε hW)
  apply ht.congr'
  filter_upwards [cubicThetaPositiveZeroObservable_continued W hε hW
    (s:=(4/3:ℂ)) (by norm_num)] with s hs
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveModelObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit nonconstant arithmetic model gives every positive-height
Fourier test of the actual residue, not only its high-cusp restriction. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveNormalized_nonzero_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaNormalizedObservedCoefficient h*
        cubicThetaFullPoleWeightIntegral h W := by
  have hJ : ((9*Real.sqrt 3/2:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,inner_smul_right,
    cubicThetaPositiveResidue_fourier_observation hh W hε hW,
    cubicThetaPositivePoleRadialTest_weight hh W hε hW]
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
  field_simp

theorem cubicThetaPositiveModel_nonzero_observation {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v) := by
  rw [cubicThetaPositiveNormalized_nonzero_observation hh W hε hW,
    cubicThetaCoefficientScalar hh,cubicThetaFullPoleWeightIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaArithmeticModel_horizontal _ hv,ite_eq_right hh]
  ring

theorem cubicThetaPositiveNormalized_zero_observation
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 0 W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)*
        mellin (star W) (-(4/3:ℂ)) := by
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,inner_smul_right,
    cubicThetaPositiveResidue_zero_observation W hε hW]
  calc
    _ = (cubicThetaResidueScale*((3*Real.pi:ℂ)*cubicThetaScatteringResidue))*
        mellin (star W) (-(4/3:ℂ)) := by ring
    _ = _ := by rw [cubicThetaResidueScale_constant]

theorem cubicThetaPositiveModel_zero_observation
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 0 W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency 0)):ℂ)*
            cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v) := by
  have hm : mellin (star W) (-(4/3:ℂ))=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*(v:ℂ)^(2/3:ℂ) := by
    rw [show -(4/3:ℂ)=(2/3:ℂ)-2 by ring,
      ←cubicThetaPositiveWindow_power W hε hW (2/3:ℂ)]
    simpa only [div_mul_eq_mul_div] using
      cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW
        (fun v => (v:ℂ)^(2/3:ℂ))
  rw [cubicThetaPositiveNormalized_zero_observation W hε hW,hm,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaArithmeticModel_horizontal _ hv]
  simp only [ite_true, if_true,Complex.ofReal_mul]
  have hc : ((v^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      Complex.ofReal_cpow hv.le (2/3:ℝ)
  rw [hc]
  ring

theorem cubicThetaPositiveModel_all_observations
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v) := by
  by_cases hh : h=0
  · subst h
    exact cubicThetaPositiveModel_zero_observation W hε hW
  · exact cubicThetaPositiveModel_nonzero_observation hh W hε hW

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Fourier pairing on the actual positive strip, and its
compatibility with the global energy restriction. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

theorem cubicThetaPositiveModelStrip_observations {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W)
      (cubicThetaPositiveCuspRestriction hε cubicThetaNormalizedArithmeticResidue)=
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W)
      (cubicThetaPositiveModelStrip cubicThetaArithmeticBaseScalar hε) := by
  rw [←cubicThetaPositiveRestriction_pairing hε h W hW hsm,
    cubicThetaPositiveModel_all_observations h W hε hW,
    cubicThetaPositiveModelStrip,cubicThetaPositiveStrip_inner_formula hε]
  exact (cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveModelIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized residue equals the explicit arithmetic model
on every positive-height strip. The remaining normalization scalar is retained. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveModelIdentity {ε : ℝ} (hε : 0<ε) :
    cubicThetaPositiveCuspRestriction hε cubicThetaNormalizedArithmeticResidue=
      cubicThetaPositiveModelStrip cubicThetaArithmeticBaseScalar hε := by
  apply sub_eq_zero.mp
  apply cubicThetaPositiveStripFourier_separates hε
  intro h W hW hsm
  rw [inner_sub_right,cubicThetaPositiveModelStrip_observations hε h W hW hsm,sub_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed positive-strip restriction is the actual measurable
lift from the quotient, including its cubic automorphy factor. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

theorem cubicThetaResidue_borel_model {ε : ℝ} (hε : 0<ε) :
    cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
      =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
  have he := cubicThetaPositiveModelIdentity hε
  rw [cubicThetaPositiveCuspRestriction_borel] at he
  filter_upwards [cubicThetaBorelRestriction_coe hε
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue),
    (cubicThetaArithmeticModel_positive_memLp cubicThetaArithmeticBaseScalar hε).coeFn_toLp] with p hB hM
  rw [←hB,he]
  exact hM

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
theorem cubicThetaArithmeticModel_global_ae :
    cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
      =ᵐ[cubicThetaPointMeasure]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
  have hslice (n : ℕ) : ∀ᵐ p ∂cubicThetaPointMeasure,
      p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
      cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue) p=
        cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val :=
    (ae_restrict_iff' (cubicThetaCuspStrip_measurable _)).mp
      (cubicThetaResidue_borel_model (by positivity : (0:ℝ)<1/(n+1:ℝ)))
  have hall : ∀ᵐ p ∂cubicThetaPointMeasure,∀ w : Eisenstein,∀ n : ℕ,
      cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
      cubicThetaBorelLift (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
          (cubicThetaPrincipalTranslation w • p)=
        cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
          (cubicThetaPrincipalTranslation w • p).val :=
    ae_all_iff.mpr (fun w => ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (cubicThetaPrincipalTranslation w) cubicThetaPointMeasure).quasiMeasurePreserving.ae (hslice n)))
  filter_upwards [hall] with p hp
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt p.property
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hn
  have he := hp w n hw
  rw [cubicThetaBorelLift_automorphy,cubicThetaPrincipalTranslation_value,one_mul] at he
  exact he.trans (cubicThetaArithmeticModel_translation cubicThetaArithmeticBaseScalar w p)

theorem cubicThetaArithmeticModel_automorphy (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (g • p).val=
      cubicThetaKubotaValue g*cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val := by
  have hg := (measurePreserving_smul g cubicThetaPointMeasure).quasiMeasurePreserving.ae
    cubicThetaArithmeticModel_global_ae
  have he : (fun p : CubicThetaPoint =>
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (g • p).val)
      =ᵐ[cubicThetaPointMeasure]
      (fun p => cubicThetaKubotaValue g*cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae,hg] with p hp hgp
    rw [←hgp,cubicThetaBorelLift_automorphy,hp]
  have hc := cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar
  exact congrFun (Measure.eq_of_ae_eq he (hc.comp (continuous_const_smul g)) (continuous_const.mul hc)) p

def cubicThetaArithmeticModelSection : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val,
    cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar⟩,
    cubicThetaArithmeticModel_automorphy⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual automorphic function by its nonzero Fourier
coefficient. Its constant coefficient is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNormalizedSeriesSection : CubicThetaSection :=
  cubicThetaArithmeticBaseScalar⁻¹ • cubicThetaArithmeticModelSection

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExtendedAutomorphy
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reconstructed arithmetic theta section has the actual Gamma_2
multiplier. Its integer invariance follows from S,T generation. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaNormalizedStabilizer : Subgroup SL(2,Eisenstein) where
  carrier := {g | ∀ p : CubicThetaPoint,
    cubicThetaNormalizedSeriesSection.val (g • p)=cubicThetaNormalizedSeriesSection.val p}
  one_mem' := by intro p; rw [one_smul]
  mul_mem' := by intro g h hg hh p; rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg p
    have he := hg (g⁻¹ • p)
    rw [smul_inv_smul] at he
    exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary projector and its finite transformed cusp family. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaNormalizedPrimaryProjection (p : CubicThetaPoint) : ℂ :=
  (star (cubicThetaNormalizedSeriesSection.val p)+
    omega*star (cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation omegaE • p))+
    omega^2*star (cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation (2*omegaE) • p)))/3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaModelGlobalL2
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous arithmetic model is the actual global L2 residue,
not only its restriction to a cusp. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticModelRepresentative_ae :
    cubicThetaSectionRepresentative cubicThetaArithmeticModelSection
      =ᵐ[cubicThetaQuotientMeasure]
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue :
          CubicThetaQuotient → ℂ) := by
  let R := cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue
  have hp : ∀ᵐ p ∂cubicThetaPointMeasure,
      cubicThetaSectionRepresentative cubicThetaArithmeticModelSection (cubicThetaQuotientMap p)=
        R (cubicThetaQuotientMap p) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae] with p hp
    have he := cubicThetaBorelLift_section cubicThetaArithmeticModelSection p
    have hh : cubicThetaBorelPhase p*
        cubicThetaSectionRepresentative cubicThetaArithmeticModelSection (cubicThetaQuotientMap p)=
        cubicThetaBorelPhase p*R (cubicThetaQuotientMap p) := he.trans hp.symm
    exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [cubicThetaBorelPhase_norm]; norm_num)) hh
  change ∀ᵐ q ∂cubicThetaQuotientMeasure,
    cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q=R q
  change ∀ᵐ q ∂(cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain).map
    cubicThetaQuotientMap, cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q=R q
  apply (ae_map_iff cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (measurableSet_eq_fun (cubicThetaSectionRepresentative_measurable _)
      (Lp.stronglyMeasurable R).measurable)).mpr
  exact ae_mono Measure.restrict_le_self hp

lemma cubicThetaArithmeticModelGlobal_memLp :
    MemLp (cubicThetaSectionRepresentative cubicThetaArithmeticModelSection)
      2 cubicThetaQuotientMeasure :=
  (memLp_congr_ae cubicThetaArithmeticModelRepresentative_ae).mpr
    (Lp.memLp (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaModelRankinLimit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Rankin pole paired with the actual global cubic theta section. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
namespace CubicFirstMoment

def cubicThetaArithmeticRankinMass (σ : ℝ) : ℂ :=
  ∫ q,(cubicThetaScalarRankinKernel σ q:ℂ)*
    cubicThetaSectionPairing cubicThetaArithmeticModelSection
      cubicThetaArithmeticModelSection q ∂cubicThetaQuotientMeasure

end CubicFirstMoment

end

end OAI
end


