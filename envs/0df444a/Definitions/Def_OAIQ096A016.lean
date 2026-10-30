-- Prove2me | Definitions.Def_OAIQ096A016
-- name    : OAIQ096A016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:50:38.220335+00:00
-- url     : https://prove2.me/theorems/968b910a-9ee0-4e81-b243-d7fc4e82ef46
-- title:
--   Definitions bundle OAIQ096A016 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 179 declarations of OpenAI's Lean: 48 definitions and 131 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain`, `OAI.CubicFirstMoment.cubicThetaActualCuspConstant`, `OAI.CubicFirstMoment.cubicThetaActualRawRadialMain`, `OAI.CubicFirstMoment.cubicThetaAngularCompletion`, `OAI.CubicFirstMoment.cubicThetaAnnularL2`, `OAI.CubicFirstMoment.cubicThetaAnnularL2Linear`, `OAI.CubicFirstMoment.cubicThetaArithmeticBaseScalar`, `OAI.CubicFirstMoment.cubicThetaArithmeticCoordinateEnergy`, `OAI.CubicFirstMoment.cubicThetaArithmeticDistribution`, `OAI.CubicFirstMoment.cubicThetaArithmeticFourierResidue`, `OAI.CubicFirstMoment.cubicThetaCompactEnergyCorrection`, `OAI.CubicFirstMoment.cubicThetaComplexLocalInclusion`, `OAI.CubicFirstMoment.cubicThetaCoreLocalInclusion`, `OAI.CubicFirstMoment.cubicThetaCoreMass`, `OAI.CubicFirstMoment.cubicThetaCoreMassFamily`, `OAI.CubicFirstMoment.cubicThetaCoreMultiplier`, `OAI.CubicFirstMoment.cubicThetaCorePointSupport`, `OAI.CubicFirstMoment.cubicThetaCoreRestriction`, `OAI.CubicFirstMoment.cubicThetaCuspCoordinateEnergy`, `OAI.CubicFirstMoment.cubicThetaCuspCutoffSection`, `OAI.CubicFirstMoment.cubicThetaCuspRestriction`, `OAI.CubicFirstMoment.cubicThetaFiniteEnergyEmbedding`, `OAI.CubicFirstMoment.cubicThetaForcedResolvent`, `OAI.CubicFirstMoment.cubicThetaGlobalEnergyGradient`, `OAI.CubicFirstMoment.cubicThetaGlobalEnergyTest`, `OAI.CubicFirstMoment.cubicThetaGlobalEnergyTestLinear`, `OAI.CubicFirstMoment.cubicThetaGlobalGreen`, `OAI.CubicFirstMoment.cubicThetaGlobalLocalInclusion`, `OAI.CubicFirstMoment.cubicThetaGlobalResolvent`, `OAI.CubicFirstMoment.cubicThetaGlobalSpectralResolvent`, `OAI.CubicFirstMoment.cubicThetaGlobalToLocalEnergy`, `OAI.CubicFirstMoment.cubicThetaIntrinsicCoordinateEnergy`, `OAI.CubicFirstMoment.cubicThetaLocalEnergyResolvent`, `OAI.CubicFirstMoment.cubicThetaNormalizedObservedCoefficient`, `OAI.CubicFirstMoment.cubicThetaObservedWhittakerCoefficient`, `OAI.CubicFirstMoment.cubicThetaProjectedConstant`, `OAI.CubicFirstMoment.cubicThetaProjectedRadialAxis`, `OAI.CubicFirstMoment.cubicThetaProjectedRadialConstant`, `OAI.CubicFirstMoment.cubicThetaResidueRadialPole`, `OAI.CubicFirstMoment.cubicThetaResidueScale` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_LatticePoisson`, `CubicMoment_Estimates_PrincipalIdealTheta`, `CubicMoment_Estimates_PrincipalLatticeTheta`, `CubicMoment_Estimates_PrincipalZetaContinuation`, `CubicMoment_Theta_CubicThetaActualCuspCoefficients`, `CubicMoment_Theta_CubicThetaAngularFunctionalEquation`, `CubicMoment_Theta_CubicThetaAnnularL2`, `CubicMoment_Theta_CubicThetaArithmeticCuspEnergy`, `CubicMoment_Theta_CubicThetaArithmeticDistribution`, `CubicMoment_Theta_CubicThetaArithmeticEnergy`, `CubicMoment_Theta_CubicThetaArithmeticGradientMass`, `CubicMoment_Theta_CubicThetaAutomorphicSections`, `CubicMoment_Theta_CubicThetaC1Cutoff`, `CubicMoment_Theta_CubicThetaChartEnergyDomination`, `CubicMoment_Theta_CubicThetaCoefficientScalar`, `CubicMoment_Theta_CubicThetaCompactCuspCutoff`, `CubicMoment_Theta_CubicThetaCompactCuspEnergy`, `CubicMoment_Theta_CubicThetaCompactEnergyCorrection`, `CubicMoment_Theta_CubicThetaComplexLocalization`, `CubicMoment_Theta_CubicThetaCoreBumpIntegral`, `CubicMoment_Theta_CubicThetaCoreLocalRellich`, `CubicMoment_Theta_CubicThetaCoreMassCompact`, `CubicMoment_Theta_CubicThetaCoreMassFamily`, `CubicMoment_Theta_CubicThetaCoreRestriction`, `CubicMoment_Theta_CubicThetaCuspCoordinateEnergy`, `CubicMoment_Theta_CubicThetaCuspCutoffEnergy`, `CubicMoment_Theta_CubicThetaCuspCutoffMeasurable`, `CubicMoment_Theta_CubicThetaCuspDerivativeIntegral`, `CubicMoment_Theta_CubicThetaCuspDisjointness`, `CubicMoment_Theta_CubicThetaCuspExhaustion`, `CubicMoment_Theta_CubicThetaCuspExhaustionBounds`, `CubicMoment_Theta_CubicThetaCuspLogSection`, `CubicMoment_Theta_CubicThetaCuspRestriction`, `CubicMoment_Theta_CubicThetaCuspVerticalEnergy`, `CubicMoment_Theta_CubicThetaEnergyIntegralIdentities`, `CubicMoment_Theta_CubicThetaEnergyInverseContinuation`, `CubicMoment_Theta_CubicThetaEnergyRegularDomain`, `CubicMoment_Theta_CubicThetaExceptionalAlgebra`, `CubicMoment_Theta_CubicThetaFiniteCusps`, `CubicMoment_Theta_CubicThetaFiniteEnergyClosure`, `CubicMoment_Theta_CubicThetaFiniteEnergySections`, `CubicMoment_Theta_CubicThetaForcedResolvent`, `CubicMoment_Theta_CubicThetaForcingL2`, `CubicMoment_Theta_CubicThetaFrequencyResidue`, `CubicMoment_Theta_CubicThetaGlobalEnergy`, `CubicMoment_Theta_CubicThetaGlobalGreen`, `CubicMoment_Theta_CubicThetaGlobalLocalRellich`, `CubicMoment_Theta_CubicThetaGlobalLocalizationBound`, `CubicMoment_Theta_CubicThetaGlobalSpectralResolvent`, `CubicMoment_Theta_CubicThetaHorizontalCompact`, `CubicMoment_Theta_CubicThetaLocalEnergyResolvent`, `CubicMoment_Theta_CubicThetaNormalizedSeries`, `CubicMoment_Theta_CubicThetaObservationScaling`, `CubicMoment_Theta_CubicThetaProjectedCoefficient`, `CubicMoment_Theta_CubicThetaProjectedRadial`, `CubicMoment_Theta_CubicThetaRadialAverage`, `CubicMoment_Theta_CubicThetaRadialRawVoronoi`, `CubicMoment_Theta_CubicThetaRadialRegularization`, `CubicMoment_Theta_CubicThetaResidueNormalization`, `CubicMoment_Theta_CubicThetaScalarCuspQuotient`, `CubicMoment_Theta_CubicThetaScalarCuspSupport`, `CubicMoment_Theta_CubicThetaScalarCuspVanishing`, `CubicMoment_Theta_CubicThetaSectionCutoffEnergy`, `CubicMoment_Theta_CubicThetaThetaObservation`, `CubicMoment_Theta_CubicThetaTranslatedCuspStrip`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A011` and `OAIQ096A012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A021`, `OAIQ096A022`, `OAIQ096A023` and `OAIQ096A027`; the statements `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq`, `OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi`, `OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit` and `OAI_CubicFirstMoment_cubicThetaScalarRankinKernel_residue`; the proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_centered_short_low_power`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_radial_model_low_power`, `OAI.CubicFirstMoment.ProfileControl.low_poisson_dyadic_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power`, `OAI_CubicFirstMoment_ProfileControl_smallB_radial_form_height_power`, `OAI_CubicFirstMoment_UniformLogWeights_cubeModelTerm_mass_error`, `OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving`, `OAI_CubicFirstMoment_angular_cube_poisson_log_saving`, `OAI_CubicFirstMoment_angular_divisor_noncube_annulus_saving`, `OAI.CubicFirstMoment.angular_divisor_noncube_total_saving`, `OAI.CubicFirstMoment.angular_full_prime_centered_product_bilinear_actual`, `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving`, `OAI_CubicFirstMoment_angular_height_poisson_total_saving`, `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual`, `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual`, `OAI_CubicFirstMoment_angular_noncube_poisson_dyadic_saving`, `OAI.CubicFirstMoment.angular_noncube_poisson_total_saving`, `OAI_CubicFirstMoment_angular_noncube_signed_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_primeProductLowHeight_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedEarly_isLittleO_actual`, `OAI.CubicFirstMoment.angular_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_angular_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_angular_stopped_divisor_noncube_dyadic`, `OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total`, `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form`, `OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual`, `OAI_CubicFirstMoment_angular_stopped_reflected_arithmetic_mellin_integral`, `OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual`, `OAI_CubicFirstMoment_angular_typeI_low_proved`, `OAI.CubicFirstMoment.bounded_poisson_dyadic`, `OAI.CubicFirstMoment.centralRoughProduct_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.coprime_noncube_mellin_integral_saving`, `OAI_CubicFirstMoment_cube_poisson_log_saving`, `OAI.CubicFirstMoment.cubicTheta_radial_scaleFirstOrdinaryNoStopTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_radial_upperNoStopTail_isLittleO`, `OAI_CubicFirstMoment_divisor_high_poisson_log_saving`, `OAI.CubicFirstMoment.divisor_noncube_total_saving`, `OAI.CubicFirstMoment.full_prime_centered_product_bilinear_actual`, `OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay`, `OAI_CubicFirstMoment_height_poisson_total_saving`, `OAI.CubicFirstMoment.height_radial_form_saving`, `OAI_CubicFirstMoment_huxleyAdditiveLargeSieve_proved`, `OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.noncube_poisson_total_saving`, `OAI_CubicFirstMoment_noncube_signed_mellin_integral_saving`, `OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual`, `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.primeProductLowHeight_angular_isLittleO_actual`, `OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual`, `OAI.CubicFirstMoment.primeProductLowHeight_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.semiprime_block_log_saving_actual`, `OAI.CubicFirstMoment.short_outer_low_bound_actual`, `OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual`, `OAI_CubicFirstMoment_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_stopped_divisor_noncube_dyadic`, `OAI.CubicFirstMoment.stopped_divisor_noncube_total`, `OAI.CubicFirstMoment.stopped_noncube_radial_form`, `OAI_CubicFirstMoment_stopped_norm_mellin_integral` and `OAI.CubicFirstMoment.stopped_typeI_mixed_actual`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A012

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma integral_complexMul (q : ℂ) (hq : q ≠ 0) (f : ℂ → ℂ) :
    ∫ z : ℂ, f (q * z) = (Complex.normSq q)⁻¹ • ∫ z : ℂ, f z := by
  have h := integral_map_equiv (μ := volume)
    (complexMulEquiv q hq).toHomeomorph.toMeasurableEquiv f
  change (∫ z : ℂ, f z ∂Measure.map (fun z => q * z) volume) =
    ∫ z : ℂ, f (q * z) at h
  rw [complexMul_map_volume q hq, integral_smul_measure] at h
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Complex.normSq_nonneg q),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Complex.normSq_nonneg q))] using h.symm

lemma traceFourier_complexMul (q : ℂ) (hq : q ≠ 0) (f : ℂ → ℂ) (w : ℂ) :
    traceFourier (fun z => f (q * z)) w =
      (Complex.normSq q)⁻¹ • traceFourier f (w / q) := by
  unfold traceFourier
  convert integral_complexMul q hq
    (fun z => (Real.fourierChar (-tracePair z (w / q)) : ℂ) * f z) using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards with z
  congr 2
  unfold tracePair
  congr 2
  field_simp

theorem poisson_eisenstein_coset (f : 𝓢(ℂ, ℂ)) (q : ℂ) (hq : q ≠ 0) (z : ℂ) :
    ∑' a : Eisenstein, f (z + q * (a : ℂ)) =
      (2 / (Real.sqrt 3 * Complex.normSq q) : ℝ) • ∑' h : Eisenstein,
        (Real.fourierChar (tracePair z ((h : ℂ) / (q * traceLambda))) : ℂ) *
          traceFourier f ((h : ℂ) / (q * traceLambda)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (complexMulEquiv q hq) f
  have hg : (g : ℂ → ℂ) = (fun x => f (q * x)) := rfl
  have he := poisson_eisenstein_translate g (z / q)
  rw [hg] at he
  simp_rw [mul_add, mul_div_cancel₀ z hq, traceFourier_complexMul q hq] at he
  have hfreq (h : Eisenstein) : ((h : ℂ) / traceLambda) / q =
      (h : ℂ) / (q * traceLambda) := by ring
  have hphase (h : Eisenstein) : tracePair (z / q) ((h : ℂ) / traceLambda) =
      tracePair z ((h : ℂ) / (q * traceLambda)) := by
    unfold tracePair
    congr 2
    ring
  simp_rw [hfreq, hphase, mul_smul_comm] at he
  rw [tsum_const_smul'', smul_smul] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalLatticeTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson inversion of the principal lattice Gaussian, with its zero
term retained. This supplies the pole term of the principal ideal zeta
function rather than treating it as a nonprincipal Hecke function. -/
noncomputable section
namespace CubicFirstMoment

lemma principalLatticeTheta_inversion {t : ℝ} (ht : 0 < t) :
    principalLatticeTheta t=(1/t:ℝ)*principalLatticeTheta (1/t) := by
  have hA := residueHeckeScale_pos (q := 1) one_ne_zero
  let F := radialGaussianSchwartz (t/residueHeckeScale 1) (div_pos ht hA)
  have hp := poisson_eisenstein_coset F (1:ℂ) one_ne_zero 0
  have he (a : Eisenstein) : F (a:ℂ)=
      (Real.exp (-norm a*t/residueHeckeScale 1):ℂ) := by
    dsimp only [F]
    rw [radialGaussianSchwartz_apply]
    change (Real.exp (-(t/residueHeckeScale 1)*‖(a:ℂ)‖^2):ℂ)=
      (Real.exp (-Complex.normSq (a:ℂ)*t/residueHeckeScale 1):ℂ)
    rw [Complex.normSq_eq_norm_sq]
    congr 2
    ring
  have hf := residueGaussian_prefactor (q := 1) one_ne_zero ht
  norm_num only [norm,Eisenstein.coe_one,Complex.normSq_one,Real.sqrt_one,one_mul,mul_one] at hf
  have hx (a : Eisenstein) := residueGaussian_exponent (q := 1) one_ne_zero ht a
  simp only [Eisenstein.coe_one,one_mul] at hx
  simp only [one_mul,zero_add,Complex.normSq_one,mul_one,tracePair,zero_mul,
    Complex.zero_re,mul_zero,AddChar.map_zero_eq_one,Circle.coe_one,he] at hp
  dsimp only [F] at hp
  simp_rw [radialGaussianSchwartz_traceFourier,hx] at hp
  rw [tsum_mul_left,Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,hf] at hp
  calc
    principalLatticeTheta t=(1/t:ℝ)*
        ∑' a : Eisenstein, (Real.exp (-norm a/(residueHeckeScale 1*t)):ℂ) := hp
    _ = _ := by
      congr 1
      apply tsum_congr
      intro a
      congr 2
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalIdealTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The principal theta function includes the zero vector. Its exact
unit multiplicity gives the inhomogeneous transformation of the ideal
theta sum and therefore the principal zeta pole. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem principalIdealTheta_inversion {t : ℝ} (ht : 0 < t) :
    idealTheta (residueHeckeScale 1) (fun _ => 1) (1/t)=
      (t:ℂ)*idealTheta (residueHeckeScale 1) (fun _ => 1) t+
        ((t:ℂ)-1)/(Nat.card (Eisensteinˣ):ℂ) := by
  have h := principalLatticeTheta_inversion (one_div_pos.mpr ht)
  rw [one_div_one_div,principalLatticeTheta_eq_ideal (one_div_pos.mpr ht),
    principalLatticeTheta_eq_ideal ht] at h
  have hU := residueTheta_unit_multiplicity_ne_zero
  field_simp
  linear_combination h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def principalIdealFEPair : WeakFEPair ℂ where
  f t := principalThetaConstant+idealTheta (residueHeckeScale 1) (fun _ => 1) t
  g t := principalThetaConstant+idealTheta (residueHeckeScale 1) (fun _ => 1) t
  k := 1
  ε := 1
  f₀ := principalThetaConstant
  g₀ := principalThetaConstant
  hf_int := (continuousOn_const.add (idealTheta_continuousOn
    (residueHeckeScale_pos (q := 1) one_ne_zero) _ (by simp))).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_const.add (idealTheta_continuousOn
    (residueHeckeScale_pos (q := 1) one_ne_zero) _ (by simp))).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := one_ne_zero
  hf_top r := by
    simpa only [add_sub_cancel_left] using idealTheta_isBigO_rpow
      (residueHeckeScale_pos (q := 1) one_ne_zero) (fun _ => 1) (by simp) r
  hg_top r := by
    simpa only [add_sub_cancel_left] using idealTheta_isBigO_rpow
      (residueHeckeScale_pos (q := 1) one_ne_zero) (fun _ => 1) (by simp) r
  h_feq t ht := by
    simp only [Real.rpow_one,one_mul,smul_eq_mul]
    rw [principalIdealTheta_inversion ht]
    unfold principalThetaConstant
    have hU := residueTheta_unit_multiplicity_ne_zero
    field_simp
    ring

def principalIdealZeta (s : ℂ) : ℂ :=
  thetaHeckeL (residueHeckeScale 1) principalIdealFEPair.Λ s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAutomorphicSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous sections with the actual cubic multiplier. Their norm
descends to the arithmetic quotient, and quotient cutoffs localize them. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSectionCutoff_norm (ψ : C(CubicThetaQuotient,ℂ)) (F : CubicThetaSection)
    (q : CubicThetaQuotient) :
    cubicThetaSectionNorm (cubicThetaSectionCutoff ψ F) q=‖ψ q‖*cubicThetaSectionNorm F q := by
  unfold cubicThetaSectionNorm
  change ‖ψ (cubicThetaQuotientMap (cubicThetaQuotientLift q))*F.val (cubicThetaQuotientLift q)‖=_
  rw [cubicThetaQuotientLift_map,norm_mul]

lemma cubicThetaSectionCutoff_compact (ψ : C(CubicThetaQuotient,ℂ)) (F : CubicThetaSection)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (cubicThetaSectionNorm (cubicThetaSectionCutoff ψ F)) := by
  have hnorm : HasCompactSupport (fun q => ‖ψ q‖) :=
    hψ.comp_left (g:=fun z : ℂ => ‖z‖) (by simp)
  have he : cubicThetaSectionNorm (cubicThetaSectionCutoff ψ F)=
      fun q => ‖ψ q‖*cubicThetaSectionNorm F q := funext (cubicThetaSectionCutoff_norm ψ F)
  rw [he]
  exact hnorm.mul_right

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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

def cubicThetaGlobalEnergyTest (F : cubicThetaSmoothTests) : cubicThetaGlobalEnergySpace :=
  ⟨cubicThetaGlobalEnergyGraph F,Submodule.le_topologicalClosure _ ⟨F,rfl⟩⟩

def cubicThetaGlobalEnergyGradient : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGradientL2 :=
  (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).comp
    cubicThetaGlobalEnergySpace.subtypeL

lemma cubicThetaGlobalInclusion_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)=cubicThetaGlobalMass F := rfl

lemma cubicThetaGlobalEnergyGradient_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)=cubicThetaGlobalGradient F := rfl

lemma cubicThetaGlobalInclusion_bound (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaGlobalInclusion u‖≤‖u‖ := WithLp.norm_fst_le CubicThetaGlobalL2 (u:CubicThetaGlobalEnergyAmbient)

lemma cubicThetaGlobalInclusion_norm : ‖cubicThetaGlobalInclusion‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using cubicThetaGlobalInclusion_bound u

lemma cubicThetaGlobalEnergy_norm_sq (u : cubicThetaGlobalEnergySpace) :
    ‖u‖^2=‖cubicThetaGlobalInclusion u‖^2+‖cubicThetaGlobalEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 (u:CubicThetaGlobalEnergyAmbient)

lemma cubicThetaGlobalEnergyTest_norm_sq (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyTest F‖^2=
      ∫ q, ‖cubicThetaSectionRepresentative F q‖^2+cubicThetaQuotientEnergy F q
        ∂cubicThetaQuotientMeasure := by
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalInclusion_test,
    cubicThetaGlobalEnergyGradient_test]
  have hM : Integrable (fun q => ‖cubicThetaSectionRepresentative F q‖^2)
      cubicThetaQuotientMeasure := (cubicThetaSectionRepresentative_memLp F).integrable_norm_pow (by norm_num)
  have hG : Integrable (fun q => ‖cubicThetaGradientRepresentative F q‖^2)
      cubicThetaQuotientMeasure := (cubicThetaGradientRepresentative_memLp F).integrable_norm_pow (by norm_num)
  have he : (fun q => ‖cubicThetaGradientRepresentative F q‖^2)=cubicThetaQuotientEnergy F := by
    funext q
    change ‖cubicThetaSectionGradient F (cubicThetaBorelSection q)‖^2=_
    rw [cubicThetaSectionGradient_norm_sq,← cubicThetaQuotientEnergy_apply,
      cubicThetaBorelSection_rightInverse]
  rw [cubicTheta_l2_norm_sq_measure,cubicTheta_l2_norm_sq_measure]
  have h₁ : (fun q => ‖(cubicThetaGlobalMass F) q‖^2) =ᵐ[cubicThetaQuotientMeasure]
      (fun q => ‖cubicThetaSectionRepresentative F q‖^2) := by
    filter_upwards [(cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hq
    change ‖((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
    rw [hq]
  have h₂ : (fun q => ‖(cubicThetaGlobalGradient F) q‖^2) =ᵐ[cubicThetaQuotientMeasure]
      (fun q => ‖cubicThetaGradientRepresentative F q‖^2) := by
    filter_upwards [(cubicThetaGradientRepresentative_memLp F).coeFn_toLp] with q hq
    change ‖((cubicThetaGradientRepresentative_memLp F).toLp _) q‖^2=_
    rw [hq]
  rw [integral_congr_ae h₁,integral_congr_ae h₂,← integral_add hM hG]
  apply integral_congr_ae
  filter_upwards with q
  rw [congrFun he q]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaChartEnergyDomination
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An injective chart cannot contribute more intrinsic energy than the
whole quotient. Only the proved local measure identity is used here. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaChart_measure_le
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap ≤ cubicThetaQuotientMeasure := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable)]
  rw [← cubicThetaQuotientMeasure_chart e he
    ((hB.preimage cubicThetaQuotientMap_open.continuous.measurable).inter hS)
    (fun _ hx => hSe hx.2)]
  apply measure_mono
  rintro q ⟨p,hp,rfl⟩
  exact hp.1

lemma cubicThetaChart_integral_le
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    (hn : ∀ q, 0≤f q) :
    (∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure)≤
      ∫ q, f q ∂cubicThetaQuotientMeasure := by
  have hm := cubicThetaChart_measure_le e he hS hSe
  rw [← integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hm)]
  exact integral_mono_measure hm (Filter.Eventually.of_forall hn) hf

lemma cubicThetaQuotientEnergy_nonneg (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) :
    0 ≤ cubicThetaQuotientEnergy F q :=
  mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)

lemma cubicThetaIntrinsicEnergy_integrable (F : cubicThetaSmoothTests) :
    Integrable (fun q => cubicThetaSectionNorm F q^2+cubicThetaQuotientEnergy F q)
      cubicThetaQuotientMeasure := by
  have hm : Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
    have h := (cubicThetaSectionRepresentative_memLp F).integrable_norm_pow (by norm_num)
    simpa only [cubicThetaSectionRepresentative_norm] using h
  have hd : Integrable (cubicThetaQuotientEnergy F) cubicThetaQuotientMeasure :=
    (cubicThetaQuotientEnergy_continuous F).integrable_of_hasCompactSupport
      (cubicThetaQuotientEnergy_compact F)
  exact hm.add hd

theorem cubicThetaChart_energy_le
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (F : cubicThetaSmoothTests) :
    (∫ p in S, cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
      cubicThetaSectionEnergy F p ∂cubicThetaPointMeasure)≤
        ‖cubicThetaGlobalEnergyTest F‖^2 := by
  rw [cubicThetaGlobalEnergyTest_norm_sq]
  simp only [cubicThetaSectionRepresentative_norm]
  have h := cubicThetaChart_integral_le e he hS hSe
    (cubicThetaIntrinsicEnergy_integrable F)
    (fun q => add_nonneg (sq_nonneg _) (cubicThetaQuotientEnergy_nonneg F q))
  simpa only [cubicThetaQuotientEnergy_apply] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspLogSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact smooth sections, pulled into a cusp and conjugated
by logarithmic height, are genuine compact radial test functions. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaCuspCutoffSection (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) (v : ℝ) : ℂ :=
  cubicThetaCuspCutoff v*cubicThetaSectionFunction F
    (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspVerticalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial derivative in a cusp is controlled by the actual
hyperbolic Dirichlet energy of the pulled-back cubic section. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspSection_deriv (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))) v=
      ((cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv)).comp
        (cubicThetaTangentDerivative (cubicThetaFullComplex δ) (z,v))) cubicThetaVerticalTangent := by
  have hm := (cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ) (p:=(z,v)) hv).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hp := cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (p:=(z,v)) hv
  have hf := cubicThetaSectionFunction_differentiable F hp
  have hline : HasDerivAt (fun t : ℝ => (z,t)) (0,1) v :=
    (hasDerivAt_const v z).prodMk (hasDerivAt_id v)
  have h := (hf.hasFDerivAt.comp_hasDerivAt v (hm.hasFDerivAt.comp_hasDerivAt v hline)).deriv
  have hpoint : (δ • cubicThetaVerticalPoint z v hv).val=
      cubicThetaMobius (cubicThetaFullComplex δ) (z,v) := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,cubicThetaVerticalTangent,
    ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,hpoint,Function.comp_def] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTranslatedCuspStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaTranslatedCuspStrip_measurable (δ : SL(2,Eisenstein)) (H : ℝ) :
    MeasurableSet (cubicThetaTranslatedCuspStrip δ H) :=
  (Homeomorph.smul δ).measurableEmbedding.measurableSet_image' (cubicThetaCuspStrip_measurable H)

lemma cubicThetaTranslatedCuspStrip_injective (δ : SL(2,Eisenstein))
    {H : ℝ} (hH : 1≤H) : InjOn cubicThetaQuotientMap (cubicThetaTranslatedCuspStrip δ H) := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ he
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change g.val • (δ • q)=δ • p at hg
  have hc : cubicThetaPrincipalConjugate δ g • q=p := by
    change (δ⁻¹*g.val*δ) • q=p
    rw [mul_smul,mul_smul,hg,inv_smul_smul]
  have hπ : cubicThetaQuotientMap p=cubicThetaQuotientMap q := by
    rw [← hc,cubicThetaQuotient_covering.map_smul]
  exact congrArg (fun r : CubicThetaPoint => δ • r) (cubicThetaCuspStrip_injective hH hp hq hπ)

lemma cubicThetaSmul_map_restrict (δ : SL(2,Eisenstein)) {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map (fun p : CubicThetaPoint => δ • p)=
      cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' S) := by
  have hImage := (Homeomorph.smul δ).measurableEmbedding.measurableSet_image' hS
  change MeasurableSet ((fun p : CubicThetaPoint => δ • p) '' S) at hImage
  have h := Measure.restrict_map (measurable_const_smul δ) hImage (μ:=cubicThetaPointMeasure)
  rw [(measurePreserving_smul δ cubicThetaPointMeasure).map_eq] at h
  have he : (fun p : CubicThetaPoint => δ • p) ⁻¹' ((fun p : CubicThetaPoint => δ • p) '' S)=S :=
    Set.preimage_image_eq _ (MulAction.injective δ)
  rw [he] at h
  exact h.symm

lemma cubicThetaTranslatedCuspStrip_integrable (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure) :
    IntegrableOn (fun p => f (cubicThetaQuotientMap (δ • p))) (cubicThetaCuspStrip H)
      cubicThetaPointMeasure := by
  have h := hf.integrableOn (s:=cubicThetaQuotientMap '' cubicThetaTranslatedCuspStrip δ H)
  unfold IntegrableOn at h
  rw [← cubicThetaInjective_map_restrict (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH)] at h
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  change Integrable (fun p => f (cubicThetaQuotientMap p))
    (cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H)) at hi
  rw [← cubicThetaSmul_map_restrict δ (cubicThetaCuspStrip_measurable H)] at hi
  simpa only [IntegrableOn,Function.comp_def] using
    hi.comp_measurable (measurable_const_smul δ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCoordinateEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The true scalar mass and energy in each cusp, in the Euclidean
coordinates used for the radial integration. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaCuspCoordinateEnergy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (y : ℂ × ℝ) : ℝ :=
  cubicThetaSectionNorm F
      (cubicThetaQuotientMap (δ • cubicThetaPointInclusion.symm y))^2+
    cubicThetaSectionEnergy F (δ • cubicThetaPointInclusion.symm y)

lemma cubicThetaCuspCoordinateEnergy_apply (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (p : CubicThetaPoint) :
    cubicThetaCuspCoordinateEnergy δ F (cubicThetaPointCoordinates p)=
      cubicThetaSectionNorm F (cubicThetaQuotientMap (δ • p))^2+
        cubicThetaSectionEnergy F (δ • p) := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaCuspCoordinateEnergy,h]

lemma cubicThetaCuspCoordinateEnergy_integrable (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) {H : ℝ} (hH : 1≤H) :
    IntegrableOn (fun y => cubicThetaCuspCoordinateEnergy δ F y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi H) := by
  have h := cubicThetaTranslatedCuspStrip_integrable δ hH (cubicThetaIntrinsicEnergy_integrable F)
  simp only [cubicThetaQuotientEnergy_apply] at h
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable H)]
  simpa only [cubicThetaCuspCoordinateEnergy_apply] using h

lemma cubicThetaCusp_raw_norm (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖=
      cubicThetaSectionNorm F (cubicThetaQuotientMap (δ • cubicThetaVerticalPoint z v hv)) := by
  have h := cubicThetaSectionNorm_apply F (δ • cubicThetaVerticalPoint z v hv)
  rw [cubicThetaSectionFunction_apply F (cubicThetaMobius_height_pos
    (cubicThetaFullComplex δ) (p:=(z,v)) hv)]
  exact h.symm

lemma cubicThetaCuspCoordinateEnergy_norm (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaCuspCoordinateEnergy δ F (z,v)=
      ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2+
        cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
  have h := cubicThetaCuspCoordinateEnergy_apply δ F (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspCoordinateEnergy δ F (z,v)=_ at h
  rw [cubicThetaCusp_raw_norm δ F z hv]
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! With any prescribed loss above the sharp coefficient one, cutting
off a cusp costs only mass in its fixed compact transition annulus. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspRaw_differentiableAt (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    DifferentiableAt ℝ (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))) v := by
  have hm := (cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ) (p:=(z,v)) hv).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hp := cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (p:=(z,v)) hv
  have hf := cubicThetaSectionFunction_differentiable F hp
  have hline : DifferentiableAt ℝ (fun t : ℝ => (z,t)) v :=
    ((hasDerivAt_const v z).prodMk (hasDerivAt_id v)).differentiableAt
  exact DifferentiableAt.comp (g:=cubicThetaSectionFunction F)
    (f:=fun t : ℝ => cubicThetaMobius (cubicThetaFullComplex δ) (z,t)) v hf (hm.comp v hline)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCutoffMeasurable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability of the true radial cusp derivative, needed to
integrate the sectionwise Hardy inequalities by Fubini. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspCutoffSection_continuous (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    Continuous (Function.uncurry (cubicThetaCuspCutoffSection δ F)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  change ContinuousAt (fun y : ℂ × ℝ => cubicThetaCuspCutoff y.2*
    cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) y)) y
  by_cases hy : 0<y.2
  · have hpos := cubicThetaMobius_height_pos (cubicThetaFullComplex δ) hy
    have hf : ContinuousAt (cubicThetaSectionFunction F)
        (cubicThetaMobius (cubicThetaFullComplex δ) y) :=
      (F.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)).continuousAt
    have hm := cubicThetaMobius_continuousAt (cubicThetaFullComplex δ) hy
    have hs := ContinuousAt.comp (f:=cubicThetaMobius (cubicThetaFullComplex δ))
      (g:=cubicThetaSectionFunction F) (x:=y) hf hm
    exact (cubicThetaCuspCutoff_smooth.continuous.continuousAt.comp continuous_snd.continuousAt).mul hs
  · have hlt : y.2<1 := lt_of_le_of_lt (le_of_not_gt hy) zero_lt_one
    have hnear : ∀ᶠ x : ℂ × ℝ in 𝓝 y, x.2<1 :=
      continuous_snd.continuousAt.eventually (eventually_lt_nhds hlt)
    have he : (fun y : ℂ × ℝ => cubicThetaCuspCutoff y.2*
        cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) y))=ᶠ[𝓝 y]
        (fun _ => (0:ℂ)) := by
      filter_upwards [hnear] with x hx
      rw [cubicThetaCuspCutoff_zero hx.le,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

lemma cubicThetaCuspCutoff_deriv_measurable (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    Measurable (fun y : ℂ × ℝ => deriv (cubicThetaCuspCutoffSection δ F y.1) y.2) :=
  measurable_deriv_with_param (cubicThetaCuspCutoffSection_continuous δ F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspDerivativeIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cutoff radial derivative is integrable on each exact
cusp cell. The majorant is the already proved global mass plus energy. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaHorizontalCell_measurable : MeasurableSet cubicThetaHorizontalCell := by
  have hm (i : Fin 2) : Measurable (fun z => cubicThetaPeriodCoordinates z i) :=
    ((continuous_apply i).comp cubicThetaPeriodCoordinates_continuous).measurable
  convert MeasurableSet.iInter (fun i =>
    (measurableSet_Ico : MeasurableSet (Ico (0:ℝ) 1)).preimage (hm i)) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [cubicThetaHorizontalCell,mem_iInter,mem_preimage,mem_ofPred_eq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCompact
attribute [-instance] _root_.instMeasurableSpace
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

lemma cubicThetaHorizontalCell_normSq_bound :
    ∃ R : ℝ, 0≤R ∧ ∀ z∈cubicThetaHorizontalCell, Complex.normSq z≤R := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn Complex.continuous_normSq.continuousOn
  refine ⟨max 0 R,le_max_left _ _,fun z hz => ?_⟩
  exact ((le_abs_self _).trans (hR z (hsub hz))).trans (le_max_right _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspDisjointness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaCuspNeighborhood_parabolic_eq (δ ε : SL(2,Eisenstein))
    (g : cubicThetaPrincipalGroup) (a : SL(2,Eisenstein)) (ha : a 1 0=0)
    (he : δ*a=g.val*ε) (H : ℝ) :
    cubicThetaCuspNeighborhood δ H=cubicThetaCuspNeighborhood ε H := by
  have hmap (p : CubicThetaPoint) :
      cubicThetaQuotientMap (δ • (a • p))=cubicThetaQuotientMap (ε • p) := by
    rw [← mul_smul,he,mul_smul]
    change cubicThetaQuotientMap (g • (ε • p))=cubicThetaQuotientMap (ε • p)
    exact cubicThetaQuotient_covering.map_smul g
  ext q
  rw [cubicThetaCuspNeighborhood_mem_iff,cubicThetaCuspNeighborhood_mem_iff]
  constructor
  · rintro ⟨p,hp,hpq⟩
    have hheight : cubicThetaPointHeight (a⁻¹ • p)=cubicThetaPointHeight p := by
      have h := cubicThetaPointHeight_upper a ha (a⁻¹ • p)
      simpa only [smul_inv_smul] using h.symm
    refine ⟨a⁻¹ • p,?_,?_⟩
    · rwa [hheight]
    · have h := hmap (a⁻¹ • p)
      rw [smul_inv_smul,hpq] at h
      exact h.symm
  · rintro ⟨p,hp,hpq⟩
    refine ⟨a • p,?_,(hmap p).trans hpq⟩
    rwa [cubicThetaPointHeight_upper a ha]

theorem cubicThetaCuspNeighborhood_overlap (δ ε : SL(2,Eisenstein))
    {H : ℝ} (hH : 1≤H)
    (hne : (cubicThetaCuspNeighborhood δ H ∩ cubicThetaCuspNeighborhood ε H).Nonempty) :
    ∀ T : ℝ, cubicThetaCuspNeighborhood δ T=cubicThetaCuspNeighborhood ε T := by
  obtain ⟨q,hδ,hε⟩ := hne
  obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ H q).mp hδ
  obtain ⟨r,hr,hrq⟩ := (cubicThetaCuspNeighborhood_mem_iff ε H q).mp hε
  have he : cubicThetaQuotientMap (δ • p)=cubicThetaQuotientMap (ε • r) := hpq.trans hrq.symm
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change g.val • (ε • r)=δ • p at hg
  let a := δ⁻¹*g.val*ε
  have har : a • r=p := by
    dsimp [a]
    rw [mul_smul,mul_smul,hg,inv_smul_smul]
  have hhigh : 1<(cubicThetaMobius (cubicThetaFullComplex a) r.val).2 := by
    change 1 < cubicThetaPointHeight (a • r)
    rw [har]
    exact lt_of_le_of_lt hH hp
  have ha : a 1 0=0 := cubicThetaMobius_high_overlap a (lt_of_le_of_lt hH hr) hhigh
  have hrel : δ*a=g.val*ε := by dsimp [a]; group
  exact cubicThetaCuspNeighborhood_parabolic_eq δ ε g a ha hrel

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic remainder has a continuous invariant
Dirichlet energy density. No energy membership is assumed here. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticSectionFunction_contDiffOn_one {s : ℂ} (hs : 2 < s.re) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs))
      {p : ℂ × ℝ | 0<p.2} := by
  apply (cubicThetaArithmeticRemainder_contDiffOn_one hs).congr
  intro p hp
  rw [cubicThetaSectionFunction_apply _ hp]
  rfl

lemma cubicThetaArithmeticDifferential_automorphy {s : ℂ} (hs : 2 < s.re)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) (g • p)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g) p.val)=
      cubicThetaKubotaValue g • cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) p := by
  let F := cubicThetaArithmeticSection s hs
  have hd {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaSectionFunction F) y :=
    ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).contDiffAt
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

lemma cubicThetaArithmeticEnergy_continuous {s : ℂ} (hs : 2 < s.re) :
    Continuous (cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs)) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) p.val) :=
    ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).continuousOn_fderiv_of_isOpen
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
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCuspEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of the arithmetic energy to a cusp, followed by
the operator-norm bound for its genuine joint derivative. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticCusp_energy_eq (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 2 < s.re)
    (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • p)=
      p.val.2^2*cubicThetaTangentEnergy
        ((fderiv ℝ (fun q => cubicThetaArithmeticRemainder
          (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p.val).comp
          cubicThetaTangentCoordinates.toContinuousLinearMap) := by
  let F := cubicThetaArithmeticSection s hs
  let g := cubicThetaFullComplex δ
  have hgp := cubicThetaMobius_height_pos g p.property
  have hF := ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hgp)).differentiableAt (by norm_num)
  have hg := (cubicThetaMobius_contDiffAt g p.property).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (fun q => cubicThetaSectionFunction F (cubicThetaMobius g q))=ᶠ[𝓝 p.val]
      (fun q => cubicThetaArithmeticRemainder (cubicThetaMobius g q) s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with q hq
    rw [cubicThetaSectionFunction_apply F (cubicThetaMobius_height_pos g hq)]
    rfl
  have hd := he.fderiv_eq (𝕜:=ℝ)
  have hcomp : fderiv ℝ (fun q => cubicThetaSectionFunction F (cubicThetaMobius g q)) p.val=
      (fderiv ℝ (cubicThetaSectionFunction F) (cubicThetaMobius g p.val)).comp
        (fderiv ℝ (cubicThetaMobius g) p.val) := by
    simpa only [Function.comp_def] using (fderiv_comp p.val hF hg)
  rw [hcomp] at hd
  have ht : (fderiv ℝ (fun q => cubicThetaArithmeticRemainder (cubicThetaMobius g q) s) p.val).comp
      cubicThetaTangentCoordinates.toContinuousLinearMap=
      (cubicThetaSectionDifferential F (δ • p)).comp (cubicThetaTangentDerivative g p.val) := by
    rw [← hd]
    apply ContinuousLinearMap.ext
    intro u
    simp only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,
      cubicThetaFullPointAction_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [ht,cubicThetaTangentEnergy_derivative _ _ p.property]
  change _=p.val.2^2*(((cubicThetaMobius g p.val).2/p.val.2)^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (δ • p)))
  unfold cubicThetaSectionEnergy
  rw [cubicThetaFullPointAction_apply]
  field_simp [p.property.ne']
  rfl

lemma cubicThetaArithmeticCusp_energy_le (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 2 < s.re)
    (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • p)≤
      (Module.finrank ℝ CubicThetaTangent:ℝ)*p.val.2^2*
        ‖fderiv ℝ (fun q => cubicThetaArithmeticRemainder
          (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p.val‖^2 := by
  rw [cubicThetaArithmeticCusp_energy_eq δ hs p]
  exact (mul_le_mul_of_nonneg_left (cubicThetaTangentEnergy_coordinate_bound _) (sq_nonneg _)).trans_eq
    (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1Cutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product bounds and local agreement for actual C1 section cutoffs. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaSectionCutoff_regular (ψ : C(CubicThetaQuotient,ℂ))
    (hψ : ContDiffOn ℝ 1 (fun y => ψ (cubicThetaQuotientMap
      (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F))
      {y : ℂ × ℝ | 0<y.2} := hψ.mul hF

lemma cubicThetaSectionCutoff_gradient_error (ψ : C(CubicThetaQuotient,ℂ))
    (hψ : ContDiffOn ℝ 1 (fun y => ψ (cubicThetaQuotientMap
      (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2})
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    ‖cubicThetaSectionGradient (cubicThetaSectionCutoff ψ F) p-cubicThetaSectionGradient F p‖^2≤
      2*‖ψ (cubicThetaQuotientMap p)-1‖^2*‖cubicThetaSectionGradient F p‖^2+
      2*‖F.val p‖^2*(p.val.2^2*cubicThetaFunctionEnergy (fun y =>
        ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p.val) := by
  let f := fun y => ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
  have hp : {y : ℂ × ℝ | 0<y.2}∈𝓝 p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hf : DifferentiableAt ℝ f p.val := (hψ.contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := (hF.contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := cubicThetaSectionCutoff_regular ψ hψ F hF
  rw [← cubicThetaC1Gradient_sub _ _ hc hF,cubicThetaSectionGradient_norm_sq]
  have he : cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F-F)=
      (fun y => f y-1)*cubicThetaSectionFunction F := by
    funext y
    change f y*cubicThetaSectionFunction F y-cubicThetaSectionFunction F y=_
    simp only [Pi.mul_apply]
    ring
  have hdf : fderiv ℝ (fun y => f y-1) p.val=fderiv ℝ f p.val := by
    rw [fderiv_fun_sub hf (differentiableAt_const _),fderiv_const_apply,sub_zero]
  have hE : cubicThetaFunctionEnergy (fun y => f y-1) p.val=cubicThetaFunctionEnergy f p.val := by
    unfold cubicThetaFunctionEnergy
    rw [hdf]
  have hm := mul_le_mul_of_nonneg_left
    (cubicThetaFunctionEnergy_mul (hf.sub_const 1) hg) (sq_nonneg p.val.2)
  change p.val.2^2*cubicThetaFunctionEnergy (cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F-F)) p.val≤_
  rw [he]
  rw [hE] at hm
  have hfv : f p.val=ψ (cubicThetaQuotientMap p) := by
    dsimp [f]
    have hl : cubicThetaPointInclusion.symm p.val=p :=
      cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
    exact congrArg (fun z => ψ (cubicThetaQuotientMap z)) hl
  have hgv : cubicThetaSectionFunction F p.val=F.val p :=
    cubicThetaSectionFunction_apply F p.property
  rw [hfv,hgv] at hm
  rw [cubicThetaSectionGradient_norm_sq]
  change _≤2*‖ψ (cubicThetaQuotientMap p)-1‖^2*
    (p.val.2^2*cubicThetaFunctionEnergy (cubicThetaSectionFunction F) p.val)+_
  nlinarith [hm]

lemma cubicThetaSectionCutoff_local_gradient (ψ : C(CubicThetaQuotient,ℂ))
    (F : CubicThetaSection) (p : CubicThetaPoint)
    (hψ : (ψ : CubicThetaQuotient → ℂ)=ᶠ[𝓝 (cubicThetaQuotientMap p)] (fun _ => 1)) :
    cubicThetaSectionGradient (cubicThetaSectionCutoff ψ F) p=cubicThetaSectionGradient F p := by
  have ht : p.val∈cubicThetaPointInclusion.target := by
    rw [cubicThetaPointInclusion_target]
    exact p.property
  have hm := cubicThetaQuotientMap_open.continuous.continuousAt.comp
    (cubicThetaPointInclusion.symm.continuousAt ht)
  have hleft : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  change ContinuousAt (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)) p.val at hm
  have hmt : Tendsto (fun y => cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
      (𝓝 p.val) (𝓝 (cubicThetaQuotientMap p)) := by
    simpa only [ContinuousAt,Function.comp_apply,hleft] using hm
  have he : cubicThetaSectionFunction (cubicThetaSectionCutoff ψ F)=ᶠ[𝓝 p.val]
      cubicThetaSectionFunction F := by
    filter_upwards [hψ.comp_tendsto hmt] with y hy
    change ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=1 at hy
    change ψ (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))*
      cubicThetaSectionFunction F y=cubicThetaSectionFunction F y
    rw [hy,one_mul]
  unfold cubicThetaSectionGradient cubicThetaSectionDifferential
  rw [he.fderiv_eq (𝕜:=ℝ)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaScalarCuspQuotient_norm (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N)
    (q : CubicThetaQuotient) : ‖cubicThetaScalarCuspQuotient δ N q‖≤1 :=
  cubicThetaScalarCusp_norm hN (δ⁻¹ • cubicThetaQuotientLift q).property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar cutoff is supported in its actual cusp and equals one
above twice its scale. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaScalarCuspQuotient_cusp (δ : SL(2,Eisenstein)) (N : ℝ) (p : CubicThetaPoint) :
    cubicThetaScalarCuspQuotient δ N (cubicThetaQuotientMap (δ • p))=cubicThetaScalarCusp N p.val := by
  rw [cubicThetaScalarCuspQuotient_apply]
  simp only [cubicThetaScalarCuspAt,inv_smul_smul]

lemma cubicThetaScalarCuspQuotient_support (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N)
    {q : CubicThetaQuotient} (hq : cubicThetaScalarCuspQuotient δ N q≠0) :
    q∈cubicThetaCuspNeighborhood δ N := by
  let x := cubicThetaQuotientLift q
  let y := δ⁻¹ • x
  have ht : ∃ r, cubicThetaScalarCuspTerm N r y.val≠0 := by
    by_contra! hz
    apply hq
    change (∑' r, cubicThetaScalarCuspTerm N r y.val)=0
    simp only [hz,tsum_zero]
  obtain ⟨r,hr⟩ := ht
  let g := r.completion
  let p := g • y
  have hh : N < r.height y.val := by
    by_contra hn
    exact hr (cubicThetaScalarCuspTerm_zero N (by linarith) r (le_of_not_gt hn))
  have hp : N < cubicThetaPointHeight p := by
    change N<(cubicThetaMobius (cubicThetaPrincipalComplex g) y.val).2
    rwa [← cubicThetaBottomRow_height,r.completion_row]
  have he : δ • p=cubicThetaPrincipalConjugate δ⁻¹ g • x := by
    change δ • (g.val • (δ⁻¹ • x))=((δ⁻¹)⁻¹*g.val*δ⁻¹) • x
    simp only [inv_inv,mul_smul]
  apply (cubicThetaCuspNeighborhood_mem_iff δ N q).mpr
  refine ⟨p,hp,?_⟩
  rw [he,cubicThetaQuotient_covering.map_smul]
  exact cubicThetaQuotientLift_map q

lemma cubicThetaScalarCuspQuotient_high (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N)
    {q : CubicThetaQuotient} (hq : q∈cubicThetaCuspNeighborhood δ (2*N)) :
    cubicThetaScalarCuspQuotient δ N q=1 := by
  obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ (2*N) q).mp hq
  rw [← hpq,cubicThetaScalarCuspQuotient_cusp]
  exact cubicThetaScalarCusp_high hN hp.le

lemma cubicThetaScalarCuspQuotient_coordinates (δ : SL(2,Eisenstein)) (N : ℝ)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaScalarCuspQuotient δ N (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=
      cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y) := by
  rw [cubicThetaScalarCuspQuotient_apply]
  unfold cubicThetaScalarCuspAt
  rw [cubicThetaFullPointAction_apply]
  congr 1
  exact congrArg (cubicThetaMobius (cubicThetaFullComplex δ⁻¹))
    (cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target]))

lemma cubicThetaScalarCuspQuotient_smooth (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaScalarCuspQuotient δ N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  have hM := cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ⁻¹) hy
  have hs := (cubicThetaScalarCusp_smooth hN).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (cubicThetaMobius_height_pos (cubicThetaFullComplex δ⁻¹) hy))
  have he : (fun y => cubicThetaScalarCuspQuotient δ N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)))=ᶠ[𝓝 y]
      (fun y => cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hy] with z hz
    exact cubicThetaScalarCuspQuotient_coordinates δ N hz
  exact ((hs.comp y hM).congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCusps
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cusp cover can be made disjoint without changing its union
at any height. Representatives are selected from the given arithmetic
charts, so all preceding analytic estimates continue to apply. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_one_nonempty (δ : SL(2,Eisenstein)) :
    (cubicThetaCuspNeighborhood δ 1).Nonempty := by
  let p : CubicThetaPoint := ⟨(0,2),by norm_num⟩
  refine ⟨cubicThetaQuotientMap (δ • p),cubicThetaCuspNeighborhood_mem_of_height δ p ?_⟩
  norm_num [p,cubicThetaPointHeight,cubicThetaPointCoordinates]

theorem cubicThetaFiniteCusps_disjoint (S : Finset SL(2,Eisenstein)) :
    ∃ T : Finset SL(2,Eisenstein), T⊆S ∧
      (∀ H : ℝ, (⋃ δ∈S, cubicThetaCuspNeighborhood δ H)=
        ⋃ δ∈T, cubicThetaCuspNeighborhood δ H) ∧
      ∀ H : ℝ, 1≤H → (T : Set SL(2,Eisenstein)).PairwiseDisjoint
        (fun δ => cubicThetaCuspNeighborhood δ H) := by
  classical
  let f : SL(2,Eisenstein) → Set CubicThetaQuotient := fun δ => cubicThetaCuspNeighborhood δ 1
  have hs : (S : Set SL(2,Eisenstein)).SurjOn f (S.image f) := by
    intro U hU
    exact Finset.mem_image.mp hU
  obtain ⟨T,hTS,hT,himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (S : Set SL(2,Eisenstein)) (S.image f) hs
  have hrep (δ : SL(2,Eisenstein)) (hδ : δ∈S) :
      ∃ ε∈T, ∀ H : ℝ, cubicThetaCuspNeighborhood δ H=cubicThetaCuspNeighborhood ε H := by
    have hmem : f δ∈T.image f := by rw [himage]; exact Finset.mem_image.mpr ⟨δ,hδ,rfl⟩
    obtain ⟨ε,hε,he⟩ := Finset.mem_image.mp hmem
    obtain ⟨q,hq⟩ := cubicThetaCuspNeighborhood_one_nonempty δ
    have hne : (cubicThetaCuspNeighborhood δ 1 ∩ cubicThetaCuspNeighborhood ε 1).Nonempty := by
      refine ⟨q,hq,?_⟩
      change q∈f ε
      rw [he]
      exact hq
    exact ⟨ε,hε,cubicThetaCuspNeighborhood_overlap δ ε (le_refl 1) hne⟩
  refine ⟨T,hTS,?_,?_⟩
  · intro H
    ext q
    constructor
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      obtain ⟨ε,hε,he⟩ := hrep δ hδ
      exact mem_iUnion₂.mpr ⟨ε,hε,(he H) ▸ hqδ⟩
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      exact mem_iUnion₂.mpr ⟨δ,hTS hδ,hqδ⟩
  · intro H hH δ hδ ε hε hne
    apply Set.disjoint_left.mpr
    intro q hqδ hqε
    have he := cubicThetaCuspNeighborhood_overlap δ ε hH ⟨q,hqδ,hqε⟩ 1
    exact hne (hT hδ hε he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCuspCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaDisjointCuspCover :
    ∃ S T : Finset SL(2,Eisenstein),
      (∀ V, cubicThetaQuotientCore S V ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ V=univ) ∧
      (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1) := by
  classical
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  obtain ⟨T,_,hT,hd⟩ := cubicThetaFiniteCusps_disjoint (S.image Inv.inv)
  refine ⟨S,T,?_,hd 1 le_rfl⟩
  intro V
  have him : (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ V)=
      ⋃ δ∈S.image Inv.inv,cubicThetaCuspNeighborhood δ V := by
    ext q
    simp
  rw [← hT V,← him]
  exact hS V

lemma cubicThetaCompactCuspCutoff_smooth (T : Finset SL(2,Eisenstein))
    {N : ℝ} (hN : 1≤N) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaCompactCuspCutoff T N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} :=
  contDiffOn_const.sub (ContDiffOn.sum (fun δ _ => cubicThetaScalarCuspQuotient_smooth δ hN))

lemma cubicThetaCompactCuspCutoff_high (T : Finset SL(2,Eisenstein))
    (hd : (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1))
    {N : ℝ} (hN : 1≤N) {δ : SL(2,Eisenstein)} (hδ : δ∈T)
    {q : CubicThetaQuotient} (hq : q∈cubicThetaCuspNeighborhood δ (2*N)) :
    cubicThetaCompactCuspCutoff T N q=0 := by
  classical
  have hqδ := cubicThetaCuspNeighborhood_mono δ (by linarith : (1:ℝ)≤2*N) hq
  have hz (ε : SL(2,Eisenstein)) (hε : ε∈T) (hne : ε≠δ) :
      cubicThetaScalarCuspQuotient ε N q=0 := by
    by_contra h
    have hqε := cubicThetaCuspNeighborhood_mono ε hN (cubicThetaScalarCuspQuotient_support ε hN h)
    exact Set.disjoint_left.mp (hd hε hδ hne) hqε hqδ
  have hsum : (∑ ε∈T,cubicThetaScalarCuspQuotient ε N q)=cubicThetaScalarCuspQuotient δ N q :=
    Finset.sum_eq_single δ hz (fun h => False.elim (h hδ))
  rw [cubicThetaCompactCuspCutoff,hsum,cubicThetaScalarCuspQuotient_high δ hN hq,sub_self]

lemma cubicThetaCompactCuspCutoff_compact (S T : Finset SL(2,Eisenstein))
    (hc : ∀ V, cubicThetaQuotientCore S V ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ V=univ)
    (hd : (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1))
    {N : ℝ} (hN : 1≤N) : HasCompactSupport (cubicThetaCompactCuspCutoff T N) := by
  have hK := cubicThetaQuotientCore_compact S (2*N)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro q hq
  by_contra hn
  have hcover : q∈cubicThetaQuotientCore S (2*N) ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ (2*N) := by
    rw [hc]
    trivial
  obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp (hcover.resolve_left hn)
  exact hq (cubicThetaCompactCuspCutoff_high T hd hN hδ hqδ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspVanishing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar cusp cutoffs vanish uniformly on each compact quotient
set once their height scale is large enough. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaScalarCuspQuotient_compact_zero {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ N : ℝ, C<N → ∀ δ : SL(2,Eisenstein), ∀ q∈K,
      cubicThetaScalarCuspQuotient δ N q=0 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_all_cusp_height_bound hK
  refine ⟨C,hC,fun N hN δ q hq => ?_⟩
  let x := cubicThetaQuotientLift q
  let y := δ⁻¹ • x
  have hzero (r : CubicThetaBottomRow) : cubicThetaScalarCuspTerm N r y.val=0 := by
    have hx : cubicThetaQuotientMap x∈K := by rwa [cubicThetaQuotientLift_map]
    have hr := hbound x hx (r.completion.val*δ⁻¹)
    rw [mul_smul] at hr
    change (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) y.val).2≤C at hr
    rw [← cubicThetaBottomRow_height,r.completion_row] at hr
    exact cubicThetaScalarCuspTerm_zero N (lt_of_le_of_lt hC hN) r (hr.trans hN.le)
  change (∑' r, cubicThetaScalarCuspTerm N r y.val)=0
  simp only [hzero,tsum_zero]

lemma cubicThetaCompactCuspCutoff_compact_one (T : Finset SL(2,Eisenstein))
    {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ N : ℝ, C<N → ∀ q∈K, cubicThetaCompactCuspCutoff T N q=1 := by
  obtain ⟨C,hC,hzero⟩ := cubicThetaScalarCuspQuotient_compact_zero hK
  refine ⟨C,hC,fun N hN q hq => ?_⟩
  simp only [cubicThetaCompactCuspCutoff,hzero N hN _ q hq,Finset.sum_const_zero,sub_zero]

lemma cubicThetaCompactCuspCutoff_local_one (T : Finset SL(2,Eisenstein))
    (q : CubicThetaQuotient) :
    ∃ C≥0, ∀ N : ℝ, C<N → cubicThetaCompactCuspCutoff T N=ᶠ[𝓝 q] (fun _ => (1:ℂ)) := by
  obtain ⟨K,hK,hKq⟩ := exists_compact_mem_nhds q
  obtain ⟨C,hC,h⟩ := cubicThetaCompactCuspCutoff_compact_one T hK
  exact ⟨C,hC,fun N hN => Filter.mem_of_superset hKq (fun x hx => h N hN x hx)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCuspEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform value and hyperbolic differential bounds for the compact
arithmetic exhaustion. Its finite cusp set is fixed while the height grows. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff BigOperators
namespace CubicFirstMoment

lemma cubicThetaScalarCuspQuotient_energy_bound :
    ∃ B≥0, ∀ (δ : SL(2,Eisenstein)) (N : ℝ), 2≤N → ∀ p : ℂ × ℝ, 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaScalarCuspQuotient δ N
        (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p≤B := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaScalarCusp_energy_bound
  refine ⟨B,hB,?_⟩
  intro δ N hN p hp
  have he : (fun y => cubicThetaScalarCuspQuotient δ N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)))=ᶠ[𝓝 p]
      (fun y => cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y)) := by
    filter_upwards [isOpen_lt continuous_const continuous_snd |>.mem_nhds hp] with y hy
    exact cubicThetaScalarCuspQuotient_coordinates δ N hy
  have hf := (cubicThetaScalarCusp_smooth (by linarith : 1≤N)).contDiffAt
    (isOpen_lt continuous_const continuous_snd |>.mem_nhds (cubicThetaMobius_height_pos (cubicThetaFullComplex δ⁻¹) hp))
  have ht := cubicThetaFunctionEnergy_mobius (cubicThetaScalarCusp N)
    (cubicThetaFullComplex δ⁻¹) hp (hf.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  unfold cubicThetaFunctionEnergy
  rw [he.fderiv_eq (𝕜:=ℝ)]
  change p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaScalarCusp N
    (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y)) p≤B
  rw [ht]
  exact hbound N hN _ (cubicThetaMobius_height_pos _ hp)

lemma cubicThetaCompactCuspCutoff_norm (T : Finset SL(2,Eisenstein))
    {N : ℝ} (hN : 1≤N) (q : CubicThetaQuotient) :
    ‖cubicThetaCompactCuspCutoff T N q‖≤1+(T.card:ℝ) := by
  classical
  calc
    _ ≤ ‖(1:ℂ)‖+‖∑ δ∈T,cubicThetaScalarCuspQuotient δ N q‖ := norm_sub_le _ _
    _ ≤ 1+∑ δ∈T,‖cubicThetaScalarCuspQuotient δ N q‖ := by
      simpa only [norm_one] using add_le_add le_rfl
        (norm_sum_le T (fun δ => cubicThetaScalarCuspQuotient δ N q))
    _ ≤ 1+(T.card:ℝ) := by
      have h := Finset.sum_le_sum (fun δ (_ : δ∈T) => cubicThetaScalarCuspQuotient_norm δ hN q)
      simpa using add_le_add_left h 1

lemma cubicThetaCompactCuspCutoff_energy_bound (T : Finset SL(2,Eisenstein)) :
    ∃ B≥0, ∀ N : ℝ, 2≤N → ∀ p : ℂ × ℝ, 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaCompactCuspCutoff T N
        (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p≤B := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaScalarCuspQuotient_energy_bound
  refine ⟨(T.card:ℝ)^2*B,mul_nonneg (sq_nonneg _) hB,?_⟩
  intro N hN p hp
  let f := fun δ y => cubicThetaScalarCuspQuotient δ N
    (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))
  have hf (δ : SL(2,Eisenstein)) : DifferentiableAt ℝ (f δ) p :=
    ((cubicThetaScalarCuspQuotient_smooth δ (by linarith : 1≤N)).contDiffAt
      (isOpen_lt continuous_const continuous_snd |>.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := cubicThetaFunctionEnergy_one_sub (DifferentiableAt.fun_sum (fun δ (_ : δ∈T) => hf δ))
  change p.2^2*cubicThetaFunctionEnergy (fun y => 1-∑ δ∈T,f δ y) p≤_
  rw [he]
  calc
    _ ≤ p.2^2*((T.card:ℝ)*∑ δ∈T,cubicThetaFunctionEnergy (f δ) p) :=
      mul_le_mul_of_nonneg_left (cubicThetaFunctionEnergy_sum_le T f p (fun δ _ => hf δ)) (sq_nonneg _)
    _ = (T.card:ℝ)*∑ δ∈T,p.2^2*cubicThetaFunctionEnergy (f δ) p := by
      rw [← Finset.mul_sum]; ring
    _ ≤ (T.card:ℝ)*∑ δ∈T,B := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun δ _ => hbound δ N hN p hp)) (Nat.cast_nonneg _)
    _ = (T.card:ℝ)^2*B := by simp; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspExhaustion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaCuspExhaustion_smooth (T : Finset SL(2,Eisenstein)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaCuspExhaustion T n
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} :=
  cubicThetaCompactCuspCutoff_smooth T (by linarith [Nat.cast_nonneg (α:=ℝ) n])

lemma cubicThetaCuspExhaustion_compact (S T : Finset SL(2,Eisenstein))
    (hc : ∀ V, cubicThetaQuotientCore S V ∪ ⋃ δ∈T,cubicThetaCuspNeighborhood δ V=univ)
    (hd : (T : Set SL(2,Eisenstein)).PairwiseDisjoint (fun δ => cubicThetaCuspNeighborhood δ 1))
    (n : ℕ) : HasCompactSupport (cubicThetaCuspExhaustion T n) :=
  cubicThetaCompactCuspCutoff_compact S T hc hd (by linarith [Nat.cast_nonneg (α:=ℝ) n])

lemma cubicThetaCuspExhaustion_local_one (T : Finset SL(2,Eisenstein)) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, (cubicThetaCuspExhaustion T n : CubicThetaQuotient → ℂ)=ᶠ[𝓝 q] (fun _ => 1) := by
  obtain ⟨C,_,hC⟩ := cubicThetaCompactCuspCutoff_local_one T q
  have hn : ∀ᶠ n : ℕ in atTop, C<(n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop C)
  filter_upwards [hn] with n hn
  exact hC _ (by linarith)

lemma cubicThetaCuspExhaustion_value_one (T : Finset SL(2,Eisenstein)) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, cubicThetaCuspExhaustion T n q=1 :=
  (cubicThetaCuspExhaustion_local_one T q).mono (fun _ h => h.eq_of_nhds)

lemma cubicThetaCuspExhaustion_gradient_agrees (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, cubicThetaGradientRepresentative
      (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q=cubicThetaGradientRepresentative F q := by
  filter_upwards [cubicThetaCuspExhaustion_local_one T q] with n hn
  unfold cubicThetaGradientRepresentative
  apply cubicThetaSectionCutoff_local_gradient
  rwa [cubicThetaBorelSection_rightInverse]

lemma cubicThetaCuspExhaustion_value_agrees (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection) (q : CubicThetaQuotient) :
    ∀ᶠ n : ℕ in atTop, cubicThetaSectionRepresentative
      (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q=cubicThetaSectionRepresentative F q := by
  filter_upwards [cubicThetaCuspExhaustion_value_one T q] with n hn
  change cubicThetaCuspExhaustion T n (cubicThetaQuotientMap (cubicThetaBorelSection q))*
    cubicThetaSectionRepresentative F q=cubicThetaSectionRepresentative F q
  rw [cubicThetaBorelSection_rightInverse,hn,one_mul]

lemma cubicThetaCuspExhaustion_norm (T : Finset SL(2,Eisenstein)) (n : ℕ) (q : CubicThetaQuotient) :
    ‖cubicThetaCuspExhaustion T n q‖≤1+(T.card:ℝ) :=
  cubicThetaCompactCuspCutoff_norm T (by linarith [Nat.cast_nonneg (α:=ℝ) n]) q

lemma cubicThetaCuspExhaustion_energy (T : Finset SL(2,Eisenstein)) :
    ∃ B≥0, ∀ (n : ℕ) (p : ℂ × ℝ), 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaCuspExhaustion T n
        (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) p≤B := by
  obtain ⟨B,hB,h⟩ := cubicThetaCompactCuspCutoff_energy_bound T
  exact ⟨B,hB,fun n p hp => h _ (by linarith [Nat.cast_nonneg (α:=ℝ) n]) p hp⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspExhaustionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common square-integrable majorant for the exhaustion errors. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspExhaustion_sub_one_norm (T : Finset SL(2,Eisenstein))
    (n : ℕ) (q : CubicThetaQuotient) :
    ‖cubicThetaCuspExhaustion T n q-1‖≤2+(T.card:ℝ) := by
  have h := (norm_sub_le (cubicThetaCuspExhaustion T n q) 1).trans
    (add_le_add (cubicThetaCuspExhaustion_norm T n q) (le_refl ‖(1:ℂ)‖))
  exact h.trans_eq (by rw [norm_one]; ring)

lemma cubicThetaCuspExhaustion_value_bound (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection) (n : ℕ) (q : CubicThetaQuotient) :
    ‖cubicThetaSectionRepresentative (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q-
      cubicThetaSectionRepresentative F q‖^2≤
      (2+(T.card:ℝ))^2*‖cubicThetaSectionRepresentative F q‖^2 := by
  have he : cubicThetaSectionRepresentative (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q-
      cubicThetaSectionRepresentative F q=
      (cubicThetaCuspExhaustion T n q-1)*cubicThetaSectionRepresentative F q := by
    unfold cubicThetaSectionRepresentative
    change cubicThetaCuspExhaustion T n (cubicThetaQuotientMap (cubicThetaBorelSection q))*_ -_=_
    rw [cubicThetaBorelSection_rightInverse]
    ring
  rw [he,norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (_root_.norm_nonneg _) (cubicThetaCuspExhaustion_sub_one_norm T n q) 2

lemma cubicThetaCuspExhaustion_gradient_bound (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ∃ B≥0, ∀ (n : ℕ) (q : CubicThetaQuotient),
      ‖cubicThetaGradientRepresentative (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q-
        cubicThetaGradientRepresentative F q‖^2≤
      2*(2+(T.card:ℝ))^2*‖cubicThetaGradientRepresentative F q‖^2+
        2*B*‖cubicThetaSectionRepresentative F q‖^2 := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaCuspExhaustion_energy T
  refine ⟨B,hB,fun n q => ?_⟩
  have h := cubicThetaSectionCutoff_gradient_error (cubicThetaCuspExhaustion T n)
    ((cubicThetaCuspExhaustion_smooth T n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) F hF (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse] at h
  change _≤2*‖cubicThetaCuspExhaustion T n q-1‖^2*‖cubicThetaGradientRepresentative F q‖^2+
    2*‖cubicThetaSectionRepresentative F q‖^2*_
    at h
  apply h.trans
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _)
    (cubicThetaCuspExhaustion_sub_one_norm T n q) 2
  have he := hbound n (cubicThetaBorelSection q).val (cubicThetaBorelSection q).property
  have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2))
    (sq_nonneg ‖cubicThetaGradientRepresentative F q‖)
  have h₂ := mul_le_mul_of_nonneg_left he
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg ‖cubicThetaSectionRepresentative F q‖))
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergyClosure
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every C1 automorphic section with square-integrable value and gradient
belongs to the actual closed energy graph. Compact cusp exhaustion supplies
the approximants, with no extra boundary condition imposed at the cusps. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaFiniteEnergy_mem_graph (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hv : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    (hg : MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure) :
    WithLp.toLp 2 (hv.toLp _,hg.toLp _)∈cubicThetaGlobalEnergySpace := by
  obtain ⟨S,T,hcover,hdisj⟩ := cubicThetaDisjointCuspCover
  let G := fun n : ℕ => cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F
  have hG (n : ℕ) : ContDiffOn ℝ 1 (cubicThetaSectionFunction (G n)) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaSectionCutoff_regular _ ((cubicThetaCuspExhaustion_smooth T n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) F hF
  have hcG (n : ℕ) : HasCompactSupport (cubicThetaSectionNorm (G n)) :=
    cubicThetaSectionCutoff_compact _ F (cubicThetaCuspExhaustion_compact S T hcover hdisj n)
  have hvG (n : ℕ) := cubicThetaCompactSection_memLp (G n) (hcG n)
  have hgG (n : ℕ) := cubicThetaC1Gradient_memLp (G n) (hG n) (hcG n)
  have hiv := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hig := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hvlim : Tendsto (fun n => (hvG n).toLp _) atTop (𝓝 (hv.toLp _)) := by
    apply cubicThetaL2_tendsto_of_dominated_sq _ _ hvG hv
      (fun q => (2+(T.card:ℝ))^2*‖cubicThetaSectionRepresentative F q‖^2)
      (hiv.const_mul _)
    · intro n
      exact Filter.Eventually.of_forall (cubicThetaCuspExhaustion_value_bound T F n)
    · apply Filter.Eventually.of_forall
      intro q
      have he : (fun n => cubicThetaSectionRepresentative (G n) q)=ᶠ[atTop]
          (fun _ => cubicThetaSectionRepresentative F q) := cubicThetaCuspExhaustion_value_agrees T F q
      exact tendsto_const_nhds.congr' he.symm
  obtain ⟨B,_,hbound⟩ := cubicThetaCuspExhaustion_gradient_bound T F hF
  have hglim : Tendsto (fun n => (hgG n).toLp _) atTop (𝓝 (hg.toLp _)) := by
    apply cubicThetaL2_tendsto_of_dominated_sq _ _ hgG hg
      (fun q => 2*(2+(T.card:ℝ))^2*‖cubicThetaGradientRepresentative F q‖^2+
        2*B*‖cubicThetaSectionRepresentative F q‖^2)
      ((hig.const_mul _).add (hiv.const_mul _))
    · intro n
      exact Filter.Eventually.of_forall (hbound n)
    · apply Filter.Eventually.of_forall
      intro q
      have he : (fun n => cubicThetaGradientRepresentative (G n) q)=ᶠ[atTop]
          (fun _ => cubicThetaGradientRepresentative F q) := cubicThetaCuspExhaustion_gradient_agrees T F q
      exact tendsto_const_nhds.congr' he.symm
  have hlim : Tendsto (fun n => cubicThetaC1EnergyData (G n) (hG n) (hcG n)) atTop
      (𝓝 (WithLp.toLp 2 (hv.toLp _,hg.toLp _))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).symm.continuous.tendsto
      (hv.toLp _,hg.toLp _)).comp (hvlim.prodMk_nhds hglim)
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n => cubicThetaCompactC1_mem_energy (G n) (hG n) (hcG n)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergySections
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

def cubicThetaFiniteEnergyEmbedding : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  (((WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).symm.toLinearMap).comp
    (cubicThetaFiniteEnergyValue.prod cubicThetaFiniteEnergyGradient)).codRestrict
      cubicThetaGlobalEnergySpace (fun F => cubicThetaFiniteEnergy_mem_graph F F.property.1
        F.property.2.1 F.property.2.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaLocalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local cutoff estimate in intrinsic quotient variables. This is
the pointwise bridge from the actual local graph to the global energy. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_energy_density (F : cubicThetaSmoothTests)
    (p : CubicThetaPoint) :
    ‖cubicThetaLocalEnergyJet (cubicThetaSectionFunction F) p.val‖^2=
      (cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
        cubicThetaQuotientEnergy F (cubicThetaQuotientMap p))/p.val.2^3 := by
  rw [cubicThetaLocalEnergyJet_density _ p.property,cubicThetaSectionNorm_apply,
    cubicThetaQuotientEnergy_apply]
  congr 1
  rw [cubicThetaSectionFunction_apply F p.property]
  rfl

theorem cubicThetaSectionCutoffEnergy_bound {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ C≥0, ∀ (F : cubicThetaSmoothTests) (p : CubicThetaPoint),
      ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) p.val‖^2≤
        C*((cubicThetaSectionNorm F (cubicThetaQuotientMap p))^2+
          cubicThetaQuotientEnergy F (cubicThetaQuotientMap p))/p.val.2^3 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCutoffEnergyCoefficient_bounded
    (hφ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hc
  refine ⟨C,hC,fun F p => ?_⟩
  have he := cubicThetaLocalEnergyJet_cutoff_le p.property
    (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p.val)
    (cubicThetaSectionFunction_differentiable F p.property)
  change ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) p.val‖^2≤_ at he
  have hmul := mul_le_mul_of_nonneg_right (hbound p.val)
    (sq_nonneg ‖cubicThetaLocalEnergyJet (cubicThetaSectionFunction F) p.val‖)
  have h := he.trans hmul
  rw [cubicThetaSectionFunction_energy_density F p] at h
  simpa only [mul_div_assoc] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalLocalizationBound
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundedness of each actual compact chart localization from the
global energy graph to its weighted local energy graph. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaIntrinsicCoordinateEnergy (F : cubicThetaSmoothTests) (y : ℂ × ℝ) : ℝ :=
  let q := cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)
  cubicThetaSectionNorm F q^2+cubicThetaQuotientEnergy F q

lemma cubicThetaIntrinsicCoordinateEnergy_apply (F : cubicThetaSmoothTests)
    (p : CubicThetaPoint) :
    cubicThetaIntrinsicCoordinateEnergy F (cubicThetaPointCoordinates p)=
      cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+cubicThetaSectionEnergy F p := by
  have he : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaIntrinsicCoordinateEnergy,cubicThetaPointCoordinates,he,
    cubicThetaQuotientEnergy_apply]

lemma cubicThetaIntrinsicCoordinateEnergy_continuousOn (F : cubicThetaSmoothTests) :
    ContinuousOn (fun y => cubicThetaIntrinsicCoordinateEnergy F y/y.2^3)
      {y : ℂ × ℝ | 0<y.2} := by
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hq := cubicThetaQuotientMap_open.continuous.comp_continuousOn hinc
  have hcont := ((cubicThetaSectionNorm_continuous F).pow 2).add
    (cubicThetaQuotientEnergy_continuous F)
  exact (hcont.comp_continuousOn hq).div (continuous_snd.pow 3).continuousOn
    (fun y hy => pow_ne_zero 3 hy.ne')

theorem cubicThetaGlobalLocalization_bound {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
    (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S) :
    ∃ C≥0, ∀ F : cubicThetaSmoothTests,
      ‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2≤C*‖cubicThetaGlobalEnergyTest F‖^2 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaSectionCutoffEnergy_bound hφ hc
  refine ⟨C,hC,fun F => ?_⟩
  let K := cubicThetaPointCoordinates '' S
  have hK : IsCompact K := hS.image continuous_subtype_val
  have hKpos : K⊆{y : ℂ × ℝ | 0<y.2} := by
    rintro _ ⟨p,_,rfl⟩
    exact p.property
  have hr : IntegrableOn (fun y => cubicThetaIntrinsicCoordinateEnergy F y/y.2^3) K :=
    ((cubicThetaIntrinsicCoordinateEnergy_continuousOn F).mono hKpos).integrableOn_compact hK
  have hj := (cubicThetaLocalSectionJet_memLp hφ hc hp F).integrable_norm_pow (by norm_num)
  have hmono : (∫ y in K, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2)≤
      C*(∫ y in K, cubicThetaIntrinsicCoordinateEnergy F y/y.2^3) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hj.integrableOn (hr.const_mul C) hK.measurableSet
    rintro _ ⟨p,hpS,rfl⟩
    rw [cubicThetaIntrinsicCoordinateEnergy_apply]
    simpa only [mul_div_assoc,cubicThetaQuotientEnergy_apply,cubicThetaPointCoordinates] using hbound F p
  have hint : (∫ y in K, cubicThetaIntrinsicCoordinateEnergy F y/y.2^3)≤
      ‖cubicThetaGlobalEnergyTest F‖^2 := by
    rw [← cubicThetaPointIntegral_density hS.measurableSet]
    have heq : (∫ p in S, cubicThetaIntrinsicCoordinateEnergy F (cubicThetaPointCoordinates p)
        ∂cubicThetaPointMeasure)=
        ∫ p in S, cubicThetaSectionNorm F (cubicThetaQuotientMap p)^2+
          cubicThetaSectionEnergy F p ∂cubicThetaPointMeasure := by
      apply setIntegral_congr_fun hS.measurableSet
      intro p _
      exact cubicThetaIntrinsicCoordinateEnergy_apply F p
    rw [heq]
    exact cubicThetaChart_energy_le e he hS.measurableSet hSe F
  have hfull : (∫ y in K, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2)=
      ∫ y, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have ht : y∉tsupport (cubicThetaTestLocalization φ F) :=
      fun h => hy (hsupp (tsupport_mul_subset_left h))
    rw [cubicThetaLocalEnergyJet_zero ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  have hn : ‖cubicThetaLocalEnergyGraph hφ hc hp F‖^2=
      ∫ y, ‖cubicThetaLocalEnergyJet (cubicThetaTestLocalization φ F) y‖^2 := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaLocalSectionJet_memLp hφ hc hp F).coeFn_toLp] with y hy
    change ‖((cubicThetaLocalSectionJet_memLp hφ hc hp F).toLp _) y‖^2=_
    rw [hy]
  rw [hn,← hfull]
  exact hmono.trans (mul_le_mul_of_nonneg_left hint hC)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalLocalRellich
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact localization of the completed global automorphic energy
space in an actual injective compact chart. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.globalLocalRellich_smoothGroup
def cubicThetaGlobalEnergyTestLinear : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaGlobalEnergyGraph.codRestrict cubicThetaGlobalEnergySpace
    (fun F => Submodule.le_topologicalClosure cubicThetaGlobalEnergyGraph.range ⟨F,rfl⟩)

lemma cubicThetaGlobalEnergyTestLinear_dense : DenseRange cubicThetaGlobalEnergyTestLinear := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range cubicThetaGlobalEnergyTestLinear=
      Set.range cubicThetaGlobalEnergyGraph := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaGlobalEnergyTestLinear F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
  (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
  (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
  {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
  (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S)

include e he hS hSe hsupp in
lemma cubicThetaGlobalToLocal_bound : ∃ C, ∀ F : cubicThetaSmoothTests,
    ‖cubicThetaLocalEnergyTestLinear hφ hc hp F‖≤C*‖cubicThetaGlobalEnergyTestLinear F‖ := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaGlobalLocalization_bound hφ hc hp e he hS hSe hsupp
  refine ⟨Real.sqrt C,fun F => ?_⟩
  have hs : ‖cubicThetaLocalEnergyTestLinear hφ hc hp F‖^2≤
      C*‖cubicThetaGlobalEnergyTestLinear F‖^2 := hbound F
  have hsqrt : (Real.sqrt C*‖cubicThetaGlobalEnergyTestLinear F‖)^2=
      C*‖cubicThetaGlobalEnergyTestLinear F‖^2 := by rw [mul_pow,Real.sq_sqrt hC]
  exact _root_.le_of_sq_le_sq (hs.trans_eq hsqrt.symm)
    (mul_nonneg (Real.sqrt_nonneg C) (_root_.norm_nonneg _))

def cubicThetaGlobalToLocalEnergy : cubicThetaGlobalEnergySpace →L[ℂ]
    cubicThetaLocalEnergySpace hφ hc hp :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=↥cubicThetaSmoothTests) (Eₗ:=↥cubicThetaGlobalEnergySpace)
    (F:=↥(cubicThetaLocalEnergySpace hφ hc hp))
    (cubicThetaLocalEnergyTestLinear hφ hc hp) cubicThetaGlobalEnergyTestLinear

include e he hS hSe hsupp in
lemma cubicThetaGlobalToLocalEnergy_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalToLocalEnergy hφ hc hp (cubicThetaGlobalEnergyTest F)=
      LocalSobolev.localEnergyTest hφ hc hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=↥cubicThetaSmoothTests) (Eₗ:=↥cubicThetaGlobalEnergySpace)
    (F:=↥(cubicThetaLocalEnergySpace hφ hc hp))
    (f:=cubicThetaLocalEnergyTestLinear hφ hc hp) (e:=cubicThetaGlobalEnergyTestLinear)
    cubicThetaGlobalEnergyTestLinear_dense
    (cubicThetaGlobalToLocal_bound hφ hc hp e he hS hSe hsupp) F

def cubicThetaGlobalLocalInclusion : cubicThetaGlobalEnergySpace →L[ℝ] LocalSobolev.TangentComplexL2 :=
  (LocalSobolev.localEnergyInclusion hφ hc hp).comp
    ((cubicThetaGlobalToLocalEnergy hφ hc hp).restrictScalars ℝ)

theorem cubicThetaGlobalLocalInclusion_compact :
    IsCompactOperator (cubicThetaGlobalLocalInclusion hφ hc hp) :=
  (LocalSobolev.localEnergyInclusion_compact hφ hc hp).comp_clm
    ((cubicThetaGlobalToLocalEnergy hφ hc hp).restrictScalars ℝ)

include e he hS hSe hsupp in
theorem cubicThetaGlobalLocalInclusion_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
      LocalSobolev.tangentFunctionL2 (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (cubicThetaTestLocalization_compact hc F) := by
  change LocalSobolev.localEnergyInclusion hφ hc hp
    (cubicThetaGlobalToLocalEnergy hφ hc hp (cubicThetaGlobalEnergyTest F))=_
  rw [cubicThetaGlobalToLocalEnergy_test hφ hc hp e he hS hSe hsupp]
  exact LocalSobolev.localEnergyInclusion_test hφ hc hp F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded restriction from the completed global energy space to the
literal high cusp strip, extending all actual C1 finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

local instance finiteEnergy_addCommGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaCuspRestriction : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaStripL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaFiniteEnergySections) (Eₗ:=cubicThetaGlobalEnergySpace) (F:=CubicThetaStripL2)
    cubicThetaFiniteCuspRestriction cubicThetaFiniteEnergyEmbedding

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticGradientMass
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual gradient energy of the arithmetic remainder is integrable
in every cusp, with the same convergent vertical power as its mass. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaArithmeticCoordinateEnergy (δ : SL(2,Eisenstein)) (s : ℂ) (hs : 2 < s.re)
    (y : ℂ × ℝ) : ℝ :=
  cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • cubicThetaPointInclusion.symm y)

lemma cubicThetaArithmeticCoordinateEnergy_apply (δ : SL(2,Eisenstein))
    (s : ℂ) (hs : 2 < s.re) (p : CubicThetaPoint) :
    cubicThetaArithmeticCoordinateEnergy δ s hs (cubicThetaPointCoordinates p)=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (δ • p) := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaArithmeticCoordinateEnergy,h]

lemma cubicThetaArithmeticCoordinateEnergy_density_bound (δ : SL(2,Eisenstein))
    {s : ℂ} (hs : 3 < s.re) {y : ℂ × ℝ} (hy : 2<y.2) {R : ℝ}
    (hR : Complex.normSq y.1≤R) :
    cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y/y.2^3≤
      ((Module.finrank ℝ CubicThetaTangent:ℝ)*
        (6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeMass s)^2)*y.2^(5-2*s.re) := by
  have hy0 : 0<y.2 := by linarith
  let p : CubicThetaPoint := ⟨y,hy0⟩
  let A := 6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeMass s
  let D := (Module.finrank ℝ CubicThetaTangent:ℝ)
  have hD : 0≤D := Nat.cast_nonneg _
  have hb := cubicThetaArithmeticCusp_fderiv_bound δ hs hy hR
  have hb' : ‖fderiv ℝ (fun q => cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex δ) q) s) y‖≤A*y.2^(3-s.re) := by
    exact hb.trans_eq (by dsimp [A]; ring)
  have hsq := mul_self_le_mul_self (_root_.norm_nonneg _) hb'
  simp only [← pow_two] at hsq
  have he : (y.2^(3-s.re))^2/y.2=y.2^(5-2*s.re) := by
    rw [← Real.rpow_mul_natCast hy0.le,← Real.rpow_sub_one hy0.ne']
    congr 1
    norm_num
    ring
  have hec := cubicThetaArithmeticCusp_energy_le δ (s:=s) (by linarith) p
  have hec' : cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y≤
      D*y.2^2*(A*y.2^(3-s.re))^2 := by
    change cubicThetaArithmeticCoordinateEnergy δ s (by linarith) (cubicThetaPointCoordinates p)≤_
    rw [cubicThetaArithmeticCoordinateEnergy_apply]
    exact hec.trans (mul_le_mul_of_nonneg_left hsq (mul_nonneg hD (sq_nonneg _)))
  calc
    _ ≤ (D*y.2^2*(A*y.2^(3-s.re))^2)/y.2^3 :=
      div_le_div_of_nonneg_right hec' (pow_nonneg hy0.le 3)
    _ = D*A^2*((y.2^(3-s.re))^2/y.2) := by field_simp [hy0.ne']
    _ = _ := by rw [he]

lemma cubicThetaArithmeticCoordinateEnergy_density_continuousOn (δ : SL(2,Eisenstein))
    (s : ℂ) (hs : 2 < s.re) :
    ContinuousOn (fun y => cubicThetaArithmeticCoordinateEnergy δ s hs y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  intro y hy
  have hy0 : 0<y.2 := lt_trans (by norm_num : (0:ℝ)<2) hy.2
  have hi : ContinuousAt (fun y => cubicThetaPointInclusion.symm y) y :=
    cubicThetaPointInclusion.symm.continuousAt (by
      change y ∈ cubicThetaPointInclusion.target
      rw [cubicThetaPointInclusion_target]
      exact hy0)
  have he := (cubicThetaArithmeticEnergy_continuous hs).continuousAt.comp
    ((continuous_const_smul δ).continuousAt.comp hi)
  exact (he.div (continuousAt_snd.pow 3) (pow_ne_zero 3 hy0.ne')).continuousWithinAt

theorem cubicThetaArithmeticCoordinateEnergy_integrable (δ : SL(2,Eisenstein))
    {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun y => cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  obtain ⟨R,_,hR⟩ := cubicThetaHorizontalCell_normSq_bound
  let C := (Module.finrank ℝ CubicThetaTangent:ℝ)*
    (6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeMass s)^2
  have hh : IntegrableOn (fun _ : ℂ => C) cubicThetaHorizontalCell :=
    integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(5-2*s.re)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  apply hm.mono'
  · exact (cubicThetaArithmeticCoordinateEnergy_density_continuousOn δ s (by linarith)).aestronglyMeasurable
      (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hn : 0 ≤ cubicThetaArithmeticCoordinateEnergy δ s (by linarith) y :=
      mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hn
      (pow_nonneg (lt_trans (by norm_num : (0:ℝ)<2) hy.2).le 3))]
    exact cubicThetaArithmeticCoordinateEnergy_density_bound δ hs hy.2 (hR y.1 hy.1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAnnularL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial annulus transport is a bounded linear map to the actual
global L2 space, with its norm bounded by the mass of a compact core. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaAnnularSeries_core :
    ∃ S : Finset (Matrix.SpecialLinearGroup (Fin 2) Eisenstein),
      ∀ (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 2 →
        cubicThetaAnnularSeries f p=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspTransition_core
  refine ⟨S,fun f p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaAnnularTerm f r p=0 by
    simp only [cubicThetaAnnularSeries,hz,tsum_zero]
  intro r
  by_contra hn
  have hh := cubicThetaAnnularTerm_high hn
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; exact hh.1.le) (by rw [he]; exact hh.2.le)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact hp hq

lemma cubicThetaAnnularRepresentative_measurable (f : C(CubicThetaForcingBand,ℂ)) :
    Measurable (cubicThetaAnnularRepresentative f) :=
  (cubicThetaAnnularSeries_measurable f).comp cubicThetaBorelSection_measurable

lemma cubicThetaAnnularRepresentative_memLp (f : C(CubicThetaForcingBand,ℂ)) :
    MemLp (cubicThetaAnnularRepresentative f) 2 cubicThetaQuotientMeasure := by
  obtain ⟨S,hS⟩ := cubicThetaAnnularSeries_core
  have hK := cubicThetaQuotientCore_compact S 2
  have hi : MemLp ((cubicThetaQuotientCore S 2).indicator (fun _ => ‖f‖)) 2
      cubicThetaQuotientMeasure :=
    memLp_indicator_const 2 hK.measurableSet ‖f‖ (Or.inr hK.measure_ne_top)
  apply hi.mono' (cubicThetaAnnularRepresentative_measurable f).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q∈cubicThetaQuotientCore S 2
  · rw [indicator_of_mem hq]
    exact cubicThetaAnnularSeries_norm f _
  · rw [indicator_of_notMem hq]
    have hz := hS f (cubicThetaBorelSection q) (by rwa [cubicThetaBorelSection_rightInverse])
    change ‖cubicThetaAnnularSeries f (cubicThetaBorelSection q)‖≤0
    rw [hz,norm_zero]

def cubicThetaAnnularL2Linear : C(CubicThetaForcingBand,ℂ) →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun f := (cubicThetaAnnularRepresentative_memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(cubicThetaAnnularRepresentative_memLp (f+g)).coeFn_toLp,
      (cubicThetaAnnularRepresentative_memLp f).coeFn_toLp,
      (cubicThetaAnnularRepresentative_memLp g).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaAnnularRepresentative_memLp f).toLp _)
        ((cubicThetaAnnularRepresentative_memLp g).toLp _)] with q hfg hf hg ha
    simp only [Pi.add_apply] at ha
    rw [hfg,ha,hf,hg]
    exact cubicThetaAnnularSeries_add f g _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(cubicThetaAnnularRepresentative_memLp (c • f)).coeFn_toLp,
      (cubicThetaAnnularRepresentative_memLp f).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaAnnularRepresentative_memLp f).toLp _)] with q hcf hf hc
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hc
    rw [hcf,hc,hf]
    exact cubicThetaAnnularSeries_smul c f _

lemma cubicThetaAnnularL2Linear_bound :
    ∃ C : ℝ, ∀ f : C(CubicThetaForcingBand,ℂ), ‖cubicThetaAnnularL2Linear f‖≤C*‖f‖ := by
  obtain ⟨S,hS⟩ := cubicThetaAnnularSeries_core
  have hK := cubicThetaQuotientCore_compact S 2
  let g : Lp ℝ 2 cubicThetaQuotientMeasure :=
    indicatorConstLp 2 hK.measurableSet hK.measure_ne_top 1
  refine ⟨‖g‖,fun f => ?_⟩
  have hb : ∀ᵐ q ∂cubicThetaQuotientMeasure,
      ‖cubicThetaAnnularL2Linear f q‖≤‖f‖*‖g q‖ := by
    filter_upwards [(cubicThetaAnnularRepresentative_memLp f).coeFn_toLp,
      indicatorConstLp_coeFn (p:=2) (hs:=hK.measurableSet) (hμs:=hK.measure_ne_top) (c:=(1:ℝ))]
      with q hf hg
    change (cubicThetaAnnularL2Linear f) q=_ at hf
    change g q=_ at hg
    rw [hf,hg]
    by_cases hq : q∈cubicThetaQuotientCore S 2
    · rw [indicator_of_mem hq,norm_one,mul_one]
      exact cubicThetaAnnularSeries_norm f _
    · rw [indicator_of_notMem hq,norm_zero,mul_zero]
      have hz := hS f (cubicThetaBorelSection q) (by rwa [cubicThetaBorelSection_rightInverse])
      change ‖cubicThetaAnnularSeries f (cubicThetaBorelSection q)‖≤0
      rw [hz,norm_zero]
  simpa only [mul_comm] using Lp.norm_le_mul_norm_of_ae_le_mul hb

def cubicThetaAnnularL2 : C(CubicThetaForcingBand,ℂ) →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaAnnularL2Linear.mkContinuous
    cubicThetaAnnularL2Linear_bound.choose cubicThetaAnnularL2Linear_bound.choose_spec

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.instMeasurableSpace
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

lemma cubicThetaForcingL2_profile (s : ℂ) :
    cubicThetaForcingL2 s=cubicThetaAnnularL2 (cubicThetaForcingProfile s) := by
  apply Lp.ext
  filter_upwards [(cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s)).coeFn_toLp,
    (cubicThetaAnnularRepresentative_memLp (cubicThetaForcingProfile s)).coeFn_toLp]
    with q h₁ h₂
  change (cubicThetaForcingL2 s) q=_ at h₁
  change (cubicThetaAnnularL2 (cubicThetaForcingProfile s)) q=_ at h₂
  rw [h₁,h₂]
  exact (cubicThetaAnnularSeries_forcing s (cubicThetaBorelSection q)).symm

theorem cubicThetaForcingL2_analytic (s : ℂ) : AnalyticAt ℂ cubicThetaForcingL2 s := by
  have h := cubicThetaAnnularL2.analyticAt (cubicThetaForcingProfile s) |>.comp
    (f:=cubicThetaForcingProfile) (x:=s) (cubicThetaForcingProfile_analytic s)
  have he : cubicThetaForcingL2=cubicThetaAnnularL2 ∘ cubicThetaForcingProfile :=
    funext cubicThetaForcingL2_profile
  rwa [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexLocalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

variable (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
  (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
  {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
  (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S)

local instance complexLocalization_borel_r3cd050_1 : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance complexLocalization_borelSpace_r3cd050_1 : BorelSpace CubicThetaTangent := ⟨rfl⟩
attribute [local instance] OAI.CubicFirstMoment.complexLocalization_smoothGroup
include e he hS hSe hsupp in
lemma cubicThetaLocalValue_bound : ∃ C, ∀ F : cubicThetaSmoothTests,
    ‖cubicThetaLocalValue hφ hc hp F‖≤C*‖cubicThetaGlobalEnergyTestLinear F‖ := by
  refine ⟨‖cubicThetaGlobalLocalInclusion hφ hc hp‖,fun F => ?_⟩
  rw [cubicThetaLocalValue_apply,← cubicThetaGlobalLocalInclusion_test hφ hc hp e he hS hSe hsupp F]
  exact (cubicThetaGlobalLocalInclusion hφ hc hp).le_opNorm (cubicThetaGlobalEnergyTest F)

def cubicThetaComplexLocalInclusion : cubicThetaGlobalEnergySpace →L[ℂ] LocalSobolev.TangentComplexL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=↥cubicThetaSmoothTests) (Eₗ:=↥cubicThetaGlobalEnergySpace)
    (F:=LocalSobolev.TangentComplexL2)
    (cubicThetaLocalValue hφ hc hp) cubicThetaGlobalEnergyTestLinear

include e he hS hSe hsupp in
lemma cubicThetaComplexLocalInclusion_test (F : cubicThetaSmoothTests) :
    cubicThetaComplexLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
      cubicThetaLocalValue hφ hc hp F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaLocalValue hφ hc hp) (e:=cubicThetaGlobalEnergyTestLinear)
    cubicThetaGlobalEnergyTestLinear_dense (cubicThetaLocalValue_bound hφ hc hp e he hS hSe hsupp) F

include e he hS hSe hsupp in
theorem cubicThetaComplexLocalInclusion_eq :
    (cubicThetaComplexLocalInclusion hφ hc hp : cubicThetaGlobalEnergySpace → LocalSobolev.TangentComplexL2)=
      cubicThetaGlobalLocalInclusion hφ hc hp := by
  apply cubicThetaGlobalEnergyTestLinear_dense.equalizer
    (cubicThetaComplexLocalInclusion hφ hc hp).continuous
    (cubicThetaGlobalLocalInclusion hφ hc hp).continuous
  funext F
  change cubicThetaComplexLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
    cubicThetaGlobalLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)
  rw [cubicThetaComplexLocalInclusion_test hφ hc hp e he hS hSe hsupp,
    cubicThetaGlobalLocalInclusion_test hφ hc hp e he hS hSe hsupp,cubicThetaLocalValue_apply]

include e he hS hSe hsupp in
theorem cubicThetaComplexLocalInclusion_compact :
    IsCompactOperator (cubicThetaComplexLocalInclusion hφ hc hp) := by
  rw [cubicThetaComplexLocalInclusion_eq hφ hc hp e he hS hSe hsupp]
  exact cubicThetaGlobalLocalInclusion_compact hφ hc hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreLocalRellich
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The abstract chart estimate applies to the actual arithmetic core
profiles already constructed from the quotient's smooth bump functions. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaCorePointSupport (c : CubicThetaQuotient) : Set CubicThetaPoint :=
  cubicThetaPointInclusion.symm '' tsupport (cubicThetaCoreProfile c)

lemma cubicThetaCorePointSupport_compact (c : CubicThetaQuotient) :
    IsCompact (cubicThetaCorePointSupport c) := by
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  exact (cubicThetaCoreProfile_compact c).image_of_continuousOn
    (hinc.mono (cubicThetaCoreProfile_support_positive c))

lemma cubicThetaCorePointSupport_sheet (c : CubicThetaQuotient) :
    cubicThetaCorePointSupport c⊆(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source := by
  rintro p ⟨y,hy,rfl⟩
  have ht := cubicThetaCoreProfile_support_target c hy
  change y∈cubicThetaPointInclusion.target ∧
    cubicThetaPointInclusion.symm y∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source at ht
  exact ht.2

lemma cubicThetaCoreProfile_support_coordinates (c : CubicThetaQuotient) :
    tsupport (cubicThetaCoreProfile c)⊆cubicThetaPointCoordinates '' cubicThetaCorePointSupport c := by
  intro y hy
  refine ⟨cubicThetaPointInclusion.symm y,⟨y,hy,rfl⟩,?_⟩
  exact cubicThetaPointInclusion.right_inv
    (by rw [cubicThetaPointInclusion_target]; exact cubicThetaCoreProfile_support_positive c hy)

def cubicThetaCoreLocalInclusion (c : CubicThetaQuotient) :
    cubicThetaGlobalEnergySpace →L[ℂ] LocalSobolev.TangentComplexL2 :=
  cubicThetaComplexLocalInclusion (cubicThetaCoreProfile_contDiff c)
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)

theorem cubicThetaCoreLocalInclusion_compact (c : CubicThetaQuotient) :
    IsCompactOperator (cubicThetaCoreLocalInclusion c) :=
  cubicThetaComplexLocalInclusion_compact (cubicThetaCoreProfile_contDiff c)
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
    (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    (cubicThetaCorePointSupport_compact c) (cubicThetaCorePointSupport_sheet c)
    (cubicThetaCoreProfile_support_coordinates c)

theorem cubicThetaCoreLocalInclusion_test (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    cubicThetaCoreLocalInclusion c (cubicThetaGlobalEnergyTest F)=
      cubicThetaLocalValue (cubicThetaCoreProfile_contDiff c)
        (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c) F :=
  cubicThetaComplexLocalInclusion_test (cubicThetaCoreProfile_contDiff c)
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
    (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    (cubicThetaCorePointSupport_compact c) (cubicThetaCorePointSupport_sheet c)
    (cubicThetaCoreProfile_support_coordinates c) F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreBumpIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of a global core cutoff equals the scalar integral over
its actual covering sheet. This retains the cubic section's unit twist. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoreBump_support_image (c : CubicThetaQuotient) :
    Function.support (cubicThetaCoreBump c)⊆
      cubicThetaQuotientMap '' cubicThetaCorePointSupport c := by
  intro q hq
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  have ht : q∈e.target := ((cubicThetaCoreBump c).support_subset_source hq).1
  let p := e.symm q
  have hp : p∈e.source := e.map_target ht
  have hqp : cubicThetaQuotientMap p=q := by
    rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
    exact e.right_inv ht
  have hv := cubicThetaCoreSeed_eq_bump c hp
  rw [hqp] at hv
  have hprof : cubicThetaCoreProfile c p.val≠0 := by
    rw [hv]
    exact_mod_cast hq
  refine ⟨p,?_,hqp⟩
  refine ⟨p.val,subset_tsupport _ hprof,?_⟩
  exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

lemma cubicThetaCoreBump_complex_bound (c q : CubicThetaQuotient) :
    ‖(cubicThetaCoreBump c q : ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cubicThetaCoreBump c).nonneg]
  exact (cubicThetaCoreBump c).le_one

def cubicThetaCoreMultiplier (c : CubicThetaQuotient) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalMultiplier
    (Complex.continuous_ofReal.comp (cubicThetaCoreBump c).continuous).aestronglyMeasurable
    (cubicThetaCoreBump_complex_bound c)

lemma cubicThetaCoreMultiplier_ae (c : CubicThetaQuotient) (u : CubicThetaGlobalL2) :
    (cubicThetaCoreMultiplier c u : CubicThetaQuotient → ℂ)=ᵐ[cubicThetaQuotientMeasure]
      fun q => (cubicThetaCoreBump c q:ℂ)*u q :=
  cubicThetaGlobalMultiplier_ae _ _ u

def cubicThetaCoreMass (c : CubicThetaQuotient) : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGlobalL2 :=
  (cubicThetaCoreMultiplier c).comp cubicThetaGlobalInclusion

lemma cubicThetaCoreMass_test_norm_sq (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreMass c (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q, (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [cubicThetaCoreMultiplier_ae c (cubicThetaGlobalMass F),
    (cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hq hF
  change ‖cubicThetaCoreMultiplier c (cubicThetaGlobalMass F) q‖^2=_
  rw [hq]
  change ‖(cubicThetaCoreBump c q:ℂ)*((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
  rw [hF,norm_mul,mul_pow,cubicThetaSectionRepresentative_norm,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cubicThetaCoreMass_sheet_integral (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreMass c (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ p in cubicThetaCorePointSupport c,
        ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F (cubicThetaPointCoordinates p)‖^2
          ∂cubicThetaPointMeasure := by
  rw [cubicThetaCoreMass_test_norm_sq]
  let S := cubicThetaCorePointSupport c
  have hzero : ∀ q, q∉cubicThetaQuotientMap '' S →
      (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2=0 := by
    intro q hq
    have hz : cubicThetaCoreBump c q=0 :=
      Function.notMem_support.mp (fun h => hq (cubicThetaCoreBump_support_image c h))
    rw [hz,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcont : Continuous (fun q => (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2) :=
    ((cubicThetaCoreBump c).continuous.pow 2).mul ((cubicThetaSectionNorm_continuous F).pow 2)
  rw [cubicThetaChart_integral (cubicThetaCoveringChart (cubicThetaQuotientLift c))
    (cubicThetaCoveringChart_coe _) (cubicThetaCorePointSupport_compact c).measurableSet
    (cubicThetaCorePointSupport_sheet c)
    (fun q => (cubicThetaCoreBump c q)^2*cubicThetaSectionNorm F q^2) hcont.stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCorePointSupport_compact c).measurableSet
  intro p hp
  have he := cubicThetaCoreSeed_eq_bump c (cubicThetaCorePointSupport_sheet c hp)
  have hi : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaPointCoordinates,cubicThetaTestLocalization,hi,norm_mul,mul_pow,he,
    cubicThetaSectionNorm_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreMassCompact
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness of the genuine global core bump multipliers. The
weighted quotient norm is controlled by the proved compact local map. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment

local instance coreMassCompact_borel_r3cd050_1 : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance coreMassCompact_borelSpace_r3cd050_1 : BorelSpace CubicThetaTangent := ⟨rfl⟩
lemma cubicThetaCoreMass_weighted_integral (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreMass c (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ y, ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F y‖^2/y.2^3 := by
  rw [cubicThetaCoreMass_sheet_integral]
  have hi := cubicThetaPointIntegral_density (cubicThetaCorePointSupport_compact c).measurableSet
    (fun y => ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F y‖^2)
  change (∫ p in cubicThetaCorePointSupport c,
    ‖cubicThetaTestLocalization (cubicThetaCoreProfile c) F (cubicThetaPointCoordinates p)‖^2
      ∂cubicThetaPointMeasure)=_ 
  rw [hi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have ht : y∉tsupport (cubicThetaTestLocalization (cubicThetaCoreProfile c) F) :=
    fun h => hy (cubicThetaCoreProfile_support_coordinates c (tsupport_mul_subset_left h))
  rw [image_eq_zero_of_notMem_tsupport ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

lemma cubicThetaCoreMass_norm_domination (c : CubicThetaQuotient) :
    ∃ C, ∀ u : cubicThetaGlobalEnergySpace,
      ‖cubicThetaCoreMass c u‖≤C*‖cubicThetaCoreLocalInclusion c u‖ := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompactDensity_bound
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
  refine ⟨Real.sqrt C,?_⟩
  apply isClosed_property cubicThetaGlobalEnergyTestLinear_dense
    (isClosed_le (cubicThetaCoreMass c).continuous.norm
      (continuous_const.mul (cubicThetaCoreLocalInclusion c).continuous.norm))
  intro F
  have h := hbound (cubicThetaTestLocalization (cubicThetaCoreProfile c) F)
    (cubicThetaTestLocalization_smooth (cubicThetaCoreProfile_contDiff c)
      (cubicThetaCoreProfile_support_positive c) F).continuous
    (cubicThetaTestLocalization_compact (cubicThetaCoreProfile_compact c) F)
    tsupport_mul_subset_left
  rw [← cubicThetaCoreMass_weighted_integral,← cubicThetaLocalValue_norm_sq
    (cubicThetaCoreProfile_contDiff c) (cubicThetaCoreProfile_compact c)
      (cubicThetaCoreProfile_support_positive c),← cubicThetaCoreLocalInclusion_test] at h
  have he : (Real.sqrt C*‖cubicThetaCoreLocalInclusion c (cubicThetaGlobalEnergyTest F)‖)^2=
      C*‖cubicThetaCoreLocalInclusion c (cubicThetaGlobalEnergyTest F)‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  exact _root_.le_of_sq_le_sq (h.trans_eq he.symm)
    (mul_nonneg (Real.sqrt_nonneg C) (_root_.norm_nonneg _))

theorem cubicThetaCoreMass_compact (c : CubicThetaQuotient) :
    IsCompactOperator (cubicThetaCoreMass c) :=
  cubicThetaCompact_of_norm_domination (cubicThetaCoreMass c) (cubicThetaCoreLocalInclusion c)
    (cubicThetaCoreLocalInclusion_compact c) (cubicThetaCoreMass_norm_domination c)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreMassFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaCoreMassFamily (A : Finset CubicThetaQuotient) :
    cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaCoreValueFamily A := by
  classical
  exact ∑ i : A, (lp.singleContinuousLinearMap ℂ (fun _ : A => CubicThetaGlobalL2) 2 i).comp
    (cubicThetaCoreMass i.val)

lemma cubicThetaCoreMassFamily_apply (A : Finset CubicThetaQuotient)
    (u : cubicThetaGlobalEnergySpace) (i : A) :
    cubicThetaCoreMassFamily A u i=cubicThetaCoreMass i.val u := by
  classical
  simp only [cubicThetaCoreMassFamily,sum_apply,ContinuousLinearMap.comp_apply]
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply,lp.singleContinuousLinearMap_apply,lp.single_apply]
  simp

theorem cubicThetaCoreMassFamily_compact (A : Finset CubicThetaQuotient) :
    IsCompactOperator (cubicThetaCoreMassFamily A) := by
  classical
  apply (compactOperator (RingHom.id ℂ) _ _).sum_mem
  intro i _
  exact (cubicThetaCoreMass_compact i.val).clm_comp
    (lp.singleContinuousLinearMap ℂ (fun _ : A => CubicThetaGlobalL2) 2 i)

lemma cubicThetaCoreMassFamily_norm_sq (A : Finset CubicThetaQuotient)
    (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCoreMassFamily A u‖^2=∑ i : A, ‖cubicThetaCoreMass i.val u‖^2 := by
  have h := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) (cubicThetaCoreMassFamily A u)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,tsum_fintype,cubicThetaCoreMassFamily_apply] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global restriction to the arithmetic compact core is
compact from the energy space to L2. The finite bump inequality gives
norm domination by the already compact family of localizations. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

def cubicThetaCoreRestriction (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGlobalL2 :=
  (cubicThetaGlobalRestriction (cubicThetaQuotientCore_compact S V).measurableSet).comp
    cubicThetaGlobalInclusion

lemma cubicThetaCoreMass_integral (c : CubicThetaQuotient) (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCoreMass c u‖^2 =
      ∫ q, (cubicThetaCoreBump c q)^2*‖cubicThetaGlobalInclusion u q‖^2
        ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [cubicThetaCoreMultiplier_ae c (cubicThetaGlobalInclusion u)] with q hq
  change ‖cubicThetaCoreMultiplier c (cubicThetaGlobalInclusion u) q‖^2=_
  rw [hq,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cubicThetaCoreMass_density_integrable (c : CubicThetaQuotient)
    (u : cubicThetaGlobalEnergySpace) :
    Integrable (fun q => (cubicThetaCoreBump c q)^2*‖cubicThetaGlobalInclusion u q‖^2)
      cubicThetaQuotientMeasure := by
  have h := (Lp.memLp (cubicThetaCoreMass c u)).integrable_norm_pow (by norm_num)
  apply h.congr
  filter_upwards [cubicThetaCoreMultiplier_ae c (cubicThetaGlobalInclusion u)] with q hq
  change ‖cubicThetaCoreMultiplier c (cubicThetaGlobalInclusion u) q‖^2=_
  rw [hq,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cubicThetaCoreRestriction_norm_sq_le (S : Finset SL(2,Eisenstein)) (V : ℝ)
    (A : Finset CubicThetaQuotient)
    (hA : ∀ q∈cubicThetaQuotientCore S V, 1≤∑ c∈A, (cubicThetaCoreBump c q)^2)
    (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCoreRestriction S V u‖^2≤∑ c∈A, ‖cubicThetaCoreMass c u‖^2 := by
  classical
  rw [cubicTheta_l2_norm_sq_measure]
  simp_rw [cubicThetaCoreMass_integral]
  rw [← integral_finsetSum A (fun c _ => cubicThetaCoreMass_density_integrable c u)]
  apply integral_mono_ae
    ((Lp.memLp (cubicThetaCoreRestriction S V u)).integrable_norm_pow (by norm_num))
    (integrable_finsetSum A (fun c _ => cubicThetaCoreMass_density_integrable c u))
  filter_upwards [cubicThetaGlobalRestriction_ae
    (cubicThetaQuotientCore_compact S V).measurableSet (cubicThetaGlobalInclusion u)] with q hq
  change ‖cubicThetaGlobalRestriction (cubicThetaQuotientCore_compact S V).measurableSet
    (cubicThetaGlobalInclusion u) q‖^2≤_
  rw [hq,← Finset.sum_mul]
  by_cases h : q∈cubicThetaQuotientCore S V
  · simp only [Set.indicator_of_mem h]
    exact le_mul_of_one_le_left (sq_nonneg _) (hA q h)
  · simp only [Set.indicator_of_notMem h,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact mul_nonneg (Finset.sum_nonneg (fun c _ => sq_nonneg _)) (sq_nonneg _)

theorem cubicThetaCoreRestriction_compact (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    IsCompactOperator (cubicThetaCoreRestriction S V) := by
  obtain ⟨A,hA⟩ := cubicThetaCoreBump_sum_sq S V
  apply cubicThetaCompact_of_norm_domination (cubicThetaCoreRestriction S V)
    (cubicThetaCoreMassFamily A) (cubicThetaCoreMassFamily_compact A)
  refine ⟨1,fun u => ?_⟩
  rw [one_mul]
  apply _root_.le_of_sq_le_sq _ (_root_.norm_nonneg _)
  rw [cubicThetaCoreMassFamily_norm_sq]
  rw [Finset.sum_coe_sort A (fun c => ‖cubicThetaCoreMass c u‖^2)]
  exact cubicThetaCoreRestriction_norm_sq_le S V A hA u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyIntegralIdentities
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed energy coordinates and compact restrictions retain
the literal mass and differential integrals on smooth sections. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCoreRestriction_test_norm_sq (S : Finset SL(2,Eisenstein)) (V : ℝ)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreRestriction S V (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q in cubicThetaQuotientCore S V, cubicThetaSectionNorm F q^2
        ∂cubicThetaQuotientMeasure := by
  let K := cubicThetaQuotientCore S V
  have hK : MeasurableSet K := (cubicThetaQuotientCore_compact S V).measurableSet
  rw [cubicTheta_l2_norm_sq_measure,← integral_indicator hK]
  apply integral_congr_ae
  filter_upwards [cubicThetaGlobalRestriction_ae hK
    (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)),
    (cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hr hq
  change ‖cubicThetaGlobalRestriction hK
    (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)) q‖^2=_
  rw [hr]
  by_cases hk : q∈K
  · rw [indicator_of_mem hk,indicator_of_mem hk]
    change ‖((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
    rw [hq,cubicThetaSectionRepresentative_norm]
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalGreen
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaLocalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instCompleteSpace_h1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive global Green operator is constructed from the actual
energy inclusion. Its resolvent is analytic off the nonnegative spectral
axis; continuation across that axis is a separate step. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

def cubicThetaGlobalGreen : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalInclusion.comp cubicThetaGlobalInclusion.adjoint

def cubicThetaGlobalResolvent (z : ℂ) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  Ring.inverse (1-z • cubicThetaGlobalGreen)*cubicThetaGlobalGreen

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactEnergyCorrection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaCompactEnergyCorrection (S R : Finset SL(2,Eisenstein)) (B : ℝ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  (cubicThetaCoreRestriction S 2).adjoint.comp (cubicThetaCoreRestriction S 2)+
    (B:ℂ) • ((cubicThetaCoreRestriction R 2).adjoint.comp (cubicThetaCoreRestriction R 2))

lemma cubicThetaCompactEnergyCorrection_compact (S R : Finset SL(2,Eisenstein)) (B : ℝ) :
    IsCompactOperator (cubicThetaCompactEnergyCorrection S R B) := by
  have hS : IsCompactOperator ((cubicThetaCoreRestriction S 2).adjoint.comp
      (cubicThetaCoreRestriction S 2)) :=
    (cubicThetaCoreRestriction_compact S 2).clm_comp (cubicThetaCoreRestriction S 2).adjoint
  have hR : IsCompactOperator ((cubicThetaCoreRestriction R 2).adjoint.comp
      (cubicThetaCoreRestriction R 2)) :=
    (cubicThetaCoreRestriction_compact R 2).clm_comp (cubicThetaCoreRestriction R 2).adjoint
  exact hS.add (hR.smul (B:ℂ))

lemma cubicThetaEnergyMass_inner (u : cubicThetaGlobalEnergySpace) :
    (inner ℂ (cubicThetaEnergyMass u) u).re=‖cubicThetaGlobalInclusion u‖^2 := by
  rw [cubicThetaEnergyMass,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExceptionalAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional projection diagonalizes the energy mass operator.
These exact identities isolate the simple pole in the local inverse. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaExceptionalProjection_idempotent (z : ℂ) :
    cubicThetaExceptionalProjection z*cubicThetaExceptionalProjection z=
      cubicThetaExceptionalProjection z :=
  (cubicThetaEnergyPencil z).ker.isIdempotentElem_starProjection

lemma cubicThetaEnergyMass_mul_projection {z : ℝ} (hz : z≠0) :
    cubicThetaEnergyMass*cubicThetaExceptionalProjection (z:ℂ)=
      ((z⁻¹:ℝ):ℂ) • cubicThetaExceptionalProjection (z:ℂ) := by
  apply ContinuousLinearMap.ext
  intro u
  have hm := (cubicThetaEnergyPencil (z:ℂ)).ker.starProjection_apply_mem u
  change cubicThetaExceptionalProjection (z:ℂ) u-
    (z:ℂ) • (cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u))=0 at hm
  have he := (sub_eq_zero.mp hm).symm
  change cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    ((z⁻¹:ℝ):ℂ) • (cubicThetaExceptionalProjection (z:ℂ) u)
  conv_rhs => rw [← he,smul_smul,← Complex.ofReal_mul,inv_mul_cancel₀ hz,Complex.ofReal_one,one_smul]

lemma cubicThetaEnergyMass_commute_projection {z : ℝ} (hz : z≠0) :
    Commute cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ)) := by
  have hA : star cubicThetaEnergyMass=cubicThetaEnergyMass :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self cubicThetaGlobalInclusion).isSelfAdjoint
  have hP : star (cubicThetaExceptionalProjection (z:ℂ))=cubicThetaExceptionalProjection (z:ℂ) :=
    isSelfAdjoint_starProjection _
  have hc : star ((z⁻¹:ℝ):ℂ)=((z⁻¹:ℝ):ℂ) := by rw [RCLike.star_def,Complex.conj_ofReal]
  have he := congrArg star (cubicThetaEnergyMass_mul_projection hz)
  have hm := ContinuousLinearMap.adjoint_comp cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ))
  change star (cubicThetaEnergyMass*cubicThetaExceptionalProjection (z:ℂ))=
    star (cubicThetaExceptionalProjection (z:ℂ))*star cubicThetaEnergyMass at hm
  have hs := (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)
    (F:=cubicThetaGlobalEnergySpace)).map_smulₛₗ ((z⁻¹:ℝ):ℂ) (cubicThetaExceptionalProjection (z:ℂ))
  change star (((z⁻¹:ℝ):ℂ) • cubicThetaExceptionalProjection (z:ℂ))=
    star ((z⁻¹:ℝ):ℂ) • star (cubicThetaExceptionalProjection (z:ℂ)) at hs
  rw [hm,hs,hP,hA,hc] at he
  exact (cubicThetaEnergyMass_mul_projection hz).trans he.symm

lemma cubicThetaEnergyPencil_mul_projection {z : ℝ} (hz : z≠0) (w : ℂ) :
    cubicThetaEnergyPencil w*cubicThetaExceptionalProjection (z:ℂ)=
      (1-w/(z:ℂ)) • cubicThetaExceptionalProjection (z:ℂ) := by
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace => A u)
    (cubicThetaEnergyMass_mul_projection hz)
  change cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    ((z⁻¹:ℝ):ℂ) • (cubicThetaExceptionalProjection (z:ℂ) u) at he
  change cubicThetaExceptionalProjection (z:ℂ) u-w •
      (cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u))=
    (1-w/(z:ℂ)) • (cubicThetaExceptionalProjection (z:ℂ) u)
  rw [he,Complex.ofReal_inv]
  simp only [div_eq_mul_inv]
  module

lemma cubicThetaEnergyPencil_commute_projection {z : ℝ} (hz : z≠0) (w : ℂ) :
    Commute (cubicThetaEnergyPencil w) (cubicThetaExceptionalProjection (z:ℂ)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace => A u)
    (cubicThetaEnergyMass_commute_projection hz).eq
  change cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    cubicThetaExceptionalProjection (z:ℂ) (cubicThetaEnergyMass u) at h
  change cubicThetaExceptionalProjection (z:ℂ) u-w •
    cubicThetaEnergyMass (cubicThetaExceptionalProjection (z:ℂ) u)=
    cubicThetaExceptionalProjection (z:ℂ) (u-w • cubicThetaEnergyMass u)
  rw [map_sub,map_smul,h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyResolvent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local candidate inverse at an exceptional real parameter is an
analytic inverse on the complementary subspace plus an explicit simple
pole on the finite exceptional space. Algebraic agreement with the
original inverse is proved separately. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaLocalEnergyResolvent (z w : ℂ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
      (1-cubicThetaExceptionalProjection z)+
    (z/(z-w)) • cubicThetaExceptionalProjection z

lemma cubicThetaEnergyPencil_analytic (z : ℂ) : AnalyticAt ℂ cubicThetaEnergyPencil z := by
  let L : ℂ →L[ℂ] (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight cubicThetaEnergyMass
  have hsm : AnalyticAt ℂ (fun w : ℂ => w • cubicThetaEnergyMass) z := by
    have he : (fun w : ℂ => L w)=(fun w : ℂ => w • cubicThetaEnergyMass) := by
      funext w
      rfl
    rw [← he]
    exact ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=ℂ)
      (F:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) L z
  exact analyticAt_const.sub hsm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyInverseContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local meromorphic formula agrees with the actual inverse on a
punctured neighborhood of each positive real parameter below two. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaLocalEnergyResolvent_eq_inverse {z : ℝ} (hz : z≠0) {w : ℂ}
    (hw : w≠(z:ℂ))
    (hu : IsUnit (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))) :
    cubicThetaLocalEnergyResolvent (z:ℂ) w=Ring.inverse (cubicThetaEnergyPencil w) := by
  have hcz : (z:ℂ)≠0 := by exact_mod_cast hz
  have hTP := cubicThetaEnergyPencil_mul_projection hz w
  have hPT : cubicThetaExceptionalProjection (z:ℂ)*cubicThetaEnergyPencil w=
      (1-w/(z:ℂ)) • cubicThetaExceptionalProjection (z:ℂ) := by
    exact (cubicThetaEnergyPencil_commute_projection hz w).eq.symm.trans hTP
  have hc : 1-w/(z:ℂ)≠0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hw ((div_eq_one_iff_eq hcz).mp he.symm)
  have hcoef : (1-w/(z:ℂ))⁻¹=(z:ℂ)/((z:ℂ)-w) := by
    have he : 1-w/(z:ℂ)=((z:ℂ)-w)/(z:ℂ) := by field_simp
    rw [he,inv_div]
  rw [cubicThetaLocalEnergyResolvent,← hcoef]
  exact (cubicThetaProjection_inverse _ _ _
    (cubicThetaExceptionalProjection_idempotent _) hTP hPT hu hc).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyRegularDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The energy inverse is analytic off the positive real spectral ray,
and meromorphic across its part strictly below the cusp threshold two. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaEnergyMass_positive : cubicThetaEnergyMass.IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self cubicThetaGlobalInclusion

lemma cubicThetaEnergyMass_norm : ‖cubicThetaEnergyMass‖≤1 := by
  rw [cubicThetaEnergyMass,ContinuousLinearMap.norm_adjoint_comp_self]
  exact (mul_le_mul cubicThetaGlobalInclusion_norm cubicThetaGlobalInclusion_norm
    cubicThetaGlobalInclusion.opNorm_nonneg zero_le_one).trans_eq (one_mul 1)

lemma cubicThetaEnergyPencil_unit {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    IsUnit (cubicThetaEnergyPencil z) :=
  cubicThetaPositiveContraction_unit cubicThetaEnergyMass cubicThetaEnergyMass_positive
    cubicThetaEnergyMass_norm hz

lemma cubicThetaEnergyInverse_analytic {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    AnalyticAt ℂ (fun w => Ring.inverse (cubicThetaEnergyPencil w)) z := by
  have hu := cubicThetaEnergyPencil_unit hz
  have hi : AnalyticAt ℂ Ring.inverse (cubicThetaEnergyPencil z) := by
    convert analyticAt_inverse (𝕜:=ℂ)
      (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hu.unit using 1
    all_goals try with_reducible_and_instances rfl
    exact hu.unit_spec
  exact hi.comp (f:=cubicThetaEnergyPencil) (x:=z) (cubicThetaEnergyPencil_analytic z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalSpectralResolvent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed global Green operator gives the actual Eisenstein
spectral resolvent initially in Re(s)>2 and at nonreal points of Re(s)>1.
Real poles in (1,2] still require meromorphic continuation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGlobalSpectralResolvent (s : ℂ) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalResolvent (cubicThetaGlobalSpectralParameter s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedResolvent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global resolvent applied to the literal incoming arithmetic
forcing. Identification with the Eisenstein remainder is a separate step. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaForcedResolvent (s : ℂ) : CubicThetaGlobalL2 :=
  cubicThetaGlobalSpectralResolvent s (cubicThetaForcingL2 s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticDistribution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continued family tested against actual compact automorphic
sections. On the initial half-plane these are the literal quotient
integrals of the arithmetic Eisenstein remainder. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticDistribution (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) (s : ℂ) : ℂ :=
  inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _) (cubicThetaForcedResolvent s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaArithmeticFourierResidue (h : Eisenstein) (σ : ℝ) : ℂ :=
  Complex.Gamma (σ:ℂ)/
    ((Real.pi:ℂ)*cubicThetaFourierRadialTest h cubicThetaRadialTestWeight σ)*
      inner ℂ (cubicThetaCuspFourierTest h cubicThetaRadialTestWeight)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy σ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaThetaObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaObservedWhittakerCoefficient (h : Eisenstein) : ℂ :=
  ((Real.pi:ℂ)/Complex.Gamma (4/3))*cubicThetaArithmeticFourierResidue h (4/3)*
    ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueNormalization
attribute [-instance] _root_.instMeasurableSpace
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

def cubicThetaResidueScale : ℂ :=
  (cubicThetaConstant:ℂ)/((Real.pi:ℂ)^2/(54*principalIdealZeta 2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaObservationScaling
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric normalization of the actual Whittaker observation
under multiplication of its arithmetic frequency. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNormalizedObservedCoefficient (h : Eisenstein) : ℂ :=
  cubicThetaResidueScale*cubicThetaObservedWhittakerCoefficient h/
    ((9*Real.sqrt 3/2:ℝ):ℂ)

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

def cubicThetaArithmeticBaseScalar : ℂ := cubicThetaNormalizedObservedCoefficient 1/81

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

def cubicThetaSeriesConstant : ℂ :=
  (cubicThetaConstant:ℂ)/cubicThetaArithmeticBaseScalar

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualCuspCoefficients
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal constant and nonconstant coefficients of the three actual
cusp types, and their conjugates on the common frequency lattice. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaActualCuspConstant (n : ℤ) : ℂ :=
  if (3:ℤ) ∣ n then cubicThetaSeriesConstant else 0

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

def cubicThetaAngularCompletion (q : Eisenstein) (k : ℕ) (s : ℂ) : ℂ :=
  (1/4:ℂ)*(cubicThetaLevelScale q:ℂ)^(-(2*s+(k:ℂ)-1))*
    ((2*Real.pi:ℝ):ℂ)^(-(2*s+(k:ℂ)))*
      Complex.Gamma (s+(k:ℂ)/2+1/6)*Complex.Gamma (s+(k:ℂ)/2-1/6)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite primary projector gives an explicit dual coefficient
family, with absolute convergence and its actual constant term. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaProjectedConstant (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) : ℂ :=
  (∑ j : Fin 3, omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
    star (cubicThetaActualCuspConstant (cubicThetaProjectedCuspType g j)))/3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero angular mode of the actual primary projection, with its
constant-to-Fourier ratio retained in the pole coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSelectedRadialAxis (g : SL(2,Eisenstein)) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis cubicThetaSelectedCoefficient 0
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaProjectedRadialAxis (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis (cubicThetaProjectedCoefficient g hc) 0
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaProjectedRadialConstant (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) : ℂ :=
  cubicThetaProjectedConstant g hc*((cubicThetaLevelScale (g 1 0)^(2/3:ℝ):ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRegularization
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit removal of the actual radial pole. The residue is retained
as the computed cusp constant; no normalization of that constant is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSelectedRadialTail (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaSelectedRadialAxis g)) (2*s-1)+
    mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc)) (-(2*s-1))

def cubicThetaSelectedRadialResidue (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 (5/6)*cubicThetaProjectedRadialConstant g hc/2

def cubicThetaSelectedRadialRegularized (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*
    ((s-5/6)*cubicThetaSelectedRadialTail g hc s+cubicThetaProjectedRadialConstant g hc/2)

@[simp] lemma cubicThetaSelectedRadialRegularized_at_pole (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    cubicThetaSelectedRadialRegularized g hc (5/6)=cubicThetaSelectedRadialResidue g hc := by
  simp only [cubicThetaSelectedRadialRegularized,sub_self,zero_mul,zero_add,
    cubicThetaSelectedRadialResidue]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialAverage
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic-character averaging of the actual radial formula. The
pole coefficient is calculated without assuming the arithmetic scalar. -/
noncomputable section
open scoped BigOperators MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaResidueRadialPole (r : Eisenstein) : ℂ :=
  cubicThetaAngularUncompletion r 0 (5/6)/2*
    ((Nat.card (Residues r)ˣ:ℂ)*(star cubicThetaSeriesConstant/3))*
      ((cubicThetaLevelScale r^(2/3:ℝ):ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRawVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial raw/completed Voronoi identities. The main term remains
in terms of the computed residue, without asserting its normalization. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaActualRawRadialMain (r : Eisenstein) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  cubicThetaResidueRadialPole r/
    (((3^(5/2:ℝ):ℝ):ℂ)*((Real.sqrt (norm r):ℂ)*gauss r))*
      mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ)

def cubicThetaActualCompletedRadialMain (r : Eisenstein) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  cubicThetaResidueRadialPole r/
    (((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm r):ℂ))*
      mellin W (5/6)*((X/27:ℝ):ℂ)^(5/6:ℂ)

end CubicFirstMoment

end

end OAI
end


