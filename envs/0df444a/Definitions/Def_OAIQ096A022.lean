-- Prove2me | Definitions.Def_OAIQ096A022
-- name    : OAIQ096A022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T04:03:40.759834+00:00
-- url     : https://prove2.me/theorems/a886e2b9-d69c-4637-acba-d0aaee96dfe9
-- title:
--   Definitions bundle OAIQ096A022 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 165 declarations of OpenAI's Lean: 25 definitions, 1 instance and 139 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaConstantContinuation`, `OAI.CubicFirstMoment.cubicThetaCuspFourierObservable`, `OAI.CubicFirstMoment.cubicThetaCuspObservable`, `OAI.CubicFirstMoment.cubicThetaFiniteMassClosure`, `OAI.CubicFirstMoment.cubicThetaForcedCusp`, `OAI.CubicFirstMoment.cubicThetaFrequencyContinuation`, `OAI.CubicFirstMoment.cubicThetaFrequencyQuotient`, `OAI.CubicFirstMoment.cubicThetaGlobalEnergyValueMap`, `OAI.CubicFirstMoment.cubicThetaInvertedWindowObservable`, `OAI.CubicFirstMoment.cubicThetaInvertedWindowTest`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeMass`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRawMass`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCuspRestriction`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFiniteCuspRestriction`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFiniteFourier`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFiniteWeyl`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootObservation`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootWeylL2`, `OAI.CubicFirstMoment.cubicThetaPrimeRootLiftL2`, `OAI.CubicFirstMoment.cubicThetaPrimeRootNormalizedRestriction`, `OAI.CubicFirstMoment.cubicThetaPrimeRootSmoothRestriction`, `OAI.CubicFirstMoment.cubicThetaRegularizedFrequency`, `OAI.CubicFirstMoment.cubicThetaRegularizedPrimaryOne`, `OAI.CubicFirstMoment.cubicThetaRegularizedRamifiedLow`, `OAI.CubicFirstMoment.cubicThetaScatteringResidue`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_PeriodicPoisson`, `CubicMoment_Estimates_PrincipalZetaContinuation`, `CubicMoment_Theta_CubicThetaArithmeticPoleIsolation`, `CubicMoment_Theta_CubicThetaArithmeticTorus`, `CubicMoment_Theta_CubicThetaConstantContinuation`, `CubicMoment_Theta_CubicThetaCuspFourierObservable`, `CubicMoment_Theta_CubicThetaCuspObservable`, `CubicMoment_Theta_CubicThetaCuspRestriction`, `CubicMoment_Theta_CubicThetaEisensteinFourierRows`, `CubicMoment_Theta_CubicThetaEisensteinTorus`, `CubicMoment_Theta_CubicThetaEnergySimplePole`, `CubicMoment_Theta_CubicThetaFiniteEnergyPairing`, `CubicMoment_Theta_CubicThetaFiniteEnergySections`, `CubicMoment_Theta_CubicThetaForcedCusp`, `CubicMoment_Theta_CubicThetaFourierCoefficients`, `CubicMoment_Theta_CubicThetaFourierNonzero`, `CubicMoment_Theta_CubicThetaFrequencyContinuation`, `CubicMoment_Theta_CubicThetaGlobalL2`, `CubicMoment_Theta_CubicThetaHighWindowPairing`, `CubicMoment_Theta_CubicThetaHorizontalAffine`, `CubicMoment_Theta_CubicThetaHorizontalCover`, `CubicMoment_Theta_CubicThetaHorizontalDilation`, `CubicMoment_Theta_CubicThetaHorizontalDomain`, `CubicMoment_Theta_CubicThetaHorizontalFourierTranslation`, `CubicMoment_Theta_CubicThetaHorizontalLattice`, `CubicMoment_Theta_CubicThetaHorizontalPeriodMean`, `CubicMoment_Theta_CubicThetaHorizontalTranslation`, `CubicMoment_Theta_CubicThetaInversionEnergyInvolution`, `CubicMoment_Theta_CubicThetaInvertedWindow`, `CubicMoment_Theta_CubicThetaLongWindowKernel`, `CubicMoment_Theta_CubicThetaPointC1Hecke`, `CubicMoment_Theta_CubicThetaPointC1Inversion`, `CubicMoment_Theta_CubicThetaPointC1Pairing`, `CubicMoment_Theta_CubicThetaPointC1Trace`, `CubicMoment_Theta_CubicThetaPointC1TraceIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkinPairing`, `CubicMoment_Theta_CubicThetaPrimeCubeBottomMean`, `CubicMoment_Theta_CubicThetaPrimeCubeBranchFourier`, `CubicMoment_Theta_CubicThetaPrimeCubeComplexIntegration`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstBranchMean`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodMean`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckePairing`, `CubicMoment_Theta_CubicThetaPrimeCubeHorizontalMean`, `CubicMoment_Theta_CubicThetaPrimeCubeMassOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeRadialPairing`, `CubicMoment_Theta_CubicThetaPrimeCubeReciprocalGeometry`, `CubicMoment_Theta_CubicThetaPrimeCubeReciprocalNormalizer`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCuspLift`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCuspObservation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCuspRestriction`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFourier`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFourierNorm`, `CubicMoment_Theta_CubicThetaPrimeCubeRootHorizontal`, `CubicMoment_Theta_CubicThetaPrimeCubeRootObservationProjection`, `CubicMoment_Theta_CubicThetaPrimeCubeRootSecondIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootStripBound`, `CubicMoment_Theta_CubicThetaPrimeCubeRootTracePairing`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylGlobal`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylMass`, `CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchMean`, `CubicMoment_Theta_CubicThetaPrimeCubeSelfAdjointSection`, `CubicMoment_Theta_CubicThetaPrimeCubeTracePairing`, `CubicMoment_Theta_CubicThetaPrimeCubeUnitMean`, `CubicMoment_Theta_CubicThetaPrimeEnergyValue`, `CubicMoment_Theta_CubicThetaPrimeRootBruhatMass`, `CubicMoment_Theta_CubicThetaPrimeRootCoverDegree`, `CubicMoment_Theta_CubicThetaPrimeRootLiftL2`, `CubicMoment_Theta_CubicThetaPrimeRootOrbitOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeRootPairingL2`, `CubicMoment_Theta_CubicThetaPrimeRootRestrictionBound`, `CubicMoment_Theta_CubicThetaPrimeRootRestrictionL2`, `CubicMoment_Theta_CubicThetaPrimeRootWeylFixed`, `CubicMoment_Theta_CubicThetaRadialMeanIntegral`, `CubicMoment_Theta_CubicThetaRadialProfilePairing`, `CubicMoment_Theta_CubicThetaRamifiedLowContinuation`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryContinuation`, `CubicMoment_Theta_CubicThetaRamifiedSeries`, `CubicMoment_Theta_CubicThetaRegularizedFourier`, `CubicMoment_Theta_CubicThetaRowFourier`, `CubicMoment_Theta_CubicThetaRowGaussian`, `CubicMoment_Theta_CubicThetaRowPoisson`, `CubicMoment_Theta_CubicThetaScatteringMeromorphic`, `CubicMoment_Theta_CubicThetaScatteringRegular`, `CubicMoment_Theta_CubicThetaScatteringResidue`, `CubicMoment_Theta_CubicThetaSectionFourierPairing`, `CubicMoment_Theta_CubicThetaSectionMean`, `CubicMoment_Theta_CubicThetaSectionMeanPairing`, `CubicMoment_Theta_CubicThetaSmoothChartWeak`, `CubicMoment_Theta_CubicThetaSmoothGlobalWeak`, `CubicMoment_Theta_CubicThetaSmoothWeakDefect`, `CubicMoment_Theta_CubicThetaTotientSeries`, `CubicMoment_Theta_CubicThetaWindowWeak`, `CubicMoment_Theta_CubicThetaZeroObservable`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A016`, `OAIQ096A017`, `OAIQ096A018` and `OAIQ096A019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A024`, `OAIQ096A025`, `OAIQ096A028`, `OAIQ096A029`, `OAIQ096A030` and `OAIQ096A031`; the statements `OAI_CubicFirstMoment_cubicThetaArithmeticBaseScalar_sign`, `OAI_CubicFirstMoment_cubicThetaFullDual_radial_voronoi`, `OAI_CubicFirstMoment_cubicThetaSelected_radial_voronoi` and `OAI_CubicFirstMoment_uniform_cubicTheta_radial_remainder_low`; the proofs of `OAI.CubicFirstMoment.ProfileControl.low_common_sum_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.low_variance_remainder_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power`, `OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power`, `OAI.CubicFirstMoment.SieveExponent.recurrence`, `OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood`, `OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood`, `OAI_CubicFirstMoment_angular_corrected_dispersion_asymptotic_actual`, `OAI_CubicFirstMoment_angular_distinguishedHighScaleRows_isLittleO_actual`, `OAI_CubicFirstMoment_angular_distinguishedStoppedDyad_early_bound_actual`, `OAI.CubicFirstMoment.angular_full_prime_centered_smoothed_bilinear_actual`, `OAI_CubicFirstMoment_angular_largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI.CubicFirstMoment.angular_large_tuple_triple_transition_smoothed`, `OAI_CubicFirstMoment_angular_logarithmic_prime_typeI_mixed_full_actual`, `OAI_CubicFirstMoment_angular_scaleFirstMiddleSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_semiprime_smoothed_log_saving_actual`, `OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic`, `OAI.CubicFirstMoment.angular_stopped_sieved_model_log_saving`, `OAI.CubicFirstMoment.angular_tailPrime_hecke_group`, `OAI.CubicFirstMoment.angular_tailPrime_hecke_window`, `OAI.CubicFirstMoment.angular_two_prime_transition_centered`, `OAI.CubicFirstMoment.bounded_rough_divisor_common_log_saving`, `OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit`, `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO`, `OAI_CubicFirstMoment_cubicTheta_radial_productTypeICutoffWindow_bound`, `OAI_CubicFirstMoment_distinguishedHighScaleRows_isLittleO_actual`, `OAI_CubicFirstMoment_distinguishedStoppedDyad_early_bound_actual`, `OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer`, `OAI.CubicFirstMoment.full_prime_product_height_bilinear`, `OAI_CubicFirstMoment_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI.CubicFirstMoment.large_common_nonzero_power`, `OAI_CubicFirstMoment_large_tuple_restricted_smoothed_actual`, `OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power`, `OAI.CubicFirstMoment.primitiveAngularHeckeInput_proved`, `OAI_CubicFirstMoment_rough_prime_corrected_bilinear_actual`, `OAI_CubicFirstMoment_scaleFirstLow_sub_stopped_isLittleO_actual`, `OAI_CubicFirstMoment_scaleFirstMiddleSum_isLittleO_actual`, `OAI.CubicFirstMoment.semiprimeGaussTail_angular_hecke_window`, `OAI.CubicFirstMoment.semiprime_gauss_height_log_saving`, `OAI_CubicFirstMoment_semiprime_piece_log_saving_actual`, `OAI.CubicFirstMoment.sieveExponent_four_thirds`, `OAI.CubicFirstMoment.sieved_full_model_asymptotic`, `OAI_CubicFirstMoment_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_stopped_product_bilinear_log_saving_actual`, `OAI.CubicFirstMoment.stopped_sieved_model_log_saving`, `OAI.CubicFirstMoment.two_prime_transition_centered`, `OAI.CubicFirstMoment.two_prime_transition_height`, `OAI_CubicFirstMoment_typeI_product_low_integral_actual` and `OAI_CubicFirstMoment_uniform_cubicTheta_radial_remainder_low`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A017
import Definitions.Def_OAIQ096A018
import Definitions.Def_OAIQ096A019

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem poisson_eisenstein_periodic (c : Eisenstein) (hc : c ≠ 0)
    (ψ : Residues c → ℂ) (f : 𝓢(ℂ, ℂ)) :
    ∑' a : Eisenstein, ψ (Ideal.Quotient.mk (modulus c) a) * f (a : ℂ) =
      (2 / (Real.sqrt 3 * norm c) : ℝ) • ∑' h : Eisenstein,
        (∑' v : Residues c, ψ v *
          (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
            ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ)) *
        traceFourier f ((h : ℂ) / ((c : ℂ) * traceLambda)) := by
  classical
  let : Finite (Residues c) := finite_residues hc
  let : Fintype (Residues c) := Fintype.ofFinite _
  have hc' : (c : ℂ) ≠ 0 := fun h => hc (Subtype.ext h)
  let e := Equiv.ofBijective (residueCosetMap c) (residueCosetMap_bijective hc)
  let F (v : Residues c) (a : Eisenstein) :=
    ψ v * f ((residueRepresentative c v : ℂ) + (c : ℂ) * (a : ℂ))
  have hreindex : (fun x : Residues c × Eisenstein =>
      ψ (Ideal.Quotient.mk (modulus c) (e x)) * f (e x : ℂ)) = Function.uncurry F := by
    funext x
    change ψ (Ideal.Quotient.mk (modulus c) (residueCosetMap c x)) * _ = _
    rw [residueCosetMap_mk]
    rfl
  have hs : Summable (Function.uncurry F) := by
    rw [← hreindex]
    exact e.summable_iff.mpr (periodic_schwartz_summable c hc ψ f)
  calc
    _ = ∑' x : Residues c × Eisenstein, Function.uncurry F x := by
      rw [← hreindex]
      exact (e.tsum_eq _).symm
    _ = ∑ v : Residues c, ψ v * ∑' a : Eisenstein,
        f ((residueRepresentative c v : ℂ) + (c : ℂ) * (a : ℂ)) := by
      rw [hs.tsum_prod]
      simp only [tsum_fintype, F, Function.uncurry, tsum_mul_left]
    _ = _ := by
      simp_rw [poisson_eisenstein_coset f (c : ℂ) hc']
      let K : ℝ := 2 / (Real.sqrt 3 * norm c)
      change (∑ v : Residues c, ψ v * (K • ∑' h : Eisenstein,
        (Real.fourierChar (tracePair (residueRepresentative c v : ℂ)
          ((h : ℂ) / ((c : ℂ) * traceLambda))) : ℂ) *
        traceFourier f ((h : ℂ) / ((c : ℂ) * traceLambda)))) = _
      simp_rw [mul_smul_comm, ← tsum_mul_left]
      rw [← Finset.smul_sum]
      congr 1
      rw [← Summable.tsum_finsetSum]
      · apply tsum_congr
        intro h
        simp only [tsum_fintype, Finset.sum_mul, mul_assoc]
      · intro v _
        exact (traceFourier_phase_summable f ((c : ℂ) * traceLambda)
          (mul_ne_zero hc' traceLambda_ne_zero) (residueRepresentative c v : ℂ)).mul_left (ψ v)

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma principalIdealFEPair_right {s : ℂ} (hs : 1 < s.re) :
    principalIdealFEPair.Λ s=(residueHeckeScale 1:ℂ)^s*Complex.Gamma s*
      normDirichletSeries (fun _ => 1) idealExponentNorm s := by
  have he := (principalIdealFEPair.hasMellin hs).2
  change mellin (fun t => principalThetaConstant+
    idealTheta (residueHeckeScale 1) (fun _ => 1) t-principalThetaConstant) s = _ at he
  simp only [add_sub_cancel_left] at he
  rw [←he]
  exact idealTheta_mellin (residueHeckeScale_pos (q := 1) one_ne_zero) _ (by simp) hs

lemma principalIdealZeta_right {s : ℂ} (hs : 1 < s.re) :
    principalIdealZeta s=normDirichletSeries (fun _ => 1) idealExponentNorm s := by
  rw [principalIdealZeta,thetaHeckeL,principalIdealFEPair_right hs]
  have hA : (residueHeckeScale 1:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (residueHeckeScale_pos (q := 1) one_ne_zero).ne'
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  rw [Complex.cpow_neg]
  have hp : (residueHeckeScale 1:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowGaussian
attribute [-instance] _root_.instMeasurableSpace
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

theorem cubicThetaShiftedGaussian_fourier (c z : ℂ) (hc : c ≠ 0)
    (t : ℝ) (ht : 0 < t) (w : ℂ) :
    traceFourier (cubicThetaShiftedGaussian c z hc t ht) w =
      (Complex.normSq c:ℂ)*(Real.fourierChar (tracePair z (w*c)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp (-4*Real.pi^2/t*Complex.normSq (w*c)):ℝ)) := by
  have he : (cubicThetaShiftedGaussian c z hc t ht : ℂ → ℂ) =
      fun x => (fun u => radialGaussianSchwartz t ht (z+u)) (c⁻¹*x) := by
    funext x
    change radialGaussianSchwartz t ht (c⁻¹*x- -z) = _
    congr 1
    ring
  rw [he, traceFourier_complexMul c⁻¹ (inv_ne_zero hc)
    (fun u => radialGaussianSchwartz t ht (z+u)) w, Complex.normSq_inv, inv_inv,
    div_inv_eq_mul, traceFourier_translation, radialGaussianSchwartz_traceFourier]
  simp only [Complex.real_smul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaEisensteinGaussianRow_poisson {c : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c ≠ 0) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    cubicThetaEisensteinGaussianRow c z t =
      (2/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaEisensteinGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
  have hcC : (c:ℂ) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hq : (3*c:Eisenstein) ≠ 0 := mul_ne_zero (by norm_num) hc0
  have hp := poisson_eisenstein_periodic (3*c) hq (cubicThetaEisensteinResidueWeight c)
    (cubicThetaShiftedGaussian c z hcC t ht)
  have hleft : (∑' d : Eisenstein,
      cubicThetaEisensteinResidueWeight c (Ideal.Quotient.mk (modulus (3*c)) d)*
        cubicThetaShiftedGaussian c z hcC t ht (d:ℂ)) =
      cubicThetaEisensteinGaussianRow c z t := by
    apply tsum_congr
    intro d
    rw [cubicThetaEisensteinResidueWeight_mk hc, cubicThetaShiftedGaussian_apply]
  rw [hleft] at hp
  have hfreq (h : Eisenstein) : ((h:ℂ)/((3*c:Eisenstein)*traceLambda))*(c:ℂ) =
      (h:ℂ)/(3*traceLambda) := by
    change ((h:ℂ)/(((3:ℂ)*(c:ℂ))*traceLambda))*(c:ℂ) = _
    field_simp
  simp_rw [cubicThetaShiftedGaussian_fourier, hfreq] at hp
  change cubicThetaEisensteinGaussianRow c z t =
    (2/(Real.sqrt 3*norm (3*c)):ℝ) •
      ∑' h : Eisenstein, cubicThetaEisensteinGaussCoefficient c h*
        ((Complex.normSq (c:ℂ):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ))) at hp
  rw [hp]
  change ((2/(Real.sqrt 3*norm (3*c)):ℝ):ℂ)*_ = _
  have hf : (∑' h : Eisenstein, cubicThetaEisensteinGaussCoefficient c h*
        ((Complex.normSq (c:ℂ):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)))) =
      (norm c:ℂ)*∑' h : Eisenstein,
        cubicThetaEisensteinGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    change _ = (Complex.normSq (c:ℂ):ℂ)*_
    ring
  rw [hf, ← mul_assoc]
  congr 1
  have hn : norm c ≠ 0 := ne_of_gt (norm_pos_of_ne_zero hc0)
  have hNc : norm (3*c) = 9*norm c := by
    change Complex.normSq (((3:Eisenstein)*c):ℂ) = _
    change Complex.normSq ((3:ℂ)*(c:ℂ)) = _
    rw [map_mul]
    norm_num
    rfl
  rw [hNc]
  push_cast
  have hnC : (norm c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientSeries
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

theorem cubicThetaTotientSeries_zeta_quotient {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries cubicThetaIdealDensity idealExponentNorm s=
      principalIdealZeta s/principalIdealZeta (s+1) := by
  have hsp : 1<(s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hmu := idealDirichlet_moebius_mul (fun _ => (1:ℂ)) (by simp) rfl (by simp) hsp
  have hn := idealDirichlet_ne_zero (fun _ => (1:ℂ)) (by simp) rfl (by simp) hsp
  rw [cubicThetaTotientSeries_product hs,principalIdealZeta_right hs,
    principalIdealZeta_right hsp]
  apply (eq_div_iff hn).mpr
  have hmu' : normDirichletSeries
      (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)) idealExponentNorm (s+1)*
        normDirichletSeries (fun _ => (1:ℂ)) idealExponentNorm (s+1)=1 := by
    simpa only [mul_one] using hmu
  calc
    _ = normDirichletSeries (fun _ => (1:ℂ)) idealExponentNorm s *
        (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ))
          idealExponentNorm (s+1)*normDirichletSeries (fun _ => (1:ℂ)) idealExponentNorm (s+1)) := by ring
    _ = _ := by rw [hmu',mul_one]

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

theorem cubicThetaRamifiedDensitySeries_eq {s : ℂ} (hs : 1 < s.re) :
    cubicThetaRamifiedDensitySeries s=
      ((2/3:ℂ)*(3:ℂ)^(-s)/(1-(3:ℂ)^(-(s+1))))*
        (principalIdealZeta s/principalIdealZeta (s+1)) := by
  have he := cubicThetaPrimeDensity_series_equation cubicThetaRamifiedPrime hs
  rw [cubicThetaRamifiedPrime_norm] at he
  change cubicThetaRamifiedDensitySeries s=(3:ℂ)^(-s)*
    ((1-(3:ℂ)⁻¹)*normDirichletSeries cubicThetaIdealDensity idealExponentNorm s+
      (3:ℂ)⁻¹*cubicThetaRamifiedDensitySeries s) at he
  have hshift : (3:ℂ)^(-(s+1))=(3:ℂ)^(-s)/3 := by
    rw [show -(s+1)=-s+(-1) by ring,Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0),
      Complex.cpow_neg_one,div_eq_mul_inv]
  have hb : cubicThetaRamifiedDensitySeries s*(1-(3:ℂ)^(-(s+1)))=
      (2/3:ℂ)*(3:ℂ)^(-s)*normDirichletSeries cubicThetaIdealDensity idealExponentNorm s := by
    rw [hshift]
    linear_combination he
  calc
    _ = ((2/3:ℂ)*(3:ℂ)^(-s)*
        normDirichletSeries cubicThetaIdealDensity idealExponentNorm s)/
        (1-(3:ℂ)^(-(s+1))) := (eq_div_iff (cubicTheta_ramified_denominator_ne_zero hs)).mpr hb
    _ = _ := by rw [cubicThetaTotientSeries_zeta_quotient hs]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantContinuation
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

def cubicThetaConstantContinuation (s : ℂ) : ℂ :=
  (2*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(2-3*s)))*
    principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2)

theorem cubicThetaConstantContinuation_right {s : ℂ} (hs : 4/3 < s.re) :
    cubicThetaConstantDirichlet s=cubicThetaConstantContinuation s := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  rw [cubicThetaConstantDirichlet_eq_ramified hs,cubicThetaRamifiedDensitySeries_eq ht]
  rw [show -(3*s-3)=3-3*s by ring,show (3*s-3)+1=3*s-2 by ring,
    show -(3*s-2)=2-3*s by ring]
  unfold cubicThetaConstantContinuation
  ring

lemma cubicTheta_principalZeta_analyticAt {s : ℂ} (hs0 : s≠0) (hs1 : s≠1) :
    AnalyticAt ℂ principalIdealZeta s := by
  change AnalyticAt ℂ (fun z => principalZetaPrefactor z*
    (principalIdealFEPair.Λ₀ z-(1/z)*principalThetaConstant-
      (1/(1-z))*principalThetaConstant)) s
  apply (principalZetaPrefactor_differentiable.analyticAt s).mul
  apply AnalyticAt.sub
  · exact (principalIdealFEPair.differentiable_Λ₀.analyticAt s).sub
      ((analyticAt_const.div analyticAt_id hs0).mul analyticAt_const)
  · exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr hs1.symm)).mul analyticAt_const

lemma cubicTheta_principalZeta_two_ne_zero : principalIdealZeta 2≠0 := by
  rw [principalIdealZeta_right (by norm_num : 1<(2:ℂ).re)]
  exact idealDirichlet_ne_zero (fun _ => (1:ℂ)) (by simp) rfl (by simp) (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaEisensteinRow_heat_poisson {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) (z : ℂ) (v : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*cubicThetaEisensteinGaussianRow c z t =
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaRowFourierCoefficient c z h*cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t := by
  rw [cubicThetaEisensteinGaussianRow_poisson hc hc0 z ht]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro h
  unfold cubicThetaRowFourierCoefficient
  have he := cubicThetaRowHeat_factor ht v s h
  change (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
    ((2/(9*Real.sqrt 3):ℂ)*(cubicThetaEisensteinGaussCoefficient c h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp
          (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ)))) = _
  calc
    _ = (2/(9*Real.sqrt 3):ℂ)*cubicThetaRowFourierCoefficient c z h*
        ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
          ((Real.pi/t:ℝ)*(Real.exp
            (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ))) := by
      unfold cubicThetaRowFourierCoefficient
      ring
    _ = _ := by rw [he]; unfold cubicThetaRowFourierCoefficient; ring

theorem cubicThetaEisensteinRow_fourier {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisensteinRow c p s =
      ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hs1 : 1 < s.re := by linarith
  have hFi (h : Eisenstein) : IntegrableOn (fun t =>
      cubicThetaRowFourierCoefficient c p.1 h*
        cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) (Ioi 0) := by
    apply (cubicThetaDualHeat_integrable hp hs1 _).const_mul
    by_cases hh : h = 0
    · simp [hh]
    · exact (cubicThetaRowHeatScale_pos hh).le
  have hsum := cubicThetaWeightedDualHeat_mass_summable hp hs1 hc0 p.1
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  rw [cubicThetaEisensteinRow_mellin hc hc0 hp hs]
  calc
    _ = ((p.2/norm c:ℝ):ℂ)^s*((2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∫ t in Ioi (0:ℝ), ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
          cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
      congr 1
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => cubicThetaEisensteinRow_heat_poisson hc hc0 p.1 p.2 s ht)
    _ = _ := by
      rw [← hi]
      simp only [integral_const_mul, mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinFourierRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaEisenstein_fourier_rows {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein p s = Complex.Gamma s*(p.2:ℂ)^s+
      ∑' c : Eisenstein, if (3:Eisenstein) ∣ c ∧ c ≠ 0 then
        ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
          ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
            (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
      else 0 := by
  have hrow : Summable (fun c : Eisenstein => cubicThetaEisensteinRow c p s) :=
    (cubicThetaEisensteinGrid_summable hp hs).prod
  have he : cubicThetaEisenstein p s = ∑' c : Eisenstein, cubicThetaEisensteinRow c p s := by
    rw [cubicThetaEisenstein_eq_grid, (cubicThetaEisensteinGrid_summable hp hs).tsum_prod]
    rfl
  rw [he, hrow.tsum_eq_add_tsum_ite 0, cubicThetaEisensteinRow_zero, mul_add, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro c
  by_cases hc0 : c = 0
  · simp [hc0]
  · by_cases hc : (3:Eisenstein) ∣ c
    · simpa [hc0,hc] using cubicThetaEisensteinRow_fourier hc hc0 hp hs
    · simp [hc0,hc,cubicThetaEisensteinRow_nondivisible hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier expansion with each arithmetic Dirichlet coefficient
collected, justified by absolute convergence of the full double sum. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_fourier_coefficients {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein p s=Complex.Gamma s*(p.2:ℂ)^s+
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s*
        ∑' h : Eisenstein, cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let F (c h : Eisenstein) := cubicThetaFrequencyTerm s h c*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
  have hF : Summable (fun ch : Eisenstein × Eisenstein => F ch.1 ch.2) :=
    (cubicThetaFrequency_heat_norm_summable hp hs).of_norm
  have hswap : (∑' c,∑' h, F c h)=(∑' h,∑' c, F c h) := hF.tsum_comm.symm
  calc
    _ = Complex.Gamma s*(p.2:ℂ)^s+
        ∑' c : Eisenstein, if (3:Eisenstein)∣c ∧ c≠0 then
          ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
            ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
              (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
        else 0 := cubicThetaEisenstein_fourier_rows hp hs
    _ = Complex.Gamma s*(p.2:ℂ)^s+
        ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' c,∑' h, F c h) := by
      congr 1
      rw [←tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : (3:Eisenstein)∣c ∧ c≠0
      · rw [ite_eq_left hc,cubicTheta_row_power hp hc.2,←tsum_mul_left,←tsum_mul_left]
        apply tsum_congr
        intro h
        simp only [F,cubicThetaFrequencyTerm,ite_eq_left hc,cubicThetaRowFourierCoefficient]
        ring
      · simp [F,cubicThetaFrequencyTerm,hc]
    _ = Complex.Gamma s*(p.2:ℂ)^s+
        ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' h,∑' c, F c h) := by
      rw [hswap]
    _ = _ := by
      congr 2
      apply tsum_congr
      intro h
      dsimp only [F]
      rw [tsum_mul_right,tsum_mul_right]
      rfl

theorem cubicThetaEisenstein_fourier_normalized {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein p s=(p.2:ℂ)^s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  apply (mul_left_cancel₀ hG)
  rw [cubicThetaEisenstein_fourier_coefficients hp hs,mul_add]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaEisenstein_nonzero_coefficients {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein p s=cubicThetaEisensteinConstantMode p.2 s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, if h=0 then 0 else cubicThetaFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  rw [cubicThetaEisenstein_fourier_normalized hp hs,
    (cubicThetaFourierCoefficients_summable hp hs).tsum_eq_add_tsum_ite 0,
    cubicThetaFrequencyDirichlet_zero,cubicThetaRowHeatScale_zero]
  have hphase : (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency 0)):ℂ)=1 := by
    simp [cubicThetaRowFrequency,tracePair]
  rw [hphase,mul_one,mul_add,cubicTheta_zero_mode_archimedean hp (show 1 < s.re by linarith),
    cubicThetaEisensteinConstantMode_eq hp (show 1 < s.re by linarith)]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaEisenstein_torus {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaEisenstein (cubicThetaPeriodCell x,v) s=
      cubicThetaEisensteinConstantMode v s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaTorusRemainder v s (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaTorusRemainder_real hv hs]
  exact cubicThetaEisenstein_nonzero_coefficients hv hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
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

instance cubicThetaAutomorphicL2_complete : CompleteSpace cubicThetaAutomorphicL2 :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaArithmeticTorus_real {v : ℝ} (hv : 2≤v) {s : ℂ} (hs : 2 < s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaArithmeticRemainder (cubicThetaPeriodCell x,v) s=
      cubicThetaArithmeticTorus v s (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaArithmeticRemainder,
    cubicThetaIncomingEisenstein_high (by linarith : 1<v),cubicThetaCuspCutoff_one hv,
    one_mul,cubicThetaEisenstein_torus (by linarith) hs]
  simp only [cubicThetaArithmeticTorus,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    cubicThetaTorusFourier_zero,ContinuousMap.one_apply,smul_eq_mul,mul_one]
  ring

attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticTorusMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticTorusProbability
lemma cubicThetaArithmetic_horizontal_coefficient {v : ℝ} (hv : 2≤v)
    {s : ℂ} (hs : 2 < s.re) {h : Eisenstein} (hh : h≠0) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        cubicThetaArithmeticRemainder (z,v) s)=
      (9*Real.sqrt 3/2:ℝ) •
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
          cubicThetaNonzeroFrequencyTerm (0,v) s h) := by
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaArithmeticRemainder (z,v) s)
    (cubicThetaArithmeticTorus v s) h (cubicThetaArithmeticTorus_real hv hs),
    cubicThetaArithmeticTorus_coefficient (by linarith) hs hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergySections
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

lemma cubicThetaFiniteEnergyEmbedding_value (F : cubicThetaFiniteEnergySections) :
    cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F)=cubicThetaFiniteEnergyValue F := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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
lemma cubicThetaFiniteCuspRestriction_energy_bound :
    ∃ C, ∀ F : cubicThetaFiniteEnergySections,
      ‖cubicThetaFiniteCuspRestriction F‖≤C*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  refine ⟨1,fun F => ?_⟩
  simpa only [one_mul] using (cubicThetaFiniteCuspRestriction_bound F).trans
    (cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergySimplePole
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

lemma cubicThetaLocalEnergyResolvent_scaled {z w : ℂ} (hw : w≠z) :
    (w-z) • cubicThetaLocalEnergyResolvent z w=
      (w-z) • (Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
        (1-cubicThetaExceptionalProjection z))+(-z) • cubicThetaExceptionalProjection z := by
  apply ContinuousLinearMap.ext
  intro u
  change (w-z) • ((Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
    (1-cubicThetaExceptionalProjection z)) u+(z/(z-w)) • cubicThetaExceptionalProjection z u)=
    (w-z) • ((Ring.inverse (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection z)*
    (1-cubicThetaExceptionalProjection z)) u)+(-z) • cubicThetaExceptionalProjection z u
  exact scale_pole hw _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

def cubicThetaForcedCusp (s : ℂ) : CubicThetaStripL2 :=
  cubicThetaCuspRestriction (cubicThetaContinuedEnergyLift
    (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
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

def cubicThetaCuspObservable (T : CubicThetaStripL2) (s : ℂ) : ℂ :=
  inner ℂ T (cubicThetaForcedCusp s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

def cubicThetaCuspFourierObservable (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  cubicThetaCuspObservable (cubicThetaCuspFourierTest h W) s

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

def cubicThetaFrequencyQuotient (h : Eisenstein) (s : ℂ) : ℂ :=
  Complex.Gamma s*cubicThetaCuspFourierObservable h cubicThetaRadialTestWeight s/
    ((Real.pi:ℂ)*cubicThetaFourierRadialTest h cubicThetaRadialTestWeight s)

def cubicThetaFrequencyContinuation (h : Eisenstein) (s : ℂ) : ℂ :=
  if 3 < s.re then cubicThetaFrequencyDirichlet h s else cubicThetaFrequencyQuotient h s

theorem cubicThetaFrequencyContinuation_right (h : Eisenstein) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaFrequencyContinuation h s=cubicThetaFrequencyDirichlet h s :=
  ite_eq_left hs

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

attribute [local instance] OAI.CubicFirstMoment.cubicThetaZeroObservableMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaZeroObservableProbability
lemma cubicThetaArithmetic_horizontal_zero {v : ℝ} (hv : 2≤v)
    {s : ℂ} (hs : 2 < s.re) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency 0)):ℂ)*
        cubicThetaArithmeticRemainder (z,v) s)=
      (9*Real.sqrt 3/2:ℝ) • (cubicThetaEisensteinConstantMode v s-(v:ℂ)^s) := by
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaArithmeticRemainder (z,v) s)
    (cubicThetaArithmeticTorus v s) 0 (cubicThetaArithmeticTorus_real hv hs),
    cubicThetaArithmeticTorus_zero (by linarith) hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScatteringMeromorphic
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit scattering coefficient and actual constant observation
agree meromorphically, without assuming nonvanishing of a zeta factor. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicTheta_principalZeta_meromorphic (s : ℂ) : MeromorphicAt principalIdealZeta s := by
  change MeromorphicAt (fun z => principalZetaPrefactor z*
    (principalIdealFEPair.Λ₀ z-(1/z)*principalThetaConstant-
      (1/(1-z))*principalThetaConstant)) s
  exact (principalZetaPrefactor_differentiable.analyticAt s).meromorphicAt.mul
    (((principalIdealFEPair.differentiable_Λ₀.analyticAt s).meromorphicAt.sub
      (((MeromorphicAt.const 1 s).div analyticAt_id.meromorphicAt).mul
        (MeromorphicAt.const principalThetaConstant s))).sub
      (((MeromorphicAt.const 1 s).div (analyticAt_const.sub analyticAt_id).meromorphicAt).mul
        (MeromorphicAt.const principalThetaConstant s)))

lemma cubicThetaZetaAffine_meromorphic (b s : ℂ) :
    MeromorphicAt (fun z : ℂ => principalIdealZeta (3*z-b)) s := by
  have ha : AnalyticAt ℂ (fun z : ℂ => 3*z-b) s := by fun_prop
  exact (cubicTheta_principalZeta_meromorphic (3*s-b)).comp_analyticAt
    (f:=principalIdealZeta) (g:=fun z : ℂ => 3*z-b) ha

theorem cubicThetaConstantContinuation_meromorphic (s : ℂ) :
    MeromorphicAt cubicThetaConstantContinuation s := by
  have hp : MeromorphicAt (fun z : ℂ => 2*(3:ℂ)^(3-3*z)) s :=
    (MeromorphicAt.const 2 s).mul (cubicThetaRamifiedPower_analytic 3 s).meromorphicAt
  have hq : MeromorphicAt (fun z : ℂ => 1-(3:ℂ)^(2-3*z)) s :=
    (analyticAt_const.sub (cubicThetaRamifiedPower_analytic 2 s)).meromorphicAt
  change MeromorphicAt (fun z => (2*(3:ℂ)^(3-3*z)/(1-(3:ℂ)^(2-3*z)))*
    principalIdealZeta (3*z-3)/principalIdealZeta (3*z-2)) s
  exact ((hp.div hq).mul (cubicThetaZetaAffine_meromorphic 3 s)).div
    (cubicThetaZetaAffine_meromorphic 2 s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScatteringRegular
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In Re(s)>1 the explicit scattering coefficient has no possible pole
except s=4/3. The denominator is controlled by its convergent Euler product. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_principalZeta_right_ne_zero {s : ℂ} (hs : 1 < s.re) :
    principalIdealZeta s≠0 := by
  rw [principalIdealZeta_right hs]
  exact idealDirichlet_ne_zero (fun _ => (1:ℂ)) (by simp) rfl (by simp) hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaHighWindowPairing_section (s : ℂ) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    inner ℂ (cubicThetaHighWindowL2 s) (hF.toLp _)=
      ∫ p in cubicThetaCuspStrip 2,
        inner ℂ (cubicThetaHighWindowForcing s p.val.2) (F.val p) ∂cubicThetaPointMeasure := by
  rw [cubicThetaHighWindowL2,cubicThetaSectionPairing_L2]
  have he : (∫ q, cubicThetaSectionPairing (cubicThetaHighWindowSection s) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ q in cubicThetaQuotientMap '' cubicThetaCuspStrip 2,
        cubicThetaSectionPairing (cubicThetaHighWindowSection s) F q
          ∂cubicThetaQuotientMeasure := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hz := cubicThetaHighWindowSeries_off_cusp s (cubicThetaQuotientLift q)
      (by rwa [cubicThetaQuotientLift_map])
    change inner ℂ (cubicThetaHighWindowSeries (cubicThetaQuotientLift q).val s) _=0
    rw [hz,inner_zero_left]
  rw [he,cubicThetaInjective_complex_integral (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) _
    (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  dsimp only
  rw [cubicThetaSectionPairing_apply]
  change inner ℂ (cubicThetaHighWindowSeries p.val s) _=_
  rw [cubicThetaHighWindowSeries_high (by have h:=hp.1; change 2<p.val.2 at h; linarith) s]

lemma cubicThetaHighWindowPairing_finiteEnergy (s : ℂ) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaHighWindowL2 s) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight s))
        (cubicThetaFiniteCuspRestriction F) := by
  change inner ℂ (cubicThetaHighWindowL2 s) (F.property.2.1.toLp _)=_
  rw [cubicThetaHighWindowPairing_section s F F.property.2.1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 (cubicThetaHighWindowWeight s)).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change _=inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 (cubicThetaHighWindowWeight s)).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)
  rw [hW,hF]
  simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair,cubicThetaHighWindowWeight]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothChartWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact local Green identity descends through an injective
arithmetic chart with the actual hyperbolic measure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSmooth_chart_weak (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (lam : ℂ) (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaC1Pairing P G q ∂cubicThetaQuotientMeasure)+
      lam*(∫ q, cubicThetaSectionPairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ q, cubicThetaSectionPairing P J q ∂cubicThetaQuotientMeasure := by
  intro P
  rw [cubicThetaCoordinateSection_gradient_pairing hg hc hK hp hgs e he hKe _
    (G.property.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe,
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe]
  have hG : (∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
      (cubicThetaSectionFunction G) y)=
      ∫ y, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
        (cubicThetaSectionFunction G) y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [cubicThetaCoordinatePairing_zero_left (fun h => hy (hgs h)),mul_zero])
  have hM (F : CubicThetaSection) :
      (∫ y in K, star (g y)*cubicThetaSectionFunction F y/(y.2:ℂ)^3)=
        ∫ y, star (g y)*cubicThetaSectionFunction F y/(y.2:ℂ)^3 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgs h)),star_zero,zero_mul,zero_div])
  rw [hG,hM,hM]
  exact cubicThetaSmooth_local_weak G J lam hEq g hg hc (hgs.trans hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothWeakDefect
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous weak defect for an actual smooth section and its
compact forcing. This will pass the coordinate equation to the energy closure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSmoothWeakDefect_C1 (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaC1EnergyData F hF hc)=
      (∫ q, cubicThetaC1Pairing F G q ∂cubicThetaQuotientMeasure)+
      lam*(∫ q, cubicThetaSectionPairing F G q ∂cubicThetaQuotientMeasure)-
      ∫ q, cubicThetaSectionPairing F J q ∂cubicThetaQuotientMeasure := by
  change inner ℂ ((cubicThetaC1Gradient_memLp F hF hc).toLp _)
      ((cubicThetaGradientRepresentative_memLp G).toLp _)+
    lam*inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaSectionRepresentative_memLp G).toLp _)-
    inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaCompactSection_memLp J hJ).toLp _)=_
  rw [cubicThetaC1Pairing_L2 F G hF (G.property.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    cubicThetaSectionPairing_L2,cubicThetaSectionPairing_L2]

lemma cubicThetaSmoothWeakDefect_coordinate (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaCoordinateData hg hc (hgs.trans hp))=0 := by
  rw [cubicThetaCoordinateData,cubicThetaSmoothWeakDefect_C1]
  exact sub_eq_zero.mpr (cubicThetaSmooth_chart_weak G J lam hEq hg hc hK hp hgs e he hKe)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothGlobalWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite compact chart reconstruction and energy completion turn the
actual smooth pointwise equation into the global weak equation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaSmoothWeakDefect_compact (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaC1EnergyData F hF hc)=0 := by
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
  have hzP (c : CubicThetaQuotient) :
      cubicThetaSmoothWeakDefect G J hJ lam (cubicThetaC1EnergyData (P c) (hP c) (hcP c))=0 := by
    apply cubicThetaSmoothWeakDefect_coordinate G J hJ lam hEq
      (cubicThetaC1CoreFunction_regular c H hH) (cubicThetaC1CoreFunction_compact c H)
      (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
      (cubicThetaC1CoreFunction_support c H)
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    rintro p ⟨y,hy,rfl⟩
    exact (cubicThetaCoreProfile_support_target c hy).2
  have hsum : (∑ c∈A, P c)=F := by
    calc
      _ = ∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H := by
        apply Finset.sum_congr rfl
        intro c hcA
        exact cubicThetaC1CoreFunction_periodization c H hH
      _ = F := cubicThetaCoreDivision_reconstruction A F hn
  have he : cubicThetaC1EnergyData F hF hc=
      ∑ c∈A, cubicThetaC1EnergyData (P c) (hP c) (hcP c) := by
    rw [← cubicThetaC1EnergyData_sum A P hP hcP]
    congr 1
    exact hsum.symm
  rw [he,map_sum]
  exact Finset.sum_eq_zero (fun c _ => hzP c)

lemma cubicThetaSmoothWeakDefect_energy (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (v : cubicThetaGlobalEnergySpace) :
    cubicThetaSmoothWeakDefect G J hJ lam (v:CubicThetaGlobalEnergyAmbient)=0 := by
  have hc : IsClosed {u : CubicThetaGlobalEnergyAmbient | cubicThetaSmoothWeakDefect G J hJ lam u=0} :=
    isClosed_eq (cubicThetaSmoothWeakDefect_continuous G J hJ lam) continuous_const
  have hr : (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient)⊆
      {u | cubicThetaSmoothWeakDefect G J hJ lam u=0} := by
    rintro u ⟨F,rfl⟩
    rw [← cubicThetaC1EnergyData_smooth F]
    exact cubicThetaSmoothWeakDefect_compact G J hJ lam hEq F (F.property.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) F.property.2
  have hv : (v:CubicThetaGlobalEnergyAmbient)∈
      closure (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient) := v.property
  exact closure_minimal hr hc hv

theorem cubicThetaSmooth_global_weak (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ)
    (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalGradient G)+
      lam*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalMass G)=
      inner ℂ (cubicThetaGlobalInclusion v) ((cubicThetaCompactSection_memLp J hJ).toLp _) := by
  exact sub_eq_zero.mp (cubicThetaSmoothWeakDefect_energy G J hJ lam hEq v)

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

theorem cubicThetaWindow_global_weak (s : ℂ) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalGradient (cubicThetaIncomingWindowTest s))+
    s*(s-2)*inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalMass (cubicThetaIncomingWindowTest s))=
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaHighWindowL2 s-cubicThetaForcingL2 s) := by
  have h := cubicThetaSmooth_global_weak (cubicThetaIncomingWindowTest s)
    (cubicThetaWindowForcingSection s) (cubicThetaWindowForcingSection_compact s)
    (s*(s-2)) (cubicThetaWindow_coordinate_equation s) v
  rwa [cubicThetaWindowForcingL2] at h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticPoleIsolation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

lemma cubicThetaForcedEnergy_analytic_regular {s : ℂ} (hs : 1 < s.re)
    (h : s.im≠0 ∨ 2 < s.re) :
    AnalyticAt ℂ (fun z => cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter z) (cubicThetaForcingL2 z)) s := by
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  have hA := (cubicThetaEnergyInverse_analytic
    (cubicThetaGlobalSpectralParameter_regular hs h)).comp
      (f:=cubicThetaGlobalSpectralParameter) (x:=s) hp
  have hF := (cubicThetaGlobalInclusion.adjoint.analyticAt (cubicThetaForcingL2 s)).comp
    (f:=cubicThetaForcingL2) (x:=s) (cubicThetaForcingL2_analytic s)
  exact analytic_apply hA hF

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionEnergyInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion is an involutive isometry of the actual energy space and
preserves its mass form. It therefore preserves every spectral kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaInversionSection_involutive (F : CubicThetaSection) :
    cubicThetaInversionSection (cubicThetaInversionSection F)=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  change F.val (cubicThetaFullInversion • (cubicThetaFullInversion • p))=F.val p
  rw [cubicThetaFullInversion_involutive]

lemma cubicThetaInversionSmooth_involutive (F : cubicThetaSmoothTests) :
    cubicThetaInversionSmooth (cubicThetaInversionSmooth F)=F := by
  apply Subtype.ext
  exact cubicThetaInversionSection_involutive F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScatteringResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant Fourier observation of the actual spectral residue is
the explicitly computed arithmetic scattering residue. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

def cubicThetaScatteringResidue : ℂ :=
  (principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2)

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

def cubicThetaRegularizedFrequency (h : Eisenstein) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => (s-4/3)*cubicThetaFrequencyContinuation h s) {s : ℂ | 1 < s.re}

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergyPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal domain formulas for both Hermitian pairings on actual
finite-energy sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteEnergyValue_pairing (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyValue F) (cubicThetaFiniteEnergyValue G)=
      ∫ x in cubicThetaFundamentalDomain,inner ℂ (F.val.val x) (G.val.val x) ∂cubicThetaPointMeasure := by
  change inner ℂ (F.property.2.1.toLp _) (G.property.2.1.toLp _)=_
  rw [cubicThetaSectionPairing_L2 F.val G.val F.property.2.1 G.property.2.1,cubicThetaQuotientMeasure]
  have he := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    (cubicThetaSectionPairing_continuous F.val G.val).stronglyMeasurable
  simpa only [cubicThetaSectionPairing_apply] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
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

theorem cubicThetaHorizontalCell_fundamental (μ : Measure ℂ) :
    IsFundamentalDomain CubicThetaPeriodGroup cubicThetaHorizontalCell μ :=
  IsFundamentalDomain.mk' cubicThetaHorizontalCell_measurable.nullMeasurableSet
    cubicThetaHorizontalCell_unique

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration of a level-three periodic function is independent of
horizontal translation, on the actual half-open Eisenstein cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalTranslated_fundamental (a : ℂ) :
    IsFundamentalDomain CubicThetaPeriodGroup
      ((fun z : ℂ => z+a) '' cubicThetaHorizontalCell) volume := by
  apply (cubicThetaHorizontalCell_fundamental volume).image_of_equiv
    (Homeomorph.addRight a).toEquiv
    (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
    (Equiv.refl CubicThetaPeriodGroup)
  intro g z
  change (z+3*((Multiplicative.toAdd g:Eisenstein):ℂ))+a=(z+a)+3*((Multiplicative.toAdd g:Eisenstein):ℂ)
  ring

lemma cubicThetaHorizontal_translate_integral (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (a : ℂ) :
    (∫ z in cubicThetaHorizontalCell,f (z+a))=∫ z in cubicThetaHorizontalCell,f z := by
  have hi (g : CubicThetaPeriodGroup) (z : ℂ) : f (g • z)=f z := hf (Multiplicative.toAdd g) z
  have he := (cubicThetaHorizontalCell_fundamental volume).setIntegral_eq
    (cubicThetaHorizontalTranslated_fundamental a) hi
  have hc := (measurePreserving_add_right volume a).setIntegral_image_emb
    (Homeomorph.addRight a).measurableEmbedding f cubicThetaHorizontalCell
  exact (he.trans hc).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalAffine
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaHorizontal_affine_integral (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (b : ℂ) :
    (∫ z in cubicThetaHorizontalCell,f ((a:ℂ)*z+b))=
      ∫ z in cubicThetaHorizontalCell,f ((a:ℂ)*z) := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have he (z : ℂ) : f ((a:ℂ)*z+b)=f ((a:ℂ)*(z+b/(a:ℂ))) := by
    congr 1
    field_simp [haC]
  simp_rw [he]
  exact cubicThetaHorizontal_translate_integral (fun z => f ((a:ℂ)*z))
    (cubicThetaHorizontal_multiply_periodic f hf a) (b/(a:ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaHorizontalScaledCell_fundamental {a : Eisenstein} (ha : a≠0) :
    IsFundamentalDomain (CubicThetaScaledPeriodGroup a) (cubicThetaHorizontalScaledCell a) volume := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have hqmp : Measure.QuasiMeasurePreserving (fun z : ℂ => (a:ℂ)⁻¹*z) volume volume := by
    refine ⟨by fun_prop,?_⟩
    rw [complexMul_map_volume _ (inv_ne_zero haC)]
    exact Measure.smul_absolutelyContinuous
  apply IsFundamentalDomain.image_of_equiv (H := CubicThetaScaledPeriodGroup a)
    (cubicThetaHorizontalCell_fundamental volume)
    (complexMulEquiv (a:ℂ) haC).toEquiv
    hqmp
    (show CubicThetaScaledPeriodGroup a ≃ CubicThetaPeriodGroup from Equiv.refl _)
  intro g z
  change (a:ℂ)*(z+3*((Multiplicative.toAdd g:Eisenstein):ℂ))=
    (a:ℂ)*z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ)
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A disjoint finite union of period cells for the scaled horizontal lattice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCover_measurable {a : Eisenstein} (ha : a≠0) :
    MeasurableSet (cubicThetaHorizontalCover a) := by
  let : Finite (Residues a) := finite_residues ha
  apply MeasurableSet.iUnion
  intro r
  exact (Homeomorph.subRight (3*(residueRepresentative a r:ℂ))).measurableEmbedding.measurableSet_image'
    cubicThetaHorizontalCell_measurable

lemma cubicThetaHorizontalCover_fundamental {a : Eisenstein} (ha : a≠0) :
    IsFundamentalDomain (CubicThetaScaledPeriodGroup a) (cubicThetaHorizontalCover a) volume :=
  IsFundamentalDomain.mk' (cubicThetaHorizontalCover_measurable ha).nullMeasurableSet
    (cubicThetaHorizontalCover_unique ha)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact integration over a finite horizontal lattice cover and its dilated
fundamental cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCover_integral {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    (∫ z in cubicThetaHorizontalCover a,f z)=
      (Nat.card (Residues a):ℂ)*(∫ z in cubicThetaHorizontalCell,f z) := by
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  have hmeas (r : Residues a) :
      MeasurableSet ((fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell) :=
    (Homeomorph.subRight _).measurableEmbedding.measurableSet_image' cubicThetaHorizontalCell_measurable
  have hint (r : Residues a) :
      IntegrableOn f ((fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell) := by
    have hp (g : CubicThetaPeriodGroup) (z : ℂ) : f (g • z)=f z := hf (Multiplicative.toAdd g) z
    have hh := ((cubicThetaHorizontalCell_fundamental volume).integrableOn_iff
      (cubicThetaHorizontalTranslated_fundamental (-3*(residueRepresentative a r:ℂ))) hp).mp hi
    simpa only [sub_eq_add_neg,neg_mul] using hh
  unfold cubicThetaHorizontalCover
  rw [integral_iUnion_fintype hmeas (cubicThetaHorizontalCover_disjoint a) hint]
  have he (r : Residues a) :
      (∫ z in (fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell,f z)=
        ∫ z in cubicThetaHorizontalCell,f z := by
    have ht := (cubicThetaHorizontalCell_fundamental volume).setIntegral_eq
      (cubicThetaHorizontalTranslated_fundamental (-3*(residueRepresentative a r:ℂ)))
      (fun g z => hf (Multiplicative.toAdd g) z)
    simpa only [sub_eq_add_neg,neg_mul] using ht.symm
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul]

lemma cubicThetaHorizontalScaledCell_integral {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    (∫ z in cubicThetaHorizontalScaledCell a,f z)=
      (Nat.card (Residues a):ℂ)*(∫ z in cubicThetaHorizontalCell,f z) := by
  have hp (g : CubicThetaScaledPeriodGroup a) (z : ℂ) : f (g • z)=f z := by
    change f (z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ))=f z
    simpa only [Subalgebra.coe_mul,mul_assoc] using hf (a*Multiplicative.toAdd g) z
  exact ((cubicThetaHorizontalScaledCell_fundamental ha).setIntegral_eq
    (cubicThetaHorizontalCover_fundamental ha) hp).trans
    (cubicThetaHorizontalCover_integral ha f hf hi)

lemma cubicThetaHorizontal_mul_integral {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    (∫ z in cubicThetaHorizontalCell,f ((a:ℂ)*z))=∫ z in cubicThetaHorizontalCell,f z := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have he := setIntegral_map_equiv (μ:=volume)
    (complexMulEquiv (a:ℂ) haC).toHomeomorph.toMeasurableEquiv f (cubicThetaHorizontalScaledCell a)
  have hpre : (complexMulEquiv (a:ℂ) haC) ⁻¹' cubicThetaHorizontalScaledCell a=
      cubicThetaHorizontalCell := by
    exact (complexMulEquiv (a:ℂ) haC).injective.preimage_image _
  change (∫ z in cubicThetaHorizontalScaledCell a,f z
    ∂Measure.map (fun z : ℂ => (a:ℂ)*z) volume)=
    ∫ z in (complexMulEquiv (a:ℂ) haC) ⁻¹' cubicThetaHorizontalScaledCell a,f ((a:ℂ)*z) at he
  rw [hpre,complexMul_map_volume _ haC,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Complex.normSq_nonneg _)),
    cubicThetaHorizontalScaledCell_integral ha f hf hi,residues_card ha] at he
  have hn : (normNat a:ℝ)=Complex.normSq (a:ℂ) := normNat_cast a
  have hnC : (normNat a:ℂ)=((Complex.normSq (a:ℂ):ℝ):ℂ) := by exact_mod_cast hn
  rw [Complex.real_smul,hnC,←mul_assoc,←Complex.ofReal_mul,
    inv_mul_cancel₀ (Complex.normSq_pos.mpr haC).ne',Complex.ofReal_one,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaHorizontalFourier_translate (h : Eisenstein) (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) (b : ℂ) :
    cubicThetaHorizontalFourierCoefficient h (fun z => f (z+b))=
      cubicThetaHorizontalCharacter h b*cubicThetaHorizontalFourierCoefficient h f := by
  let g := fun z => star (cubicThetaHorizontalCharacter h z)*f z
  have he := cubicThetaHorizontal_translate_integral g
    (cubicThetaHorizontalFourier_integrand_periodic h f hf) b
  have hint : (∫ z in cubicThetaHorizontalCell,g (z+b))=
      star (cubicThetaHorizontalCharacter h b)*
        cubicThetaHorizontalFourierCoefficient h (fun z => f (z+b)) := by
    rw [cubicThetaHorizontalFourierCoefficient,←integral_const_mul]
    apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
    intro z _
    dsimp only [g]
    rw [cubicThetaHorizontalCharacter_add,star_mul]
    ring
  rw [hint] at he
  have hu : cubicThetaHorizontalCharacter h b*star (cubicThetaHorizontalCharacter h b)=1 := by
    rw [mul_comm]
    exact cubicThetaHorizontalCharacter_unit h b
  calc
    _ = (cubicThetaHorizontalCharacter h b*star (cubicThetaHorizontalCharacter h b))*
        cubicThetaHorizontalFourierCoefficient h (fun z => f (z+b)) := by rw [hu,one_mul]
    _ = _ := by rw [mul_assoc,he]; rfl

theorem cubicThetaHorizontalFourier_dilate (f : ℂ → ℂ)
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    {a : Eisenstein} (ha : a≠0) (h : Eisenstein)
    (hi : IntegrableOn (fun z => star (cubicThetaHorizontalCharacter h z)*f z) cubicThetaHorizontalCell) :
    cubicThetaHorizontalFourierCoefficient (a*h) (fun z => f ((a:ℂ)*z))=
      cubicThetaHorizontalFourierCoefficient h f := by
  unfold cubicThetaHorizontalFourierCoefficient
  simp_rw [cubicThetaHorizontalCharacter_mul_index]
  exact cubicThetaHorizontal_mul_integral ha (fun z => star (cubicThetaHorizontalCharacter h z)*f z)
    (cubicThetaHorizontalFourier_integrand_periodic h f hf) hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalPeriodMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal bottom-branch periodization has its exact degree as mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaHorizontalPeriodization_mean {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaHorizontalPeriodization a f z)=
      (norm a:ℂ)*(∫ z in cubicThetaHorizontalCell,f z) := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  have ht (b : Eisenstein) (z : ℂ) :
      cubicThetaHorizontalFraction a f b ((a:ℂ)*z)=f (z+3*(b:ℂ)/(a:ℂ)) := by
    unfold cubicThetaHorizontalFraction
    congr 1
    field_simp [haC]
  rw [←cubicThetaHorizontal_mul_integral ha _
    (cubicThetaHorizontalPeriodization_periodic ha f hf)
    (cubicThetaHorizontalPeriodization_integrable ha f)]
  unfold cubicThetaHorizontalPeriodization
  simp_rw [ht,tsum_fintype]
  have hi (r : Residues a) : IntegrableOn (fun z => f (z+3*(residueRepresentative a r:ℂ)/(a:ℂ)))
      cubicThetaHorizontalCell := by
    simpa only [one_mul] using cubicThetaHorizontal_affine_integrable f 1
      (3*(residueRepresentative a r:ℂ)/(a:ℂ))
  rw [integral_finsetSum Finset.univ (fun r _ => hi r)]
  simp_rw [cubicThetaHorizontal_translate_integral f hf]
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,residues_card ha,nsmul_eq_mul]
  have hn : (normNat a:ℂ)=(norm a:ℂ) := by exact_mod_cast normNat_cast a
  rw [hn]

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

def cubicThetaRegularizedRamifiedLow (h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedFrequency (lambdaE^3*h) s-
    cubicThetaRamifiedCubeFactor s*cubicThetaRegularizedFrequency h s

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

def cubicThetaRegularizedPrimaryOne (h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedRamifiedLow h s/
    (cubicThetaRamifiedCubeFactor s*cubicThetaRamifiedTrace h)

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

def cubicThetaInvertedWindowTest : cubicThetaSmoothTests :=
  cubicThetaInversionSmooth (cubicThetaHighWindowTest (4/3))

def cubicThetaInvertedWindowObservable (s : ℂ) : ℂ :=
  cubicThetaArithmeticDistribution cubicThetaInvertedWindowTest
    cubicThetaInvertedWindowTest.property.2 s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeUnitMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeSquareCharacter_mean {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (b : (Residues p)ˣ → ℂ) :
    (∫ z in cubicThetaHorizontalCell,
      ∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2*
        f ((p:ℂ)*z+b u))=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues p)ˣ := Fintype.ofFinite _
  simp_rw [tsum_fintype]
  rw [integral_finsetSum Finset.univ (fun u _ =>
    (cubicThetaHorizontal_affine_integrable f (p:ℂ) (b u)).const_mul _)]
  simp_rw [integral_const_mul,cubicThetaHorizontal_affine_integral f hf hp.2.ne_zero]
  have hc : (∑ u : (Residues p)ˣ,
      (cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2)=0 := by
    simpa only [tsum_fintype] using cubicThetaPrimeCubeSquareCharacter_sum hp
  rw [←Finset.sum_mul,hc,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeFirstPeriodization_mean {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaPrimeCubeFirstPeriodization p f z)=0 := by
  let : Finite (Residues (p^2)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^2)) := Fintype.ofFinite _
  rw [←cubicThetaHorizontal_mul_integral hp.2.ne_zero _
    (cubicThetaPrimeCubeFirstPeriodization_periodic hp f hf)
    (cubicThetaPrimeCubeFirstPeriodization_integrable hp f)]
  unfold cubicThetaPrimeCubeFirstPeriodization
  simp_rw [cubicThetaPrimeCubeFirstPeriodization_dilate hp,tsum_fintype]
  have hi (r : Residues (p^2)) : IntegrableOn
      (fun z => f (z+3*(residueRepresentative (p^2) r:ℂ)/(p:ℂ)^2)) cubicThetaHorizontalCell := by
    simpa only [one_mul] using cubicThetaHorizontal_affine_integrable f 1
      (3*(residueRepresentative (p^2) r:ℂ)/(p:ℂ)^2)
  rw [integral_finsetSum Finset.univ (fun r _ => (hi r).const_mul _)]
  simp_rw [integral_const_mul,cubicThetaHorizontal_translate_integral f hf]
  have hs : (∑ r : Residues (p^2),cubicSymbol p (3*residueRepresentative (p^2) r))=0 := by
    simpa only [tsum_fintype] using cubicThetaPrimeCubeFirstCoefficient_sum hp
  rw [←Finset.sum_mul,hs,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstBranchMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeFirstBranch_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,
      cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z))=0 := by
  simp_rw [cubicThetaPrimeCubeFirstBranch_periodization hp]
  exact cubicThetaPrimeCubeFirstPeriodization_mean hp _ (cubicThetaSectionHorizontal_periodic F _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBottomMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeBottom_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,
      cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z))=
    (norm (p^3):ℂ)*∫ z in cubicThetaHorizontalCell,
      cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) z := by
  simp_rw [cubicThetaPrimeCubeBottom_periodization]
  exact cubicThetaHorizontalPeriodization_mean (pow_ne_zero _ hp.2.ne_zero) _
    (cubicThetaSectionHorizontal_periodic F _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSecondBranchMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeCubeSecondBranch_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,
      cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
        (cubicThetaHorizontalPoint v hv z))=0 := by
  simp_rw [cubicThetaPrimeCubeUnitFunctionSum_two,cubicThetaPrimeCubeSecondBranch_section]
  exact cubicThetaPrimeCubeSquareCharacter_mean hp
    (cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
      (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv))
    (cubicThetaSectionHorizontal_periodic F _ _)
    (fun u => 3*(residueRepresentative p (u:Residues p):ℂ)/(p:ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHorizontalMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeDilation_horizontal_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
    ∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
      (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) z := by
  have he : (fun z : ℂ => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
      (fun z => cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z)) := by
    funext z
    rw [cubicThetaPrimeCubeDilation_horizontal_point hp]
    rfl
  rw [he]
  exact cubicThetaHorizontal_mul_integral (pow_ne_zero _ hp.2.ne_zero) _
    (cubicThetaSectionHorizontal_periodic F _ _) (cubicThetaSectionHorizontal_integrable F _ _)

theorem cubicThetaPrimeCubeHecke_horizontal_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal (cubicThetaPrimeCubeHecke hp F) v hv z)=
      (∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) z)+
      (norm (p^3):ℂ)*(∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) z) := by
  let D := fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
    cubicThetaHorizontalPoint v hv z)
  let B := fun z => cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z)
  let U := fun z => cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z)
  let V := fun z => cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩:Fin 3) F.val
    (cubicThetaHorizontalPoint v hv z)
  have hD : IntegrableOn D cubicThetaHorizontalCell := cubicThetaPrimeCubeDilation_horizontal_integrable hp F v hv
  have hB : IntegrableOn B cubicThetaHorizontalCell := cubicThetaPrimeCubeBottom_horizontal_integrable hp F v hv
  have hU : IntegrableOn U cubicThetaHorizontalCell := cubicThetaPrimeCubeUnit_horizontal_integrable hp 1 F v hv
  have hV : IntegrableOn V cubicThetaHorizontalCell := cubicThetaPrimeCubeUnit_horizontal_integrable hp _ F v hv
  have he : (fun z => cubicThetaSectionHorizontal (cubicThetaPrimeCubeHecke hp F) v hv z)=D+B+U+V := by
    funext z
    exact cubicThetaPrimeCubeHecke_functionOperator hp F (cubicThetaHorizontalPoint v hv z)
  have hDB : integral (volume.restrict cubicThetaHorizontalCell) (D+B)=
      integral (volume.restrict cubicThetaHorizontalCell) D+integral (volume.restrict cubicThetaHorizontalCell) B :=
    integral_add hD hB
  have hDBU : integral (volume.restrict cubicThetaHorizontalCell) (D+B+U)=
      integral (volume.restrict cubicThetaHorizontalCell) (D+B)+integral (volume.restrict cubicThetaHorizontalCell) U :=
    integral_add (hD.add hB) hU
  have hDBUV : integral (volume.restrict cubicThetaHorizontalCell) (D+B+U+V)=
      integral (volume.restrict cubicThetaHorizontalCell) (D+B+U)+integral (volume.restrict cubicThetaHorizontalCell) V :=
    integral_add ((hD.add hB).add hU) hV
  rw [he,hDBUV,hDBU,hDB]
  change (∫ z in cubicThetaHorizontalCell,D z)+(∫ z in cubicThetaHorizontalCell,B z)+
    (∫ z in cubicThetaHorizontalCell,U z)+(∫ z in cubicThetaHorizontalCell,V z)=_
  rw [show (∫ z in cubicThetaHorizontalCell,U z)=0 from cubicThetaPrimeCubeFirstBranch_mean hp F v hv,
    show (∫ z in cubicThetaHorizontalCell,V z)=0 from cubicThetaPrimeCubeSecondBranch_mean hp F v hv,
    add_zero,add_zero]
  exact congrArg₂ (·+·) (cubicThetaPrimeCubeDilation_horizontal_mean hp F v hv)
    (cubicThetaPrimeCubeBottom_mean hp F v hv)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof-independent scalar horizontal mean for actual sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionMean_eq (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    cubicThetaSectionMean F v=
      ∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F v hv z := by
  unfold cubicThetaSectionMean
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  exact cubicThetaSectionFunction_apply F hv

theorem cubicThetaSectionMean_hecke {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    cubicThetaSectionMean (cubicThetaPrimeCubeHecke hp F) v=
      cubicThetaSectionMean F (‖(p:ℂ)‖^3*v)+
        (norm (p^3):ℂ)*cubicThetaSectionMean F (v/‖(p:ℂ)‖^3) := by
  have hn : 0<‖(p:ℂ)‖^3 := pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3
  rw [cubicThetaSectionMean_eq _ _ hv,cubicThetaSectionMean_eq _ _ (mul_pos hn hv),
    cubicThetaSectionMean_eq _ _ (div_pos hv hn)]
  exact cubicThetaPrimeCubeHecke_horizontal_mean hp F v hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionMeanPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine compact radial observations of finite-energy sections, expressed
through their scalar horizontal means. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSectionMeanPairing (F : cubicThetaFiniteEnergySections) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaFiniteCuspRestriction F)=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionMean F v := by
  have hi := cubicThetaSectionMeanPairing_integrable F W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2)*cubicThetaSectionFunction F y) hi'
  have hpair : inner ℂ (cubicThetaCuspFourierTest 0 W) (cubicThetaFiniteCuspRestriction F)=
      ∫ p in cubicThetaCuspStrip 2,star (W p.val.2)*cubicThetaSectionFunction F p.val
        ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 W).coeFn_toLp,
      (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 W).toLp _) p)
      (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
    rw [hW,hF,cubicThetaSectionFunction_coordinates]
    rw [show cubicThetaCuspFourierWeight 0 W p=W p.val.2 from by
      simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair]]
    simpa only [starRingEnd_apply] using (RCLike.inner_apply' (W p.val.2) (F.val.val p))
  change (∫ p in cubicThetaCuspStrip 2,star (W p.val.2)*cubicThetaSectionFunction F p.val
    ∂cubicThetaPointMeasure)=
    ∫ v in Ioi (2:ℝ),∫ z in cubicThetaHorizontalCell,
      star (W v)*cubicThetaSectionFunction F (z,v)/(v:ℂ)^3 at he
  rw [hpair]
  refine he.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaSectionMean]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  ring

theorem cubicThetaSectionMeanPairing_hecke {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaFiniteCuspRestriction (cubicThetaPrimeCubeHeckeFinite hp F))=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
        (cubicThetaSectionMean F (‖(p:ℂ)‖^3*v)+
          (norm (p^3):ℂ)*cubicThetaSectionMean F (v/‖(p:ℂ)‖^3)) := by
  rw [cubicThetaSectionMeanPairing]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have hv' : 0<v := lt_trans (by norm_num) hv
  change star (W v)/(v:ℂ)^3*cubicThetaSectionMean (cubicThetaPrimeCubeHecke hp F) v=_
  rw [cubicThetaSectionMean_hecke hp _ v hv']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfilePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaRadialProfilePairing_section (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    inner ℂ (cubicThetaRadialProfileL2 W hW) (hF.toLp _)=
      ∫ p in cubicThetaCuspStrip 2,
        inner ℂ (W p.val.2) (F.val p) ∂cubicThetaPointMeasure := by
  rw [cubicThetaRadialProfileL2,cubicThetaSectionPairing_L2]
  have he : (∫ q, cubicThetaSectionPairing (cubicThetaRadialProfileSection W (fun v hv => hW v (by linarith))) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ q in cubicThetaQuotientMap '' cubicThetaCuspStrip 2,
        cubicThetaSectionPairing (cubicThetaRadialProfileSection W (fun v hv => hW v (by linarith))) F q
          ∂cubicThetaQuotientMeasure := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    have hz := cubicThetaRadialProfileSeries_off_cusp W hW (cubicThetaQuotientLift q)
      (by rwa [cubicThetaQuotientLift_map])
    change inner ℂ (cubicThetaRadialProfileSeries (cubicThetaQuotientLift q).val W) _=0
    rw [hz,inner_zero_left]
  rw [he,cubicThetaInjective_complex_integral (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) _
    (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  dsimp only
  rw [cubicThetaSectionPairing_apply]
  change inner ℂ (cubicThetaRadialProfileSeries p.val W) _=_
  rw [cubicThetaRadialProfileSeries_high W (fun v hv => hW v (by linarith))
    (by have h:=hp.1; change 2<p.val.2 at h; linarith)]

lemma cubicThetaRadialProfilePairing_finiteEnergy (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaRadialProfileL2 W hW) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaCuspFourierTest 0 (W))
        (cubicThetaFiniteCuspRestriction F) := by
  change inner ℂ (cubicThetaRadialProfileL2 W hW) (F.property.2.1.toLp _)=_
  rw [cubicThetaRadialProfilePairing_section W hW F F.property.2.1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 (W)).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change _=inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 (W)).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)
  rw [hW,hF]
  simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindowKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

lemma cubicThetaLongWindow_global_weak (H : ℝ) (hH : 2≤H) (s : ℂ)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalGradient (cubicThetaLongWindowTest H hH s))+
      s*(s-2)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalMass (cubicThetaLongWindowTest H hH s))=
      inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaRadialProfileL2 (cubicThetaLongForcingWeight H (by linarith) s)
          (cubicThetaLongForcingWeight_low_two hH s)-cubicThetaForcingL2 s) := by
  have he := cubicThetaSmooth_global_weak (cubicThetaLongWindowTest H hH s)
    (cubicThetaLongWindowDefectSection H hH s) (cubicThetaLongWindowDefectSection_compact H hH s)
    (s*(s-2)) (cubicThetaLongWindow_coordinate_equation H hH s) v
  rwa [cubicThetaLongWindowDefectL2] at he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeComplexIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex integration on the actual cubed-prime cover and the
integrability of Hermitian products of square-integrable sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeComplexSheetIntegral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℂ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure)=
      ∑' t : cubicThetaPrimeCubeTransversal p,
        ∫ x in cubicThetaFundamentalDomain,f (t.val • x) ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hmeas (t : cubicThetaPrimeCubeTransversal p) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' cubicThetaFundamentalDomain_measurable
  have hint (t : cubicThetaPrimeCubeTransversal p) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  change (∫ x in ⋃ t : cubicThetaPrimeCubeTransversal p,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaFundamentalDomain,f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas (cubicThetaPrimeCubeCoverDomain_disjoint p) hint]
  apply Finset.sum_congr rfl
  intro t _
  exact (measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul t.val) f cubicThetaFundamentalDomain

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Trace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The gradient trace identity before integration. Its finite sum uses
the same literal representatives and cubic phases as the Hecke trace. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Trace_gradient_point {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hG : ∀ g : cubicThetaPrincipalGroup,
      cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) G=cubicThetaKubotaValue g • G)
    (x : CubicThetaPoint) :
    inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp F))=
      ∑' t : cubicThetaPrimeCubeTransversal p,
        inner ℂ (cubicThetaPointC1Gradient (t.val • x) G) (cubicThetaPointC1Gradient (t.val • x) F) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  simp only [cubicThetaPointC1Trace,map_sum,map_smul,inner_sum,tsum_fintype]
  apply Finset.sum_congr rfl
  intro t _
  have he := cubicThetaPointC1Pullback_gradient_pair (cubicThetaPrincipalComplex t.val) G F x
  rw [hG t.val,map_smul,inner_smul_left] at he
  rw [inner_smul_right]
  change (starRingEnd ℂ) (cubicThetaKubotaValue t.val)*
    inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback (cubicThetaPrincipalComplex t.val) F))=
    inner ℂ (cubicThetaPointC1Gradient (cubicThetaPrincipalComplex t.val • x) G)
      (cubicThetaPointC1Gradient (cubicThetaPrincipalComplex t.val • x) F)
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkinPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeComplexAtkin_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℂ}
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f (cubicThetaPrimeCubeAtkinMatrix hp • x)
      ∂cubicThetaPointMeasure)=∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hi
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp)) f (cubicThetaPrimeCubeCoverDomain p)
  exact (he.trans hc).symm

theorem cubicThetaPrimeCubeAtkin_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeCubeSections p) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,
      star (G.val x)*F.val (cubicThetaPrimeCubeAtkinMatrix hp • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      star (G.val (cubicThetaPrimeCubeAtkinMatrix hp • x))*F.val x ∂cubicThetaPointMeasure := by
  have he := cubicThetaPrimeCubeComplexAtkin_integral hp
    (f:=fun x => star ((cubicThetaPrimeCubeAtkinSection hp G).val x)*F.val x)
    (cubicThetaPrimeCubePair_invariant (cubicThetaPrimeCubeAtkinSection hp G) F)
  change (∫ x in cubicThetaPrimeCubeCoverDomain p,
    star (G.val (cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrimeCubeAtkinMatrix hp • x)))*
      F.val (cubicThetaPrimeCubeAtkinMatrix hp • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      star (G.val (cubicThetaPrimeCubeAtkinMatrix hp • x))*F.val x ∂cubicThetaPointMeasure at he
  simpa only [cubicThetaPrimeCubeAtkinPoint_involutive] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Pairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPointC1Atkin_gradient_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hF : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,
      F.val (g.val • x)=cubicThetaKubotaValue g.val*F.val x)
    (hG : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,
      G.val (g.val • x)=cubicThetaKubotaValue g.val*G.val x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) F))
      ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) G))
        (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure := by
  let W := cubicThetaPrimeCubeAtkinMatrix hp
  have hi (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (g • x) (cubicThetaPointC1Pullback W G))
        (cubicThetaPointC1Gradient (g • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback W G))
        (cubicThetaPointC1Gradient x F) :=
    cubicThetaPointC1Pair_covariance F (cubicThetaPointC1Pullback W G) g.val (hF g)
      (cubicThetaPointC1Atkin_covariance hp G hG g) x
  have he := cubicThetaPrimeCubeComplexAtkin_integral hp
    (f:=fun x => inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback W G))
      (cubicThetaPointC1Gradient x F)) hi
  have hGG : cubicThetaPointC1Pullback W (cubicThetaPointC1Pullback W G)=G := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg G.val (cubicThetaPrimeCubeAtkinPoint_involutive hp x)
  have ht (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (W • x) (cubicThetaPointC1Pullback W G))
        (cubicThetaPointC1Gradient (W • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback W F)) := by
    rw [←cubicThetaPointC1Pullback_gradient_pair W,hGG]
  dsimp [W] at he ht
  simpa only [ht] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1TraceIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The gradient trace adjoint on the actual finite cover, obtained
from the pointwise isometry identity and justified finite integration. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPointC1Trace_gradient_integral {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hG : ∀ g : cubicThetaPrincipalGroup,
      cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) G=cubicThetaKubotaValue g • G)
    (hF : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x F‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hGc : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x G‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp F))
      ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hi := cubicThetaPointC1Pair_integrable F G hF hGc
  simp_rw [cubicThetaPointC1Trace_gradient_point hp F G hG,tsum_fintype]
  rw [integral_finsetSum Finset.univ (fun t _ => cubicThetaPrimeCubeComplexSheet_integrable hp hi t),
    cubicThetaPrimeCubeComplexSheetIntegral hp hi,tsum_fintype]

theorem cubicThetaPointC1Trace_gradient_integral_left {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hG : ∀ g : cubicThetaPrincipalGroup,
      cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) G=cubicThetaKubotaValue g • G)
    (hF : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x F‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hGc : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x G‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp F)) (cubicThetaPointC1Gradient x G)
      ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x F) (cubicThetaPointC1Gradient x G) ∂cubicThetaPointMeasure := by
  have he := congrArg star (cubicThetaPointC1Trace_gradient_integral hp F G hG hF hGc)
  rwa [cubicThetaPointC1Pair_flip,cubicThetaPointC1Pair_flip] at he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTracePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubed-prime trace is adjoint to restriction for actual
square-integrable sections, with the exact unnormalized cover measure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeTrace_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      star (G.val x)*(cubicThetaPrimeCubeTraceSection hp F).val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,star (G.val x)*F.val x ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hGc := cubicThetaPrimeCubeInvariant_integrable hp hG (cubicThetaOriginal_norm_invariant G)
  have hi := cubicThetaSquareIntegrablePair G.val F.val G.val.continuous F.val.continuous hGc hF
  simp_rw [cubicThetaPrimeCubeTrace_pair_point,tsum_fintype]
  rw [integral_finsetSum Finset.univ (fun t _ => cubicThetaPrimeCubeComplexSheet_integrable hp hi t),
    cubicThetaPrimeCubeComplexSheetIntegral hp hi,tsum_fintype]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mass adjoint of the literal cubed-prime correspondence. All
integrals use the constructed arithmetic domains. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeTrace_pairing_left {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      star ((cubicThetaPrimeCubeTraceSection hp F).val x)*G.val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,star (F.val x)*G.val x ∂cubicThetaPointMeasure := by
  have he := congrArg star (cubicThetaPrimeCubeTrace_pairing hp F G hF hG)
  rwa [cubicThetaComplexPair_flip,cubicThetaComplexPair_flip] at he

lemma cubicThetaComplexInversion_integral {f : CubicThetaPoint → ℂ}
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaFundamentalDomain,f (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) hi
  have hc := (measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul cubicThetaFullInversion) f cubicThetaFundamentalDomain
  exact (he.trans hc).symm

lemma cubicThetaInversion_pair_domain (F G : CubicThetaSection) :
    (∫ x in cubicThetaFundamentalDomain,
      star (G.val x)*(cubicThetaInversionSection F).val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      star ((cubicThetaInversionSection G).val x)*F.val x ∂cubicThetaPointMeasure := by
  have hi (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      star ((cubicThetaInversionSection G).val (g • x))*F.val (g • x)=
        star ((cubicThetaInversionSection G).val x)*F.val x := by
    simpa only [RCLike.inner_apply',Complex.star_def] using
      cubicThetaSectionPairing_invariant (cubicThetaInversionSection G) F g x
  have he := cubicThetaComplexInversion_integral
    (f:=fun x => star ((cubicThetaInversionSection G).val x)*F.val x) hi
  change (∫ x in cubicThetaFundamentalDomain,
    star (G.val (cubicThetaFullInversion • (cubicThetaFullInversion • x)))*
      F.val (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,star (G.val (cubicThetaFullInversion • x))*
      F.val x ∂cubicThetaPointMeasure at he
  change (∫ x in cubicThetaFundamentalDomain,
    star (G.val x)*F.val (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,star (G.val (cubicThetaFullInversion • x))*
      F.val x ∂cubicThetaPointMeasure
  simpa only [cubicThetaFullInversion_involutive] using he

theorem cubicThetaPrimeCubeHecke_mass_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      star (G.val x)*(cubicThetaPrimeCubeHecke hp F).val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      star ((cubicThetaInversionSection (cubicThetaPrimeCubeHecke hp
        (cubicThetaInversionSection G))).val x)*F.val x ∂cubicThetaPointMeasure := by
  let X := cubicThetaPrimeCubeAtkinSection hp (cubicThetaPrimeCubeSectionRestrict G)
  have hX : IntegrableOn (fun x => ‖X.val x‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure :=
    cubicThetaPrimeCubeAtkin_integrable hp _
      (cubicThetaPrimeCubeInvariant_integrable hp hG (cubicThetaOriginal_norm_invariant G))
  calc
    _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
        star (G.val x)*(cubicThetaPrimeCubeDilationSection hp F).val x ∂cubicThetaPointMeasure :=
      cubicThetaPrimeCubeTrace_pairing hp _ G (cubicThetaPrimeCubeDilation_integrable hp F hF) hG
    _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
        star (X.val x)*(cubicThetaInversionSection F).val x ∂cubicThetaPointMeasure := by
      rw [cubicThetaPrimeCubeDilation_eq_atkin]
      exact cubicThetaPrimeCubeAtkin_pairing hp
        (cubicThetaPrimeCubeSectionRestrict (cubicThetaInversionSection F))
        (cubicThetaPrimeCubeSectionRestrict G)
    _ = ∫ x in cubicThetaFundamentalDomain,
        star ((cubicThetaPrimeCubeTraceSection hp X).val x)*
          (cubicThetaInversionSection F).val x ∂cubicThetaPointMeasure :=
      (cubicThetaPrimeCubeTrace_pairing_left hp X (cubicThetaInversionSection F) hX
        (cubicThetaInversion_domain_integrable F hF)).symm
    _ = ∫ x in cubicThetaFundamentalDomain,
        star ((cubicThetaInversionSection (cubicThetaPrimeCubeTraceSection hp X)).val x)*
          F.val x ∂cubicThetaPointMeasure :=
      cubicThetaInversion_pair_domain F (cubicThetaPrimeCubeTraceSection hp X)
    _ = _ := by rw [show X=cubicThetaPrimeCubeDilationSection hp (cubicThetaInversionSection G) from
      cubicThetaPrimeCubeAtkin_restrict_eq hp G]; rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Inversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global inversion for the actual gradient pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPointC1Inversion_gradient_pairing (F G : cubicThetaPointC1)
    (hF : ∀ (g : cubicThetaPrincipalGroup) x,F.val (g • x)=cubicThetaKubotaValue g*F.val x)
    (hG : ∀ (g : cubicThetaPrincipalGroup) x,G.val (g • x)=cubicThetaKubotaValue g*G.val x) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback
          (cubicThetaFullComplex cubicThetaFullInversion) F)) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback
        (cubicThetaFullComplex cubicThetaFullInversion) G))
        (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure := by
  let S := cubicThetaFullComplex cubicThetaFullInversion
  have hi (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (g • x) (cubicThetaPointC1Pullback S G))
        (cubicThetaPointC1Gradient (g • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S G))
        (cubicThetaPointC1Gradient x F) :=
    cubicThetaPointC1Pair_covariance F (cubicThetaPointC1Pullback S G) g (hF g)
      (cubicThetaPointC1Inversion_covariance G hG g) x
  have he := cubicThetaComplexInversion_integral
    (f:=fun x => inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S G))
      (cubicThetaPointC1Gradient x F)) hi
  have hGG : cubicThetaPointC1Pullback S (cubicThetaPointC1Pullback S G)=G := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg G.val (cubicThetaFullInversion_involutive x)
  have ht (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (cubicThetaFullInversion • x) (cubicThetaPointC1Pullback S G))
        (cubicThetaPointC1Gradient (cubicThetaFullInversion • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F)) := by
    have hh := cubicThetaPointC1Pullback_gradient_pair S (cubicThetaPointC1Pullback S G) F x
    rw [hGG] at hh
    exact hh.symm
  dsimp [S] at he ht
  simpa only [ht] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Hecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPointC1_section_cover_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x (cubicThetaSectionPointC1 F.val F.property.1)‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  simp_rw [cubicThetaSectionPointC1_gradient,cubicThetaSectionGradient_norm_sq]
  exact cubicThetaPrimeCubeInvariant_integrable hp (cubicThetaPrimeCubeFinite_energy_domain F)
    (cubicThetaC1Energy_invariant F.val F.property.1)

lemma cubicThetaPointC1_dilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x
      (cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
        (cubicThetaSectionPointC1 F.val F.property.1))‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  simp_rw [cubicThetaPointC1Pullback_gradient_norm,cubicThetaSectionPointC1_gradient,
    cubicThetaSectionGradient_norm_sq]
  exact cubicThetaPrimeCubeScalarDilation_integrable hp (cubicThetaPrimeCubeFinite_energy_domain F)
    (cubicThetaC1Energy_invariant F.val F.property.1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBranchFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero horizontal observations of the actual four Hecke branches. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeDilation_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient (p^3*h) (fun z =>
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        cubicThetaHorizontalPoint v hv z))=
      cubicThetaSectionFourier F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv) h := by
  have he : (fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z))=
      (fun z => cubicThetaSectionHorizontal F (‖(p:ℂ)‖^3*v)
        (mul_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) hv)
        ((p^3:Eisenstein)*z)) := by
    funext z
    rw [cubicThetaPrimeCubeDilation_horizontal_point hp]
    rfl
  rw [he]
  exact cubicThetaHorizontalFourier_dilate _ (cubicThetaSectionHorizontal_periodic F _ _)
    (pow_ne_zero _ hp.2.ne_zero) h (cubicThetaHorizontalFourier_integrable h _
      (cubicThetaSectionHorizontal F _ _).continuous)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReciprocalNormalizer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeReciprocalNormalizer_lower {p : Eisenstein} (hp : primaryPrime p) :
    p^3∣(cubicThetaPrimeCubeReciprocalNormalizer hp).val 1 0 := by
  have he : (cubicThetaPrimeCubeReciprocalNormalizer hp).val 1 0=
      -(cubicThetaPrimeCubeWeyl hp).val 1 1 := by
    change (Matrix.adjugate (((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein)*
      !![0,-1;1,0])) 1 0= -((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein) 1 1
    simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  rw [he,cubicThetaPrimeCubeWeyl_d]
  exact dvd_neg.mpr (cubicThetaPrimeCubeWeylDenominator_dvd hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReciprocalGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal geometry and multiplier identities for the literal
cubed-prime correspondence. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeReciprocalNormalizer_conjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g=
      cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g*
        (cubicThetaPrimeCubeWeyl hp)⁻¹ := by
  apply Subtype.ext
  change (((cubicThetaPrimeCubeWeyl hp).val*cubicThetaFullInversion)⁻¹)⁻¹*g.val*
    ((cubicThetaPrimeCubeWeyl hp).val*cubicThetaFullInversion)⁻¹=
    (cubicThetaPrimeCubeWeyl hp).val*
      ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹)*
      (cubicThetaPrimeCubeWeyl hp).val⁻¹
  group

lemma cubicThetaPrimeCubeReciprocalNormalizer_character {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g)=
      cubicThetaKubotaValue g := by
  rw [cubicThetaPrimeCubeReciprocalNormalizer_conjugate,cubicThetaKubotaValue_mul,
    cubicThetaKubotaValue_mul,cubicThetaInversionConjugate_character]
  have he : cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)⁻¹=1 := by
    change cubicThetaKubotaCharacter (cubicThetaPrimeCubeWeyl hp)*
      cubicThetaKubotaCharacter ((cubicThetaPrimeCubeWeyl hp)⁻¹)=1
    rw [←map_mul,mul_inv_cancel,map_one]
  calc
    _ = cubicThetaKubotaValue g*(cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)⁻¹) := by ring
    _ = _ := by rw [he,mul_one]

lemma cubicThetaPrimeCube_reciprocal_point {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (g • (cubicThetaFullInversion • x)))=
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
        (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g • x) := by
  rw [cubicThetaPrimeCube_inversion_dilation hp,cubicThetaInversion_intertwine,
    cubicThetaFullInversion_involutive]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSelfAdjointSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal coset permutation identifies the actual adjoint
correspondence with the original cubed-prime operator. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_reciprocal_term {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    star (cubicThetaKubotaValue g)*F.val (cubicThetaFullInversion •
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (g • (cubicThetaFullInversion • x))))=
      star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
        cubicThetaPrimeCubeTraceTerm p (cubicThetaPrimeCubeDilationSection hp F)
          (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g)
          (cubicThetaPrimeCubeWeyl hp • x) := by
  have hg : cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g=
      cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g*cubicThetaPrimeCubeWeyl hp := by
    rw [cubicThetaPrimeCubeReciprocalNormalizer_conjugate]
    group
  have hx : cubicThetaPrimeCubeWeyl hp •
      (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g • x)=
      cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g •
        (cubicThetaPrimeCubeWeyl hp • x) := by
    rw [←mul_smul,hg,mul_smul]
  rw [cubicThetaPrimeCube_reciprocal_point hp,cubicThetaPrimeCube_inverse_section hp,hx]
  unfold cubicThetaPrimeCubeTraceTerm
  rw [cubicThetaPrimeCubeReciprocalNormalizer_character]
  change star (cubicThetaKubotaValue g) *
      (star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)) *
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g •
            (cubicThetaPrimeCubeWeyl hp • x)))) =
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)) *
      (star (cubicThetaKubotaValue g) *
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrincipalConjugate (cubicThetaPrimeCubeReciprocalNormalizer hp) g •
            (cubicThetaPrimeCubeWeyl hp • x))))
  ring

theorem cubicThetaPrimeCubeHecke_inversion_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaInversionSection (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection F))=
      cubicThetaPrimeCubeHecke hp F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection F)).val
    (cubicThetaFullInversion • x)=(cubicThetaPrimeCubeHecke hp F).val x
  rw [cubicThetaPrimeCubeHecke_apply]
  change (∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
    F.val (cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (t.val • (cubicThetaFullInversion • x)))))=_
  simp_rw [cubicThetaPrimeCube_reciprocal_term hp]
  rw [tsum_mul_left,cubicThetaPrimeCubeTrace_normalizer hp _ (cubicThetaPrimeCubeReciprocalNormalizer_lower hp)]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    (cubicThetaPrimeCubeHecke hp F).val (cubicThetaPrimeCubeWeyl hp • x)=_
  rw [(cubicThetaPrimeCubeHecke hp F).property,←mul_assoc]
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  rw [hu,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeEnergyValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility of the completed prime energy graph with the actual
automorphic L2 space, its Atkin action, and the normalized original lift. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGlobalEnergyValueMap : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaGlobalInclusion.codRestrict _ cubicThetaGlobalInclusion_mem

lemma cubicThetaGlobalEnergyValueMap_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F)=cubicThetaGlobalMassClosure F := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeMassOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
def cubicThetaFiniteMassClosure : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaGlobalEnergyValueMap.toLinearMap.comp cubicThetaFiniteEnergyEmbedding

lemma cubicThetaFiniteMassClosure_dense : DenseRange cubicThetaFiniteMassClosure := by
  have he : (fun F : cubicThetaSmoothTests =>
      cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy F))=
      (fun F => cubicThetaGlobalMassClosure F) := rfl
  have hd : DenseRange (fun F : cubicThetaSmoothTests =>
      cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy F)) := by
    rw [he]
    exact cubicThetaGlobalMassClosure_dense
  exact hd.of_comp

def cubicThetaPrimeCubeRawMass {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaFiniteMassClosure.comp (cubicThetaPrimeCubeHeckeFiniteLinear hp)

lemma cubicThetaPrimeCubeRawMass_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaPrimeCubeRawMass hp F‖≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
      ‖cubicThetaFiniteMassClosure F‖ := by
  change ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F)‖≤
    ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*‖cubicThetaFiniteEnergyValue F‖
  apply _root_.le_of_sq_le_sq _ (mul_nonneg (Nat.cast_nonneg _) (_root_.norm_nonneg _))
  simpa only [mul_pow] using cubicThetaPrimeCubeHeckeFinite_value_bound hp F

def cubicThetaPrimeCubeHeckeMass {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →L[ℂ] cubicThetaAutomorphicL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (cubicThetaPrimeCubeRawMass hp) cubicThetaFiniteMassClosure

lemma cubicThetaPrimeCubeHeckeMass_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaFiniteMassClosure F)=
      cubicThetaFiniteMassClosure (cubicThetaPrimeCubeHeckeFinite hp F) :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeCubeRawMass hp) (e:=cubicThetaFiniteMassClosure)
    cubicThetaFiniteMassClosure_dense
    ⟨((cubicThetaPrimeIwahori (p^3)).index:ℝ),cubicThetaPrimeCubeRawMass_bound hp⟩ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMeanIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of height in the literal v^-3 radial mean integral. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSectionMean_weight_integrable (F : cubicThetaFiniteEnergySections)
    (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionMean F v) (Ioi (2:ℝ)) := by
  have hi := cubicThetaSectionMeanPairing_integrable F W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have h := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable 2)
    (fun y => star (W y.2)*cubicThetaSectionFunction F y)).mp hi'
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at h
  change Integrable (fun y : ℂ × ℝ => star (W y.2)*cubicThetaSectionFunction F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at h
  rw [←Measure.prod_restrict] at h
  apply h.integral_prod_right.congr
  filter_upwards with v
  dsimp only [cubicThetaSectionMean]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRadialPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRadialPairing_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(p:ℂ)‖^3, W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
        (cubicThetaFiniteCuspRestriction (cubicThetaPrimeCubeHeckeFinite hp F))=
      inner ℂ (cubicThetaCuspFourierTest 0
        (cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3) (by
          have := cubicThetaPrimeCube_height_ge_one hp; linarith) W))
        (cubicThetaFiniteCuspRestriction F) := by
  let r := ‖(p:ℂ)‖^3
  have hr1 : 1 ≤ r := cubicThetaPrimeCube_height_ge_one hp
  have hr : 0 < r := by linarith
  have hW2 : ∀ v≤(2:ℝ), W v=0 := by
    intro v hv
    apply hW
    change v≤2*r
    linarith
  let A := cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W
  let B := cubicThetaRadialWeightScale r hr W
  have hA : ∀ v≤(2:ℝ), A v=0 := by
    intro v hv
    change W (r⁻¹*v)=0
    apply hW
    change r⁻¹*v≤2*r
    rw [mul_comm,←div_eq_mul_inv,div_le_iff₀ hr]
    have : 1 ≤ r*r := by nlinarith
    nlinarith
  have hB : ∀ v≤(2:ℝ), B v=0 := by
    intro v hv
    change W (r*v)=0
    apply hW
    change r*v≤2*r
    nlinarith
  have hiA := cubicThetaRadialIntegral_integrable_zero_extension A hA
    (cubicThetaSectionMean F) (cubicThetaSectionMean_weight_integrable F A)
  have hiB := cubicThetaRadialIntegral_integrable_zero_extension B hB
    (cubicThetaSectionMean F) (cubicThetaSectionMean_weight_integrable F B)
  have hiA' : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*cubicThetaSectionMean F v) (Ioi (0:ℝ)) := by
    simpa only [A,cubicThetaRadialWeightScale_apply,mul_comm r⁻¹,←div_eq_mul_inv] using hiA
  have hiB' : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*cubicThetaSectionMean F v) (Ioi (0:ℝ)) := hiB
  have hnorm : (norm (p^3):ℂ)=(r:ℂ)^2 := by
    rw [cubicThetaPrimeCube_norm_power]
    dsimp only [r]
    push_cast
    ring
  rw [cubicThetaSectionMeanPairing_hecke,cubicThetaSectionMeanPairing,hnorm]
  change (∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
    (cubicThetaSectionMean F (r*v)+(r:ℂ)^2*cubicThetaSectionMean F (v/r)))=
    ∫ v in Ioi (2:ℝ),star (cubicThetaRadialHeckeWeight r hr W v)/(v:ℂ)^3*cubicThetaSectionMean F v
  rw [cubicThetaRadialIntegral_zero_extension W hW2,
    cubicThetaRadialIntegral_zero_extension _ (cubicThetaPrimeCubeRadialWeight_low hp W hW),
    cubicThetaRadialIntegral_hecke r hr W _ hiA' hiB',
    cubicThetaRadialHeckeWeight_integral r hr W _ hiA' hiB']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite cubic root preserves the actual finite-domain norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment


lemma cubicThetaPrimeCubeRootWeylImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeCubeRootWeylElement hp • y) ''
        cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeCubeRootWeylElement hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeCubeRootWeylElement hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCubeRootWeylConjugate_involutive hp).toPerm
  intro g y
  change cubicThetaPrimeCubeRootWeylElement hp • ((cubicThetaPrimeCubeRootWeylConjugate hp g).val • y)=
    g.val • (cubicThetaPrimeCubeRootWeylElement hp • y)
  rw [cubicThetaPrimeCubeRootWeylPoint_intertwines,cubicThetaPrimeCubeRootWeylConjugate_involutive]

theorem cubicThetaPrimeCubeRootWeylSection_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) :
    (∫ y in cubicThetaPrimeCubeRootCoverDomain hp,
      ‖(cubicThetaPrimeCubeRootWeylSection hp F).val y‖^2 ∂cubicThetaPointMeasure)=
        ∫ y in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val y‖^2 ∂cubicThetaPointMeasure := by
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootWeylImage_fundamental hp) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeRootWeylElement hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootWeylElement hp))
      (fun y => ‖F.val y‖^2) (cubicThetaPrimeCubeRootCoverDomain hp)
  exact (hi.trans hc).symm

theorem cubicThetaPrimeCubeRootWeylSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p)
    (hF : MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))) :
    MemLp (cubicThetaPrimeCubeRootWeylSection hp F).val 2
      (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)) := by
  have hf := (memLp_two_iff_integrable_sq_norm F.val.continuous.aestronglyMeasurable).mp hF
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootWeylImage_fundamental hp) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hImage := hi.mp hf
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaPrimeCubeRootWeylSection hp F).val.continuous.aestronglyMeasurable).mpr
  exact ((measurePreserving_smul (cubicThetaPrimeCubeRootWeylElement hp) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootWeylElement hp))).mp hImage


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric opposite-root action on the actual cubic-scale completion. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubeRootWeyl_finiteGroup
def cubicThetaPrimeCubeRootFiniteWeyl {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeCubeRootWeylSection hp F.val,
    cubicThetaPrimeCubeRootWeylSection_memLp hp F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootFiniteWeyl_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteWeyl hp F)‖=
      ‖cubicThetaPrimeCubeRootFiniteEmbedding hp F‖ := by
  change ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootFiniteWeyl hp F)‖=
    ‖cubicThetaPrimeCubeRootFiniteValue hp F‖
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeCubeRootSectionL2_norm_sq,cubicThetaPrimeCubeRootSectionL2_norm_sq]
  exact cubicThetaPrimeCubeRootWeylSection_mass hp F.val

def cubicThetaPrimeCubeRootWeylL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootFiniteWeyl hp)).extendOfIsometry
    (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp) (cubicThetaPrimeCubeRootFiniteWeyl_norm hp)

lemma cubicThetaPrimeCubeRootWeylL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteWeyl hp F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylGlobal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual twice-cubically-dilated global branch and its invariance
under all cubic-scale translations. -/
noncomputable section
namespace CubicFirstMoment


lemma cubicThetaPrimeCubeRootWeyl_finite_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteTranslate hp x
      (cubicThetaPrimeCubeRootFiniteWeyl hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))=
        cubicThetaPrimeCubeRootFiniteWeyl hp (cubicThetaPrimeCubeRootSmoothRestriction hp F) := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootWeyl_global_translate hp x F.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unit-branch transport on the cubic-scale Hilbert completion.
There is no arithmetic-residue or Hecke-eigenvector hypothesis here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFinite_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteWeyl hp (cubicThetaPrimeCubeRootFiniteTranslate hp y
      (cubicThetaPrimeCubeRootSmoothRestriction hp F))=
      cubicThetaPrimeCubeRootFiniteTranslate hp (-x)
        (cubicThetaPrimeCubeRootSmoothRestriction hp (cubicThetaInversionSmooth F)) := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootWeyl_translated_global hp x y hxy F.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootStripBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRoot_strip_lintegral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) :
    (∫⁻ x in cubicThetaCuspStrip 2,‖(‖F.val x‖^2:ℝ)‖ₑ ∂cubicThetaPointMeasure)≤
      ∫⁻ x in cubicThetaPrimeCubeRootCoverDomain hp,‖(‖F.val x‖^2:ℝ)‖ₑ ∂cubicThetaPointMeasure := by
  apply cubicThetaInjective_subgroup_lintegral_le (cubicThetaPrimeCubeRootCoverGroup hp)
    (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure)
    (cubicThetaPrimeCubeRootCoverDomain_measurable hp) (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num))
  intro g x
  rw [cubicThetaPrimeCubeRootSection_norm_invariant hp F g x]

lemma cubicThetaPrimeCubeRoot_strip_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    MemLp F.val.val 2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  apply (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mpr
  refine ⟨(F.val.val.continuous.norm.pow 2).aestronglyMeasurable,?_⟩
  have hf := (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mp F.property
  exact lt_of_le_of_lt (cubicThetaPrimeCubeRoot_strip_lintegral_le hp F.val) hf.hasFiniteIntegral

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

attribute [local instance] OAI.CubicFirstMoment.cubeRootCuspFinite_addCommGroup
def cubicThetaPrimeCubeRootFiniteCuspRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] CubicThetaStripL2 where
  toFun F := (cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _
  map_add' F G := MemLp.toLp_add (cubicThetaPrimeCubeRoot_strip_memLp hp F)
    (cubicThetaPrimeCubeRoot_strip_memLp hp G)
  map_smul' c F := MemLp.toLp_const_smul c (cubicThetaPrimeCubeRoot_strip_memLp hp F)

lemma cubicThetaPrimeCubeRootFiniteCuspRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteCuspRestriction hp F‖^2=
      ∫ x in cubicThetaCuspStrip 2,‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaPrimeCubeRoot_strip_memLp hp F).coeFn_toLp] with x hx
  change ‖((cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _) x‖^2=_
  rw [hx]

lemma cubicThetaPrimeCubeRootFiniteCuspRestriction_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteCuspRestriction hp F‖≤
      ‖cubicThetaPrimeCubeRootFiniteEmbedding hp F‖ := by
  have hf := (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mp F.property
  have hi := cubicThetaPrimeCubeRoot_strip_lintegral_le hp F.val
  simp_rw [Real.enorm_eq_ofReal (sq_nonneg _)] at hi
  have hfin : (∫⁻ x in cubicThetaPrimeCubeRootCoverDomain hp,
      ENNReal.ofReal (‖F.val.val x‖^2) ∂cubicThetaPointMeasure)≠⊤ := by
    simpa only [hasFiniteIntegral_iff_enorm,Real.enorm_eq_ofReal (sq_nonneg _)] using hf.hasFiniteIntegral.ne
  have hr := ENNReal.toReal_mono hfin hi
  rw [←integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (F.val.val.continuous.norm.pow 2).aestronglyMeasurable,
    ←integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (F.val.val.continuous.norm.pow 2).aestronglyMeasurable] at hr
  rw [←cubicThetaPrimeCubeRootFiniteCuspRestriction_norm_sq,
    ←cubicThetaPrimeCubeRootSectionL2_norm_sq] at hr
  change ‖cubicThetaPrimeCubeRootFiniteCuspRestriction hp F‖^2≤
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp F‖^2 at hr
  nlinarith [_root_.norm_nonneg (cubicThetaPrimeCubeRootFiniteCuspRestriction hp F),
    _root_.norm_nonneg (cubicThetaPrimeCubeRootFiniteEmbedding hp F)]

def cubicThetaPrimeCubeRootCuspRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootAutomorphicL2 hp →L[ℂ] CubicThetaStripL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaPrimeCubeRootFiniteSections hp)
    (Eₗ:=cubicThetaPrimeCubeRootAutomorphicL2 hp) (F:=CubicThetaStripL2)
    (cubicThetaPrimeCubeRootFiniteCuspRestriction hp) (cubicThetaPrimeCubeRootFiniteEmbedding hp)

lemma cubicThetaPrimeCubeRootCuspRestriction_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootCuspRestriction hp (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteCuspRestriction hp F := by
  apply LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaPrimeCubeRootFiniteCuspRestriction hp) (e:=cubicThetaPrimeCubeRootFiniteEmbedding hp)
    (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp)
  exact ⟨1,fun G => by simpa only [one_mul] using cubicThetaPrimeCubeRootFiniteCuspRestriction_bound hp G⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCuspLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRootFiniteCuspRestriction_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteCuspRestriction hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)=
      cubicThetaFiniteCuspRestriction (cubicThetaSmoothToFiniteEnergy F) := by
  exact MemLp.toLp_congr
    (cubicThetaPrimeCubeRoot_strip_memLp hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))
    (cubicThetaFiniteEnergy_strip_memLp (cubicThetaSmoothToFiniteEnergy F))
    (Filter.Eventually.of_forall (fun _ => rfl))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite Fourier averages at the cube modulus, on sections
and on their completed domain space. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

set_option synthInstance.maxHeartbeats 400000 in
def cubicThetaPrimeCubeRootFiniteFourier {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) : cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeCubeRootFiniteSections hp := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  exact (norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
    star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
      cubicThetaPrimeCubeRootFiniteTranslate hp (residueRepresentative (p^3) r)

lemma cubicThetaPrimeCubeRootFiniteFourier_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootFiniteFourier hp k F=(norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
      star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
        cubicThetaPrimeCubeRootFiniteTranslate hp (residueRepresentative (p^3) r) F := by
  classical
  simp only [cubicThetaPrimeCubeRootFiniteFourier,LinearMap.smul_apply,LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

lemma cubicThetaPrimeCubeRootFourierL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteFourier hp k F) := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  rw [cubicThetaPrimeCubeRootFourierL2_apply,cubicThetaPrimeCubeRootFiniteFourier_apply,
    map_smul,map_sum]
  simp only [map_smul,cubicThetaPrimeCubeRootResidueL2,cubicThetaPrimeCubeRootTranslateL2_finite]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootHorizontal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRootFiniteFourier_value {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3))
    (F : cubicThetaPrimeCubeRootFiniteSections hp) (y : CubicThetaPoint) :
    (cubicThetaPrimeCubeRootFiniteFourier hp k F).val.val y=
      (norm (p^3):ℂ)⁻¹*∑ r : Residues (p^3),
        star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
          (cubicThetaPrimeCubeRootSectionTranslate hp (residueRepresentative (p^3) r) F.val).val y := by
  let ev : cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] ℂ :=
    { toFun := fun G => G.val.val y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change ev (cubicThetaPrimeCubeRootFiniteFourier hp k F)=_
  rw [cubicThetaPrimeCubeRootFiniteFourier_apply,map_smul,map_sum]
  rfl

lemma cubicThetaPrimeCubeRootFiniteFourier_horizontal_function {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp)
    (v : ℝ) (hv : 0<v) :
    (cubicThetaPrimeRootHorizontal (cubicThetaPrimeCubeRootFiniteFourier hp k F).val v hv : ℂ → ℂ)=
      fun z => (norm (p^3):ℂ)⁻¹*∑ r : Residues (p^3),
        star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
          cubicThetaPrimeRootHorizontal F.val v hv
            (z+3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ)) := by
  classical
  funext z
  change (cubicThetaPrimeCubeRootFiniteFourier hp k F).val.val (cubicThetaHorizontalPoint v hv z)=_
  rw [cubicThetaPrimeCubeRootFiniteFourier_value]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [show (cubicThetaPrimeCubeRootSectionTranslate hp (residueRepresentative (p^3) r) F.val).val
      (cubicThetaHorizontalPoint v hv z)=_ from
    cubicThetaPrimeCubeRootHorizontal_translate hp F.val (residueRepresentative (p^3) r) v hv z]

theorem cubicThetaPrimeCubeRootFiniteFourier_horizontal {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootFiniteSections hp)
    (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h
      (cubicThetaPrimeRootHorizontal (cubicThetaPrimeCubeRootFiniteFourier hp k F).val v hv)=
      if Ideal.Quotient.mk (modulus (p^3)) h=k then
        cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeRootHorizontal F.val v hv)
      else 0 := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let f := cubicThetaPrimeRootHorizontal F.val v hv
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  let c := cubicThetaHorizontalFourierCoefficient h f
  have hphase (r : Residues (p^3)) :
      cubicThetaHorizontalCharacter h (3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ))=
        ψ (r*Ideal.Quotient.mk (modulus (p^3)) h) := by
    rw [cubicThetaHorizontalCharacter_fraction h (p^3) _ (pow_ne_zero 3 hp.2.ne_zero),
      map_mul,residueRepresentative_spec,mul_comm]
  have hterm (r : Residues (p^3)) :
      cubicThetaHorizontalFourierCoefficient h (fun z => star (ψ (k*r))*
        f (z+3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ)))=
        star (ψ (k*r))*(ψ (r*Ideal.Quotient.mk (modulus (p^3)) h)*c) := by
    rw [cubicThetaHorizontalFourier_const_mul]
    rw [cubicThetaHorizontalFourier_translate h f (cubicThetaPrimeRootHorizontal_periodic F.val v hv)]
    rw [hphase]
  rw [cubicThetaPrimeCubeRootFiniteFourier_horizontal_function,cubicThetaHorizontalFourier_const_mul]
  change (norm (p^3):ℂ)⁻¹*cubicThetaHorizontalFourierCoefficient h
    (fun z => ∑ r : Residues (p^3),star (ψ (k*r))*
      f (z+3*(residueRepresentative (p^3) r:ℂ)/((p^3:Eisenstein):ℂ)))=_
  rw [cubicThetaHorizontalFourier_sum Finset.univ h _ (by
    intro r _
    exact continuous_const.mul (f.continuous.comp (continuous_id.add continuous_const)))]
  simp only [hterm]
  change (norm (p^3):ℂ)⁻¹*(∑ r : Residues (p^3),star (ψ (k*r))*
    (ψ (r*Ideal.Quotient.mk (modulus (p^3)) h)*c))=_
  rw [cubicThetaCubeResidueFourier_sum hp]
  split_ifs <;> simp [Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne',c,f]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCuspObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

def cubicThetaPrimeCubeRootObservation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) : cubicThetaPrimeCubeRootAutomorphicL2 hp →L[ℂ] ℂ :=
  (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp (cubicThetaPrimeCubeRootCuspRestriction hp)

lemma cubicThetaPrimeCubeRootFinite_observation_integral {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      ∫ x in cubicThetaCuspStrip 2,star (W x.val.2*cubicThetaHorizontalCharacter h x.val.1)*
        F.val.val x ∂cubicThetaPointMeasure := by
  change inner ℂ (cubicThetaCuspFourierTest h W)
    (cubicThetaPrimeCubeRootCuspRestriction hp (cubicThetaPrimeCubeRootFiniteEmbedding hp F))=_
  rw [cubicThetaPrimeCubeRootCuspRestriction_finite,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaPrimeCubeRoot_strip_memLp hp F).coeFn_toLp] with x hx hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) x)
    (((cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _) x)=_
  rw [hx,hF,RCLike.inner_apply]
  simp only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter]
  ring

lemma cubicThetaPrimeCubeRootFinite_observation_iterated {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
        cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaPrimeCubeRootFunction F.val (z,v)) := by
  have hi : IntegrableOn (fun x : CubicThetaPoint =>
      star (W x.val.2*cubicThetaHorizontalCharacter h x.val.1)*F.val.val x)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    have he := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W)
      (cubicThetaPrimeCubeRootFiniteCuspRestriction hp F)
    apply he.congr
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaPrimeCubeRoot_strip_memLp hp F).coeFn_toLp] with x hx hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) x)
      (((cubicThetaPrimeCubeRoot_strip_memLp hp F).toLp _) x)=_
    rw [hx,hF,RCLike.inner_apply]
    simp only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter]
    ring
  have hi' : IntegrableOn (fun x : CubicThetaPoint =>
      star (W x.val.2*cubicThetaHorizontalCharacter h x.val.1)*
        cubicThetaPrimeCubeRootFunction F.val x.val) (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    simpa only [cubicThetaPrimeCubeRootFunction_coordinates] using hi
  rw [cubicThetaPrimeCubeRootFinite_observation_integral]
  have he := cubicThetaCuspStrip_fubini (fun y =>
    star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaPrimeCubeRootFunction F.val y) hi'
  simp only [cubicThetaPointCoordinates,cubicThetaPrimeCubeRootFunction_coordinates] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  unfold cubicThetaHorizontalFourierCoefficient
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionFourierPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual weighted observations at every horizontal frequency, obtained
by Fubini on the geometric cusp strip. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaSectionFourierPairing (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaFiniteCuspRestriction F)=
      ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v := by
  have hi := cubicThetaSectionFourierPairing_integrable F h W
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
        cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have he := cubicThetaCuspStrip_fubini
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*
      cubicThetaSectionFunction F y) hi'
  have hpair : inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaFiniteCuspRestriction F)=
      ∫ p in cubicThetaCuspStrip 2,
        star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
          cubicThetaSectionFunction F p.val ∂cubicThetaPointMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
      (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
    change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
      (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
    rw [hW,hF,cubicThetaSectionFunction_coordinates]
    simpa only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter] using
      (RCLike.inner_apply' (cubicThetaCuspFourierWeight h W p) (F.val.val p))
  change (∫ p in cubicThetaCuspStrip 2,
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
      cubicThetaSectionFunction F p.val ∂cubicThetaPointMeasure)=
    ∫ v in Ioi (2:ℝ),∫ z in cubicThetaHorizontalCell,
      star (W v*cubicThetaHorizontalCharacter h z)*cubicThetaSectionFunction F (z,v)/(v:ℂ)^3 at he
  rw [hpair,he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaSectionFourierFunction,cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootObservationProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier support rule survives completion and all bounded
cusp observations. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFinite_observation_projection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootObservation hp h W
      (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteFourier hp k F))=
    if Ideal.Quotient.mk (modulus (p^3)) h=k then
      cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFiniteEmbedding hp F) else 0 := by
  rw [cubicThetaPrimeCubeRootFinite_observation_iterated]
  by_cases hk : Ideal.Quotient.mk (modulus (p^3)) h=k
  · rw [ite_eq_left hk,cubicThetaPrimeCubeRootFinite_observation_iterated]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    have hpos : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hv
    rw [cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos,
      cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos,
      cubicThetaPrimeCubeRootFiniteFourier_horizontal,ite_eq_left hk]
  · rw [ite_eq_right hk]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    have hpos : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hv
    rw [cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos,
      cubicThetaPrimeCubeRootFiniteFourier_horizontal,ite_eq_right hk,mul_zero]

theorem cubicThetaPrimeCubeRoot_observation_projection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFourierL2 hp k u)=
    if Ideal.Quotient.mk (modulus (p^3)) h=k then cubicThetaPrimeCubeRootObservation hp h W u else 0 := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootObservation hp h W).continuous.comp
      (cubicThetaPrimeCubeRootFourierL2 hp k).continuous)
      (by split_ifs <;> fun_prop)) ?_
  intro F
  rw [cubicThetaPrimeCubeRootFourierL2_finite]
  exact cubicThetaPrimeCubeRootFinite_observation_projection hp k h W F

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

lemma cubicThetaPrimeCubeRootFinite_observation_dilation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootObservation hp (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W)
      (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F))=
      ((‖(p:ℂ)‖^3:ℝ):ℂ)^2*inner ℂ (cubicThetaCuspFourierTest h W)
        (cubicThetaFiniteCuspRestriction (cubicThetaSmoothToFiniteEnergy F)) := by
  rw [cubicThetaPrimeCubeRootFinite_observation_iterated,cubicThetaSectionFourierPairing]
  calc
    _ = ∫ v in Ioi (2:ℝ),star (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W v)/(v:ℂ)^3*
          cubicThetaSectionFourierFunction F h (‖(p:ℂ)‖^3*v) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      have hpos : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hv
      congr 1
      rw [cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos]
      change cubicThetaHorizontalFourierCoefficient (p^3*h) (fun z =>
        F.val.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          cubicThetaHorizontalPoint v hpos z))=_
      rw [cubicThetaPrimeCubeDilation_fourier hp,←cubicThetaSectionFourierFunction_eq]
    _ = _ := cubicThetaRadialIntegral_scaled_weight (‖(p:ℂ)‖^3)
      (cubicThetaPrimeCube_height_one hp) W hW (cubicThetaSectionFourierFunction F h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFourierNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of the actual cubic-scale Fourier projection is the
Fourier transform of its translation correlations. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootFourierL2_norm_correlation {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3))
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    (‖cubicThetaPrimeCubeRootFourierL2 hp k u‖^2:ℂ)=
      (norm (p^3):ℂ)⁻¹*∑ r : Residues (p^3),
        star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))*
          inner ℂ u (cubicThetaPrimeCubeRootResidueL2 hp r u) := by
  calc
    _ = inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp k u)
        (cubicThetaPrimeCubeRootFourierL2 hp k u) :=
      (inner_self_eq_norm_sq_to_K (𝕜:=ℂ) _).symm
    _ = inner ℂ u (cubicThetaPrimeCubeRootFourierL2 hp k u) :=
      cubicThetaPrimeCubeRootFourierL2_pair_projection hp k u u
    _ = _ := by
      rw [cubicThetaPrimeCubeRootFourierL2_apply,
        inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),inner_sum]
      simp only [inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverDegree
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem cubicThetaPrimeRootCoverProjection_measure {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeRootCoverMeasure hp).map (cubicThetaPrimeRootCoverProjection hp)=
      ((cubicThetaPrimeRootCoverGroup hp).index : ℝ≥0∞) • cubicThetaQuotientMeasure := by
  let : Fintype (cubicThetaPrimeRootTransversal hp) := Fintype.ofFinite _
  have hdis : Pairwise (fun t u : cubicThetaPrimeRootTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
    intro t u htu
    exact cubicThetaFundamentalDomain_translates_disjoint
      (fun he => htu (Subtype.ext he))
  have hmeas (t : cubicThetaPrimeRootTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
      cubicThetaFundamentalDomain_measurable
  rw [cubicThetaPrimeRootCoverMeasure,
    Measure.map_map (cubicThetaPrimeRootCoverProjection_continuous hp).measurable
      (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable]
  change (cubicThetaPointMeasure.restrict (⋃ t : cubicThetaPrimeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)).map
      cubicThetaQuotientMap=_
  rw [Measure.restrict_iUnion hdis hmeas,
    Measure.map_sum cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  simp_rw [cubicThetaFundamentalDomain_translate_map]
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.smul_apply,tsum_fintype,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeRootTransversal_complement hp).card_right]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootRestrictionBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the root-average contraction to actual global sections. The
finite-cover degree supplies the exact normalization of their square norm. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

theorem cubicThetaPrimeRootSectionRestrict_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionRestrict F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)=
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*
        ∫ q, (cubicThetaSectionNorm F q)^2 ∂cubicThetaQuotientMeasure := by
  simp_rw [cubicThetaPrimeRootSectionRestrict_norm]
  have hi := integral_map_of_stronglyMeasurable (μ:=cubicThetaPrimeRootCoverMeasure hp)
    (cubicThetaPrimeRootCoverProjection_continuous hp).measurable
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  simp only [Pi.pow_apply] at hi
  rw [←hi,cubicThetaPrimeRootCoverProjection_measure hp,integral_smul_measure]
  simp only [ENNReal.toReal_natCast,smul_eq_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootRestrictionL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original automorphic L2 norm acquires exactly the finite-cover
degree under restriction to the root cover. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionRestrict_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootSectionRestrict F))
      2 (cubicThetaPrimeRootCoverMeasure hp) := by
  apply (memLp_norm_iff
    (cubicThetaPrimeRootSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaSectionRepresentative_norm] at hn
  have hs := hn.smul_measure
    (by simp : ((cubicThetaPrimeRootCoverGroup hp).index:ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeRootCoverProjection_measure hp] at hs
  have hc := hs.comp_of_map (cubicThetaPrimeRootCoverProjection_continuous hp).measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRepresentative_norm,
    cubicThetaPrimeRootSectionRestrict_norm] using hc

theorem cubicThetaPrimeRootSectionRestrict_L2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaPrimeRootSectionRestrict_memLp hp F hF).toLp
      (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootSectionRestrict F))‖^2=
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*‖hF.toLp (cubicThetaSectionRepresentative F)‖^2 := by
  rw [cubicThetaPrimeRootSectionL2_norm_sq,cubicThetaSectionL2_norm_sq]
  exact cubicThetaPrimeRootSectionRestrict_mass hp F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.rootLift_smoothGroup
def cubicThetaPrimeRootSmoothRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootSectionRestrict F.val,
    cubicThetaPrimeRootSectionRestrict_memLp hp F.val (cubicThetaSectionRepresentative_memLp F)⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeRootSmoothRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F)‖^2=
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 :=
  cubicThetaPrimeRootSectionRestrict_L2_norm_sq hp F.val (cubicThetaSectionRepresentative_memLp F)

def cubicThetaPrimeRootNormalizedRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeRootFiniteEmbedding hp).comp (cubicThetaPrimeRootSmoothRestriction hp))

lemma cubicThetaPrimeRootNormalizedRestriction_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeRootNormalizedRestriction hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeRootCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeRootCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeRootSmoothRestriction_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeRootLiftL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  (cubicThetaPrimeRootNormalizedRestriction hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeRootNormalizedRestriction_norm hp)

lemma cubicThetaPrimeRootLiftL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootLiftL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeRootNormalizedRestriction hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhatMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each nonzero Bruhat branch acts by its actual cubic multiplier
on the completed global mass space. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootFinite_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootFiniteResidue hp r
      (cubicThetaPrimeRootSmoothRestriction hp F))=
      (cubicSymbol p 3*cubicResidueChar p hp r) •
        cubicThetaPrimeRootFiniteResidue hp (-cubicThetaPrimeRootReciprocal p r)
          (cubicThetaPrimeRootSmoothRestriction hp (cubicThetaInversionSmooth F)) := by
  apply Subtype.ext
  exact cubicThetaPrimeRootWeyl_residue_branch hp r hr F.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootPairingL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaPrimeRootSmoothWeyl_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F))
      (cubicThetaPrimeRootWeylL2 hp
        (cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp G)))=0 := by
  rw [cubicThetaPrimeRootWeylL2_finite,cubicThetaPrimeRootSectionPairing_L2,
    cubicThetaPrimeRootSectionPairing_unfold]
  exact cubicThetaPrimeRootSquare_pair_integral_zero hp F.val G.val

theorem cubicThetaPrimeRootLiftWeyl_orthogonal {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  apply cubicThetaGlobalMassClosure_dense.induction_on₂
    (p:=fun u v => inner ℂ (cubicThetaPrimeRootLiftL2 hp u)
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp v))=0) ?_ ?_ u v
  · apply isClosed_eq _ continuous_const
    exact ((cubicThetaPrimeRootLiftL2 hp).continuous.comp continuous_fst).inner
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp
        ((cubicThetaPrimeRootLiftL2 hp).continuous.comp continuous_snd))
  · intro F G
    simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
      LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
    rw [inner_smul_left,
      inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp),
      cubicThetaPrimeRootSmoothWeyl_orthogonal,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylFixed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained twice-dilated branch is fixed by the root group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_finite_translate {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFiniteResidue hp r
      (cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F))=
        cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootSmoothRestriction hp F) := by
  apply Subtype.ext
  exact cubicThetaPrimeRootWeyl_global_translate hp (residueRepresentative p r) F.val

theorem cubicThetaPrimeRootWeyl_lift_translate {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootResidueL2 hp r
      (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))=
        cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeRootResidueL2 hp r).continuous.comp
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp (cubicThetaPrimeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeRootWeylL2 hp).continuous.comp (cubicThetaPrimeRootLiftL2 hp).continuous)) ?_
  intro F
  simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeRootWeylL2_finite,
    cubicThetaPrimeRootResidueL2_finite,cubicThetaPrimeRootWeyl_finite_translate]

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

theorem cubicThetaPrimeRootWeyl_translate_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
      (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v))=0 := by
  calc
    _ = inner ℂ (cubicThetaPrimeRootResidueL2 hp r
        (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u)))
        (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp v)) := by
          rw [cubicThetaPrimeRootWeyl_lift_translate]
    _ = inner ℂ (cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootLiftL2 hp u))
        (cubicThetaPrimeRootLiftL2 hp v) := (cubicThetaPrimeRootResidueL2 hp r).inner_map_map _ _
    _ = 0 := (inner_eq_zero_symm (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp)).mp
      (cubicThetaPrimeRootLiftWeyl_orthogonal hp v u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootSecondIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of intermediate root orthogonality to the cubic root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRoot_second_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : CubicThetaSection) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val z)*
      G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  have he := cubicThetaFiniteCover_integral (cubicThetaDoubleRootCover hp)
    (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRoot_le_double hp)
    (cubicThetaPrimeCubeRootCoverDomain hp)
    (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure)
    (f:=fun z => star (F.val z)*G.val (cubicThetaPrimeDoubleRootElement hp x • z))
    (cubicThetaPrimeDoubleRoot_translate_pair_invariant hp x F G)
  change (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val z)*
    G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=_ at he
  rw [show (∫ z in (cubicThetaDoubleRootCover hp).domain,star (F.val z)*
      G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=0 from
        cubicThetaPrimeDoubleRoot_translation_integral_zero hp x hx F G,smul_zero] at he
  exact he

theorem cubicThetaPrimeCubeRoot_single_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : CubicThetaSection) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val z)*
      G.val (cubicThetaPrimeCubeRootElement hp (p*x) • z) ∂cubicThetaPointMeasure)=0 := by
  rw [cubicThetaPrimeCubeRootElement_single]
  exact cubicThetaPrimeCubeRoot_second_integral_zero hp x hx F G

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootTracePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubed-prime trace pairing transported to the actual
common root cover. All degree factors remain explicit. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFinite_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeCubeRootFiniteSections hp) :
    inner ℂ (cubicThetaPrimeCubeRootFiniteEmbedding hp F) (cubicThetaPrimeCubeRootFiniteEmbedding hp G)=
      ∫ x in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val x)*G.val.val x ∂cubicThetaPointMeasure := by
  change inner ℂ (F.property.toLp F.val.val) (G.property.toLp G.val.val)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp,G.property.coeFn_toLp] with x hF hG
  rw [hF,hG]
  exact RCLike.inner_apply' _ _

theorem cubicThetaPrimeCubeRootTrace_integral {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      star (F.val x)*(cubicThetaPrimeCubeDilationSection hp G).val x ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℝ) •
        ∫ x in cubicThetaFundamentalDomain,
          star (F.val x)*(cubicThetaPrimeCubeHecke hp G).val x ∂cubicThetaPointMeasure := by
  have hcF := cubicThetaPrimeCubeInvariant_integrable hp hF (cubicThetaOriginal_norm_invariant F)
  have hcG := cubicThetaPrimeCubeDilation_integrable hp G hG
  have hpair := cubicThetaSquareIntegrablePair F.val (cubicThetaPrimeCubeDilationSection hp G).val
    F.val.continuous (cubicThetaPrimeCubeDilationSection hp G).val.continuous hcF hcG
  rw [cubicThetaPrimeCubeRootHecke_integral hp hpair
    (cubicThetaPrimeCubePair_invariant (cubicThetaPrimeCubeSectionRestrict F)
      (cubicThetaPrimeCubeDilationSection hp G))]
  rw [←cubicThetaPrimeCubeTrace_pairing hp (cubicThetaPrimeCubeDilationSection hp G) F hcG hF]
  rfl

theorem cubicThetaPrimeCubeRootTrace_finite {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaSmoothTests) :
    inner ℂ (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F))
      (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp G))=
      ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℝ) •
        inner ℂ (cubicThetaGlobalMassClosure F)
          (cubicThetaPrimeCubeHeckeMass hp (cubicThetaGlobalMassClosure G)) := by
  rw [cubicThetaPrimeCubeRootFinite_pairing]
  change (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
    star (F.val.val x)*(cubicThetaPrimeCubeDilationSection hp G.val).val x ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeRootTrace_integral hp F.val G.val
    (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy F))
    (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy G))]
  congr 1
  change _=inner ℂ (cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy F))
    (cubicThetaPrimeCubeHeckeMass hp (cubicThetaFiniteMassClosure (cubicThetaSmoothToFiniteEnergy G)))
  rw [cubicThetaPrimeCubeHeckeMass_finite]
  change _=inner ℂ (cubicThetaFiniteEnergyValue (cubicThetaSmoothToFiniteEnergy F))
    (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp (cubicThetaSmoothToFiniteEnergy G)))
  rw [cubicThetaFiniteEnergyValue_pairing]
  apply integral_congr_ae
  filter_upwards with x
  exact (RCLike.inner_apply' _ _).symm

end CubicFirstMoment

end

end OAI
end


