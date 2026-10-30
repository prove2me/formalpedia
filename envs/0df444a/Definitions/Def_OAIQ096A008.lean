-- Prove2me | Definitions.Def_OAIQ096A008
-- name    : OAIQ096A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:36:36.793329+00:00
-- url     : https://prove2.me/theorems/0fc8de4a-443f-4307-a0b5-8a8986ae1db0
-- title:
--   Definitions bundle OAIQ096A008 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 334 declarations of OpenAI's Lean: 126 definitions, 3 instances and 205 theorems. The definitions and types are `OAI.CubicFirstMoment.angularPrimeDifference`, `OAI.CubicFirstMoment.angularPrimeModel`, `OAI.CubicFirstMoment.angularPrimeMoment`, `OAI.CubicFirstMoment.angularRetainedIntegral`, `OAI.CubicFirstMoment.angularSmoothModel`, `OAI.CubicFirstMoment.angularStoppedAlpha`, `OAI.CubicFirstMoment.angularStoppedCharacterSum`, `OAI.CubicFirstMoment.angularStoppedDivisorMass`, `OAI.CubicFirstMoment.angularStoppedRowCoefficient`, `OAI.CubicFirstMoment.angularWeightedPrimeSum`, `OAI.CubicFirstMoment.angular_stoppedDivisorRowMass`, `OAI.CubicFirstMoment.centeredGauss`, `OAI.CubicFirstMoment.centeredProductPolynomial`, `OAI.CubicFirstMoment.centeredProductSmoothed`, `OAI.CubicFirstMoment.collectedPrimeCoefficient`, `OAI.CubicFirstMoment.commonGramBlock`, `OAI.CubicFirstMoment.commonGramZeroMode`, `OAI.CubicFirstMoment.complementAbsoluteWeight`, `OAI.CubicFirstMoment.complementProductSupport`, `OAI.CubicFirstMoment.coordinateComplementTuples`, `OAI.CubicFirstMoment.coprimeCubeMainTerm`, `OAI.CubicFirstMoment.coprimeDispersionGram`, `OAI.CubicFirstMoment.coprimeMellinEnvelope`, `OAI.CubicFirstMoment.coprimePairs`, `OAI.CubicFirstMoment.coprimePoissonDyad`, `OAI.CubicFirstMoment.coprimeResidualSupport`, `OAI.CubicFirstMoment.coprimeSquarefreeModelMass`, `OAI.CubicFirstMoment.coreDyadicBlock`, `OAI.CubicFirstMoment.coreDyadicCubeFactors`, `OAI.CubicFirstMoment.correctedBilinearSum`, `OAI.CubicFirstMoment.correctedSquareMass`, `OAI.CubicFirstMoment.cubeCompletionSeries`, `OAI.CubicFirstMoment.cubeInverseCompletionSeries`, `OAI.CubicFirstMoment.cubeModelTerm`, `OAI.CubicFirstMoment.cubePoissonContribution`, `OAI.CubicFirstMoment.cubicInstanceMoment`, `OAI.CubicFirstMoment.cubicNeighborhoodAdmissible`, `OAI.CubicFirstMoment.cubicThetaAdmissiblePair`, `OAI.CubicFirstMoment.cubicThetaAngularCoefficient`, `OAI.CubicFirstMoment.cubicThetaAngularExpConstant` and 86 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_FrequencyGauss`, `CubicGram_GramPoisson`, `CubicGram_LatticeCounts`, `CubicGram_LatticePoisson`, `CubicGram_MixedPoisson`, `CubicGram_NormRecurrence`, `CubicGram_PeriodicPoisson`, `CubicMoment_Angular_AngularAlgebra`, `CubicMoment_Angular_AngularLatticeModel`, `CubicMoment_Angular_AngularModel`, `CubicMoment_Angular_AngularSmoothApproximation`, `CubicMoment_Angular_AngularStoppedCharacterRows`, `CubicMoment_Angular_AngularStoppedDivisorPartition`, `CubicMoment_Angular_AngularStoppedMellinRows`, `CubicMoment_Angular_AngularStoppedOuterCoefficient`, `CubicMoment_Decomposition_DistinguishedCoefficients`, `CubicMoment_Decomposition_StoppedCharacterRows`, `CubicMoment_Decomposition_StoppedCoefficients`, `CubicMoment_Decomposition_StoppedDistinguishedRow`, `CubicMoment_Decomposition_StoppedDyadPartition`, `CubicMoment_Decomposition_StoppedPrimeIntervals`, `CubicMoment_Decomposition_StoppedPrimePredicate`, `CubicMoment_Decomposition_StoppedSelectedRow`, `CubicMoment_Decomposition_StoppingProductSlice`, `CubicMoment_Estimates_BilinearKernelIdentity`, `CubicMoment_Estimates_CenteredProductMellin`, `CubicMoment_Estimates_CommonGramRemainder`, `CubicMoment_Estimates_CommonZeroMode`, `CubicMoment_Estimates_ComplementAbsoluteMass`, `CubicMoment_Estimates_ComplementAbsoluteWeight`, `CubicMoment_Estimates_ConductorLocal`, `CubicMoment_Estimates_ConductorNeighborhoods`, `CubicMoment_Estimates_CoprimeDispersionPoisson`, `CubicMoment_Estimates_CoprimeResidueLift`, `CubicMoment_Estimates_CoprimeSquarefreeMass`, `CubicMoment_Estimates_CorrectedBilinearScale`, `CubicMoment_Estimates_CorrectedSquareMass`, `CubicMoment_Estimates_CubeFiniteError`, `CubicMoment_Estimates_CubeModelOverlap`, `CubicMoment_Estimates_CubicDyadicCoverage`, `CubicMoment_Estimates_CubicSupplementaryPeriodicityProof`, `CubicMoment_Estimates_DivisorFrequencyDyads`, `CubicMoment_Estimates_DivisorPoissonRadial`, `CubicMoment_Estimates_GeometricPrimeBins`, `CubicMoment_Estimates_HuxleyFractionSeparation`, `CubicMoment_Estimates_IdealDualDyads`, `CubicMoment_Estimates_IdealEulerExclusion`, `CubicMoment_Estimates_IdealMellinSeries`, `CubicMoment_Estimates_IdealMoebiusBounds`, `CubicMoment_Estimates_IdealThetaDecay`, `CubicMoment_Estimates_IdealThetaLattice`, `CubicMoment_Estimates_LargestPrimeSelection`, `CubicMoment_Estimates_NoncubeOrdinaryBounds`, `CubicMoment_Estimates_NoncubeSieveAssembly`, `CubicMoment_Estimates_NormCoprimeWindow`, `CubicMoment_Estimates_NormSeries`, `CubicMoment_Estimates_PrimaryCharacterNonprincipal`, `CubicMoment_Estimates_PrimeBins`, `CubicMoment_Estimates_PrimeIntervalGeometry`, `CubicMoment_Estimates_PrimeLogConvolution`, `CubicMoment_Estimates_PrimeLogReplacement`, `CubicMoment_Estimates_PrimeSharpCutoff`, `CubicMoment_Estimates_PrimeTupleCoordinate`, `CubicMoment_Estimates_PrimeTupleDecomposition`, `CubicMoment_Estimates_PrincipalZetaContinuation`, `CubicMoment_Estimates_PublishedHecke`, `CubicMoment_Estimates_RamifiedCubicNonprincipal`, `CubicMoment_Estimates_RamifiedCubicValues`, `CubicMoment_Estimates_ResidueIdealCharacters`, `CubicMoment_Estimates_ResidueThetaLattice`, `CubicMoment_Estimates_RoughMoebius`, `CubicMoment_Estimates_ShortFactorUniform`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Estimates_ShortMoebiusFinite`, `CubicMoment_Estimates_SmoothShortFamily`, `CubicMoment_Estimates_SparseStoppingLabels`, `CubicMoment_Theta_CubicThetaAllGridEquation`, `CubicMoment_Theta_CubicThetaAngularExponential`, `CubicMoment_Theta_CubicThetaAngularPowers`, `CubicMoment_Theta_CubicThetaAnnularSeries`, `CubicMoment_Theta_CubicThetaArithmeticAxisRegularity`, `CubicMoment_Theta_CubicThetaArithmeticEnergy`, `CubicMoment_Theta_CubicThetaArithmeticEquation`, `CubicMoment_Theta_CubicThetaArithmeticRemainder`, `CubicMoment_Theta_CubicThetaArithmeticSection`, `CubicMoment_Theta_CubicThetaAxisDifferentials`, `CubicMoment_Theta_CubicThetaBoundedScaledMellin`, `CubicMoment_Theta_CubicThetaCompactCoreCover`, `CubicMoment_Theta_CubicThetaCompactHeight`, `CubicMoment_Theta_CubicThetaContinuity`, `CubicMoment_Theta_CubicThetaCoordinateAxis`, `CubicMoment_Theta_CubicThetaCoordinateRegularity`, `CubicMoment_Theta_CubicThetaCoordinateSection`, `CubicMoment_Theta_CubicThetaCuspDisjointness`, `CubicMoment_Theta_CubicThetaCuspFourierNormalization`, `CubicMoment_Theta_CubicThetaCuspFourierObservable`, `CubicMoment_Theta_CubicThetaCuspLatticeWeight`, `CubicMoment_Theta_CubicThetaCuspRemainder`, `CubicMoment_Theta_CubicThetaCuspRemainderBound`, `CubicMoment_Theta_CubicThetaCuspRowMajorant`, `CubicMoment_Theta_CubicThetaCuspSeparation`, `CubicMoment_Theta_CubicThetaCuspStripReduction`, `CubicMoment_Theta_CubicThetaEisenstein`, `CubicMoment_Theta_CubicThetaEisensteinConvergence`, `CubicMoment_Theta_CubicThetaEisensteinResidues`, `CubicMoment_Theta_CubicThetaEisensteinSpectral`, `CubicMoment_Theta_CubicThetaEisensteinUnfold`, `CubicMoment_Theta_CubicThetaFiniteCongruenceCover`, `CubicMoment_Theta_CubicThetaForcingSeries`, `CubicMoment_Theta_CubicThetaForcingSmooth`, `CubicMoment_Theta_CubicThetaFourierCoefficients`, `CubicMoment_Theta_CubicThetaGreenAlgebra`, `CubicMoment_Theta_CubicThetaGridAnalytic`, `CubicMoment_Theta_CubicThetaGridDifferentiation`, `CubicMoment_Theta_CubicThetaGridEquation`, `CubicMoment_Theta_CubicThetaGridJets`, `CubicMoment_Theta_CubicThetaGridLocalJets`, `CubicMoment_Theta_CubicThetaGridMajorant`, `CubicMoment_Theta_CubicThetaIncomingEquation`, `CubicMoment_Theta_CubicThetaIncomingLocalFinite`, `CubicMoment_Theta_CubicThetaIncomingRowEquation`, `CubicMoment_Theta_CubicThetaIncomingRows`, `CubicMoment_Theta_CubicThetaIncomingSmooth`, `CubicMoment_Theta_CubicThetaJointRegularity`, `CubicMoment_Theta_CubicThetaNinePhase`, `CubicMoment_Theta_CubicThetaNinePhaseSymbol`, `CubicMoment_Theta_CubicThetaPoincareSections`, `CubicMoment_Theta_CubicThetaPoincareSmooth`, `CubicMoment_Theta_CubicThetaPositiveLocalization`, `CubicMoment_Theta_CubicThetaPrimaryNineFourier`, `CubicMoment_Theta_CubicThetaPrimeCubeTransversal`, `CubicMoment_Theta_CubicThetaQuotientCore`, `CubicMoment_Theta_CubicThetaQuotientMeasure`, `CubicMoment_Theta_CubicThetaRamifiedAllRows`, `CubicMoment_Theta_CubicThetaRamifiedCharacter`, `CubicMoment_Theta_CubicThetaRamifiedCharacterFourier`, `CubicMoment_Theta_CubicThetaRamifiedMiddleSupport`, `CubicMoment_Theta_CubicThetaRamifiedModel`, `CubicMoment_Theta_CubicThetaRamifiedUnitGauss`, `CubicMoment_Theta_CubicThetaRowHeightChain`, `CubicMoment_Theta_CubicThetaRowHeightEquation`, `CubicMoment_Theta_CubicThetaRowMellin`, `CubicMoment_Theta_CubicThetaRowRadius`, `CubicMoment_Theta_CubicThetaScalarCuspCutoff`, `CubicMoment_Theta_CubicThetaScalarCuspEnergy`, `CubicMoment_Theta_CubicThetaScalarCuspQuotient`, `CubicMoment_Theta_CubicThetaSecondContinuity`, `CubicMoment_Theta_CubicThetaSeries`, `CubicMoment_Theta_CubicThetaShiftedInvertedRows`, `CubicMoment_Theta_CubicThetaSiegelReduction`, `CubicMoment_Theta_CubicThetaSieveSupport`, `CubicMoment_Theta_CubicThetaSpatialContinuity`, `CubicMoment_Theta_CubicThetaSpatialDerivativeBound`, `CubicMoment_Theta_CubicThetaUnitCharacter`, `CubicMoment_Theta_CubicThetaUnitCharacterFourier`, `CubicMoment_Theta_CubicThetaUnitPhaseSymbol`, `CubicMoment_Theta_CubicThetaVerticalTermDerivative`, `CubicMoment_Transform_MetaplecticCompletion`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A004`, `OAIQ096A005` and `OAIQ096A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A011`, `OAIQ096A012`, `OAIQ096A013`, `OAIQ096A014` and `OAIQ096A015`; the statements `OAI.CubicFirstMoment.ProfileControl.low_common_sum_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power`, `OAI_CubicFirstMoment_angular_balanced_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_angular_first_twisted_vonMangoldt_neighborhood`, `OAI.CubicFirstMoment.angular_stopped_corrected_dispersion_log_saving_actual`, `OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass`, `OAI_CubicFirstMoment_angular_stopped_noncube_core_blocks`, `OAI.CubicFirstMoment.angular_stopped_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form`, `OAI.CubicFirstMoment.angular_stopped_product_bilinear_log_saving_actual`, `OAI.CubicFirstMoment.angular_stopped_sieved_model_log_saving`, `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment`, `OAI.CubicFirstMoment.bounded_large_common_nonzero`, `OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds`, `OAI_CubicFirstMoment_dominant_first_full_factor_neighborhood`, `OAI_CubicFirstMoment_first_common_coordinate_exponents`, `OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay`, `OAI_CubicFirstMoment_largePrimeTuplePiece_ordinary_range`, `OAI.CubicFirstMoment.large_common_nonzero_power`, `OAI_CubicFirstMoment_normalized_angular_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_normalized_twisted_primitive_ideal_cubic_moment`, `OAI.CubicFirstMoment.outer_core_block_sieve`, `OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power`, `OAI.CubicFirstMoment.smallB_core_hybrid_sieve`, `OAI.CubicFirstMoment.small_conductor_frequency_sieve`, `OAI.CubicFirstMoment.stopped_centered_bilinear_log_saving_actual`, `OAI.CubicFirstMoment.stopped_noncube_radial_form` and `OAI.CubicFirstMoment.stopped_sieved_model_log_saving`; the proofs of `OAI_CubicFirstMoment_angular_stopped_distinguished_full_saving`, `OAI.CubicFirstMoment.bounded_cubic_moment`, `OAI.CubicFirstMoment.bounded_large_common_nonzero`, `OAI_CubicFirstMoment_largePrimeTuplePiece_ordinary_range`, `OAI.CubicFirstMoment.outer_core_block_sieve` and `OAI_CubicFirstMoment_stopped_distinguished_full_saving`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A004
import Definitions.Def_OAIQ096A005
import Definitions.Def_OAIQ096A006

section
-- module Solutions.OAIQ096_CM.CubicGram_FrequencyGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime, squarefree and mixed frequency Gauss evaluation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem mixedFrequencyGauss_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    mixedFrequencyGauss a b h =
      (gauss a * star (gauss b)) * (star (cubicSymbol a h) * cubicSymbol b h) := by
  rw [mixedFrequencyGauss_CRT ha hb hab,
    frequencyGauss_squarefree ha hsa, conjugateFrequencyGauss_squarefree hb hsb]
  have hu : cubicSymbol a b * star (cubicSymbol b a) = 1 := by
    rw [cubic_reciprocity ha hb]
    change cubicSymbol b a * starRingEnd ℂ (cubicSymbol b a) = 1
    rw [Complex.mul_conj', norm_cubicSymbol_of_isCoprime hb hab.symm]
    norm_num
  rw [hu]
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticePoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma eisensteinRealCoords_integer (n : Fin 2 → ℤ) :
    eisensteinRealCoords (fun i => (n i : ℝ)) = (ofCoords (n 0) (n 1) : ℂ) := by
  simp [ofCoords_coe]

lemma realCoordMatrix_det : realCoordMatrix.det = Real.sqrt 3 / 2 := by
  simp [realCoordMatrix, Matrix.det_fin_two]

lemma realCoordMatrix_apply (x : Fin 2 → ℝ) :
    Matrix.toLin' realCoordMatrix x = Complex.measurableEquivPi (eisensteinRealCoords x) := by
  ext i
  fin_cases i <;>
    simp [realCoordMatrix, Matrix.toLin'_apply, Matrix.mulVec,
      omega_re, omega_im, Matrix.vecHead, Matrix.vecTail, mul_comm]

lemma eisensteinRealCoords_map_volume :
    Measure.map eisensteinRealCoords volume =
      ENNReal.ofReal (2 / Real.sqrt 3) • (volume : Measure ℂ) := by
  have hs : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := realCoordMatrix) (by rw [realCoordMatrix_det]; positivity)
  have he : (eisensteinRealCoords : (Fin 2 → ℝ) → ℂ) =
      Complex.measurableEquivPi.symm ∘ Matrix.toLin' realCoordMatrix := by
    funext x
    simp only [Function.comp_apply, realCoordMatrix_apply, MeasurableEquiv.symm_apply_apply]
  rw [he, ← Measure.map_map Complex.measurableEquivPi.symm.measurable
    (Matrix.toLin' realCoordMatrix).continuous_of_finiteDimensional.measurable, hm,
    Measure.map_smul,
    Complex.volume_preserving_equiv_pi.symm.map_eq, realCoordMatrix_det]
  congr 1
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < Real.sqrt (3 : ℝ) / 2))]
  field_simp

lemma integral_eisensteinRealCoords (f : ℂ → ℂ) :
    ∫ x : Fin 2 → ℝ, f (eisensteinRealCoords x) =
      (2 / Real.sqrt 3 : ℝ) • ∫ z : ℂ, f z := by
  have h := integral_map_equiv (μ := volume) eisensteinRealCoords.toHomeomorph.toMeasurableEquiv f
  rw [show ((eisensteinRealCoords.toHomeomorph.toMeasurableEquiv : (Fin 2 → ℝ) → ℂ)) =
    eisensteinRealCoords from rfl, eisensteinRealCoords_map_volume, integral_smul_measure] at h
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / Real.sqrt 3)] using h.symm

def dualIntegerEquiv : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun n := ![n 0 + n 1, n 0]
  invFun m := ![m 1, m 0 - m 1]
  left_inv n := by ext i; fin_cases i <;> simp
  right_inv m := by ext i; fin_cases i <;> simp

def eisensteinPullback (f : 𝓢(ℂ, ℂ)) : 𝓢(Fin 2 → ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eisensteinRealCoords f

lemma coordinateFourier_eisenstein (f : 𝓢(ℂ, ℂ)) (y : Fin 2 → ℝ) :
    coordinateFourier (eisensteinPullback f) y =
      (2 / Real.sqrt 3 : ℝ) • traceFourier f (dualRealCoords y) := by
  rw [coordinateFourier_apply, traceFourier]
  convert integral_eisensteinRealCoords
    (fun z => (Real.fourierChar (-tracePair z (dualRealCoords y)) : ℂ) * f z) using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards with x
  simp only [dualRealCoords_trace, eisensteinPullback,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

lemma coordinatesEquiv_coe (n : Fin 2 → ℤ) :
    (coordinatesEquiv n : ℂ) = eisensteinRealCoords (fun i => (n i : ℝ)) := by
  simp [coordinatesEquiv, coordinatesMap, ofCoords_coe]

lemma dualRealCoords_integer (n : Fin 2 → ℤ) :
    dualRealCoords (fun i => (n i : ℝ)) =
      (coordinatesEquiv (dualIntegerEquiv n) : ℂ) / traceLambda := by
  rw [dualRealCoords_eq, coordinatesEquiv_coe]
  simp [dualIntegerEquiv]

theorem poisson_eisenstein (f : 𝓢(ℂ, ℂ)) :
    ∑' a : Eisenstein, f (a : ℂ) =
      (2 / Real.sqrt 3 : ℝ) •
        ∑' h : Eisenstein, traceFourier f ((h : ℂ) / traceLambda) := by
  calc
    _ = ∑' n : Fin 2 → ℤ, eisensteinPullback f (fun i => (n i : ℝ)) := by
      have he := coordinatesEquiv.toEquiv.tsum_eq (fun a : Eisenstein => f (a : ℂ))
      change (∑' n : Fin 2 → ℤ, f (coordinatesEquiv n : ℂ)) = _ at he
      simpa only [coordinatesEquiv_coe, eisensteinPullback,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply] using he.symm
    _ = ∑' n : Fin 2 → ℤ,
        coordinateFourier (eisensteinPullback f) (fun i => (n i : ℝ)) :=
      poisson_coordinates_zero _
    _ = ∑' n : Fin 2 → ℤ,
        (2 / Real.sqrt 3 : ℝ) • traceFourier f
          ((coordinatesEquiv (dualIntegerEquiv n) : ℂ) / traceLambda) := by
      congr 1
      funext n
      rw [coordinateFourier_eisenstein, dualRealCoords_integer]
    _ = ∑' h : Eisenstein, (2 / Real.sqrt 3 : ℝ) •
        traceFourier f ((h : ℂ) / traceLambda) :=
      (dualIntegerEquiv.trans coordinatesEquiv.toEquiv).tsum_eq
        (fun h : Eisenstein => (2 / Real.sqrt 3 : ℝ) •
          traceFourier f ((h : ℂ) / traceLambda))
    _ = _ := tsum_const_smul'' _

theorem poisson_eisenstein_translate (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    ∑' a : Eisenstein, f (z + (a : ℂ)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' h : Eisenstein,
        (Real.fourierChar (tracePair z ((h : ℂ) / traceLambda)) : ℂ) *
          traceFourier f ((h : ℂ) / traceLambda) := by
  have he := poisson_eisenstein (f.compSubConstCLM ℂ (-z))
  have hfun : (⇑(f.compSubConstCLM ℂ (-z))) = (fun x => f (z + x)) := by
    funext x
    simp [add_comm]
  simpa only [hfun, traceFourier_translation] using he

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma schwartz_summable_eisenstein (f : 𝓢(ℂ, ℂ)) :
    Summable (fun a : Eisenstein => f (a : ℂ)) := by
  apply coordinatesEquiv.toEquiv.summable_iff.mp
  change Summable (fun n : Fin 2 → ℤ => f (coordinatesEquiv n : ℂ))
  simpa only [coordinatesEquiv_coe, eisensteinPullback,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply] using
      schwartz_summable_integerCoordinates (eisensteinPullback f)

end CubicFirstMoment

namespace CubicFirstMoment

lemma lambdaE_coe : (lambdaE : ℂ) = traceLambda := rfl

lemma three_lambda_cube : (3 : Eisenstein) * lambdaE = (-lambdaE) ^ 3 := by
  rw [pow_succ, neg_sq, lambdaE_sq]
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MixedPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary mixed characters and squarefree coset Poisson summation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_three_lambda {c : Eisenstein} (hc : primary c) :
    cubicSymbol c (3 * lambdaE) = 1 := by
  rw [three_lambda_cube, pow_succ, pow_two, cubicSymbol_mul_upper hc,
    cubicSymbol_mul_upper hc, cubicSymbol_neg hc]
  simpa only [pow_succ, pow_two, pow_zero, one_mul] using
    cubicSymbol_cube_of_isCoprime hc lambdaE (primary_coprime_lambda hc)

lemma mixedSymbol_three_lambda {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    mixedSymbol a b (3*lambdaE) = 1 := by
  simp only [mixedSymbol, cubicSymbol_three_lambda ha, cubicSymbol_three_lambda hb,
    star_one, mul_one]

end CubicFirstMoment

namespace CubicFirstMoment

def primaryMixedFourier (a b h : Eisenstein) : ℂ :=
  ∑' v : Residues (a*b), mixedSymbol a b (3 * residueRepresentative (a*b) v) *
    (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
      ((h : ℂ) / (((a*b : Eisenstein) : ℂ) * traceLambda))) : ℂ)

lemma primaryMixedFourier_eq {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : Eisenstein) :
    primaryMixedFourier a b h = (Real.sqrt (norm (a*b)) : ℂ) * mixedFrequencyGauss a b h := by
  have hc := primary_mul ha hb
  have hc0 := primary_ne_zero hc
  have hc0' : ((a*b : Eisenstein) : ℂ) ≠ 0 := fun he => hc0 (Subtype.ext he)
  obtain ⟨u, hu⟩ := residue_isUnit_of_isCoprime (primary_coprime_lambda hc)
  let e := u.mulLeft
  let F (v : Residues (a*b)) :=
    mixedSymbol a b (3 * residueRepresentative (a*b) v) *
    (Real.fourierChar (tracePair (residueRepresentative (a*b) v : ℂ)
      ((h : ℂ) / (((a*b : Eisenstein) : ℂ) * traceLambda))) : ℂ)
  have hreindex (v : Residues (a*b)) :
      Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b)) (lambdaE * residueRepresentative (a*b) v) := by
    rw [residueRepresentative_spec, map_mul, residueRepresentative_spec]
    change (u : Residues (a*b)) * v = _
    rw [hu]
  have hF (v : Residues (a*b)) : F (e v) =
      mixedSymbol a b (residueRepresentative (a*b) v) *
        additivePhase (a*b) (h * residueRepresentative (a*b) v) := by
    dsimp only [F]
    rw [mixedSymbol_congr (show Ideal.Quotient.mk (modulus (a*b))
      (3 * residueRepresentative (a*b) (e v)) = Ideal.Quotient.mk (modulus (a*b))
      (3 * (lambdaE * residueRepresentative (a*b) v)) by rw [map_mul, map_mul, hreindex])]
    rw [← mul_assoc, mixedSymbol_mul ha hb, mixedSymbol_three_lambda ha hb, one_mul,
      tracePhase_congr hc0 h (hreindex v), additivePhase_fourierChar]
    congr 2
    unfold tracePair
    congr 2
    simp only [Subalgebra.coe_mul, lambdaE_coe]
    field_simp [traceLambda_ne_zero]
  unfold primaryMixedFourier
  change (∑' v, F v) = _
  rw [← e.tsum_eq F]
  simp_rw [hF]
  unfold mixedFrequencyGauss
  have hs : (Real.sqrt (norm (a*b)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (Complex.normSq_pos.mpr hc0'))
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  rfl

theorem primaryMixedFourier_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    primaryMixedFourier a b h = (Real.sqrt (norm (a*b)) : ℂ) *
      (gauss a * star (gauss b)) * (star (cubicSymbol a h) * cubicSymbol b h) := by
  rw [primaryMixedFourier_eq ha hb, mixedFrequencyGauss_squarefree ha hb hsa hsb hab]
  ring

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

def gramDualTerm (a b : Eisenstein) (W : ℝ → ℂ) (Z : ℝ) (h : Eisenstein) : ℂ :=
  (star (cubicSymbol a h) * cubicSymbol b h) *
    (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
      normProfileFourier W
        ((Real.sqrt Z : ℂ) * ((h : ℂ) / (3*((a*b : Eisenstein) : ℂ)*traceLambda)))

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem nonzeroNormBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((nonzeroNormBall X).card : ℝ) ≤ 18*X := by
  by_cases hX1 : 1 ≤ X
  · let C : ℤ := ⌊Real.sqrt (2*X)⌋
    have hC1 : (1 : ℤ) ≤ C := Int.le_floor.mpr (by
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; nlinarith))
    have hC0 : 0 ≤ (C : ℝ) := by exact_mod_cast (show 0 ≤ C by omega)
    have hC : (C : ℝ) ≤ Real.sqrt (2*X) := Int.floor_le _
    have hCsq : (C : ℝ)^2 ≤ 2*X := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2*X by positivity)]
    let box := (Finset.Icc (-C) C).product (Finset.Icc (-C) C)
    have hsub : nonzeroNormBall X ⊆ box.image (fun p => ofCoords p.1 p.2) := by
      intro z hz
      obtain ⟨a,b,hz'⟩ := exists_coordinates z
      have hn : (a : ℝ)^2 - a*b + b^2 ≤ X := by
        have hn' : norm z = ((a^2-a*b+b^2 : ℤ) : ℝ) := by
          rw [norm, hz', coordinates_norm]
        have hz := (mem_nonzeroNormBall.mp hz).1
        rw [hn'] at hz
        exact_mod_cast hz
      have ha2 : (a : ℝ)^2 ≤ 2*X := by nlinarith [sq_nonneg ((a : ℝ)-b)]
      have hb2 : (b : ℝ)^2 ≤ 2*X := by nlinarith [sq_nonneg ((a : ℝ)-b)]
      have hab : -(Real.sqrt (2*X)) ≤ (a : ℝ) ∧ (a : ℝ) ≤ Real.sqrt (2*X) := by
        have := (sq_le_sq₀ (abs_nonneg (a : ℝ)) (Real.sqrt_nonneg (2*X))).mp
          (by rw [sq_abs, Real.sq_sqrt (show 0 ≤ 2*X by positivity)]; exact ha2)
        exact abs_le.mp this
      have hbb : -(Real.sqrt (2*X)) ≤ (b : ℝ) ∧ (b : ℝ) ≤ Real.sqrt (2*X) := by
        have := (sq_le_sq₀ (abs_nonneg (b : ℝ)) (Real.sqrt_nonneg (2*X))).mp
          (by rw [sq_abs, Real.sq_sqrt (show 0 ≤ 2*X by positivity)]; exact hb2)
        exact abs_le.mp this
      have ha : a ∈ Finset.Icc (-C) C := by
        simp only [Finset.mem_Icc]
        exact ⟨by have := Int.le_floor.mpr (show ((-a : ℤ) : ℝ) ≤ Real.sqrt (2*X) by
                    push_cast; linarith); dsimp [C] at *; omega,
          Int.le_floor.mpr hab.2⟩
      have hb : b ∈ Finset.Icc (-C) C := by
        simp only [Finset.mem_Icc]
        exact ⟨by have := Int.le_floor.mpr (show ((-b : ℤ) : ℝ) ≤ Real.sqrt (2*X) by
                    push_cast; linarith); dsimp [C] at *; omega,
          Int.le_floor.mpr hbb.2⟩
      exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, Subtype.ext hz'.symm⟩
    have hc : (nonzeroNormBall X).card ≤ box.card :=
      (Finset.card_le_card hsub).trans (Finset.card_image_le)
    have heq : (box.card : ℝ) = (2*(C : ℝ)+1)^2 := by
      dsimp [box]
      rw [Finset.card_product, Int.card_Icc]
      push_cast
      have hv : ((C+1- -C).toNat : ℝ) = (C+1- -C : ℤ) := by
        exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ C+1- -C by omega)
      rw [hv]
      push_cast
      ring
    have hc' : ((nonzeroNormBall X).card : ℝ) ≤ (2*(C : ℝ)+1)^2 := by
      rw [← heq]; exact_mod_cast hc
    have hC1' : (1 : ℝ) ≤ C := by exact_mod_cast hC1
    nlinarith [sq_nonneg ((C : ℝ)-1)]
  · have hempty : nonzeroNormBall X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz := mem_nonzeroNormBall.mp hz
      exact hX1 ((one_le_norm hz.2).trans hz.1)
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_NormRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor-completed energies and the coprime Poisson norm recurrence. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def coprimePoissonDyad (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    u a * star (u b) * ((Z / (9*Real.sqrt (norm (a*b))) : ℝ) : ℂ) *
      (gauss a * star (gauss b)) * ∑ h ∈ H, gramDualTerm a b W Z h else 0

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebra of fixed angular prime moments

The angular weight is the phase of a nonzero Eisenstein integer raised to
an integer power.  These elementary facts ensure that fixed angular
weights preserve absolute values and distribute through finite prime sums.
-/

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

/-- The elementary prime model in the fixed angular mode `ℓ`. -/
def angularPrimeModel (ℓ : ℤ) (p : Eisenstein) : ℂ :=
  theta ℓ p * (cStar * norm p ^ (-1 / 6 : ℝ) : ℝ)

/-- The prime Gauss-sum moment in the fixed angular mode `ℓ`. -/
def angularPrimeMoment (ℓ : ℤ) (X : ℝ) : ℂ :=
  primeCutoffSum (fun p => theta ℓ p * gaussAtPrime p) X

/-- The difference between the Gauss-sum moment and its elementary model. -/
def angularPrimeDifference (ℓ : ℤ) (X : ℝ) : ℂ :=
  primeCutoffSum (fun p => theta ℓ p *
    (gaussAtPrime p - (cStar * norm p ^ (-1 / 6 : ℝ) : ℝ))) X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

instance eisenstein_discreteTopology : DiscreteTopology Eisenstein := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have he : Metric.ball (0 : Eisenstein) 1 = {0} := by
    ext a
    simp only [Metric.mem_ball,dist_zero_right,Set.mem_singleton_iff]
    constructor
    · intro ha
      by_contra hn
      have h := one_le_norm hn
      rw [eisenstein_norm_eq_sq] at h
      nlinarith [_root_.norm_nonneg a]
    · rintro rfl
      simp
  rw [← he]
  exact Metric.isOpen_ball

/-- The norm is the squared complex absolute value, so the convergence
threshold for its negative powers is one. -/
theorem summable_eisenstein_norm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Eisenstein => norm a^(-s)) := by
  let L : Submodule ℤ ℂ := eisensteinRing.toSubmodule
  have hdim : Module.finrank ℤ L = 2 := by
    calc
      _ = Module.finrank ℤ Eisenstein := (eisensteinRing.toSubmoduleEquiv).finrank_eq
      _ = Module.finrank ℤ (Fin 2 → ℤ) := coordinatesEquiv.finrank_eq.symm
      _ = 2 := by simp
  have hL : DiscreteTopology L := eisenstein_discreteTopology
  let := hL
  have h := ZLattice.summable_norm_rpow L (-2*s) (by rw [hdim]; push_cast; linarith)
  change Summable (fun a : Eisenstein => ‖a‖^(-2*s)) at h
  apply h.congr
  intro a
  rw [eisenstein_norm_eq_sq,← Real.rpow_natCast ‖a‖ 2,← Real.rpow_mul (_root_.norm_nonneg a)]
  congr 1
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

theorem mixedCubic_norm_of_coprime {q₁ q₂ a : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (ha : IsCoprime (q₁ * q₂) a) :
    ‖mixedCubic q₁ q₂ a‖ = 1 := by
  rw [mixedCubic, norm_mul, norm_star,
    norm_cubicSymbol_of_isCoprime h₁ ha.of_mul_left_left,
    norm_cubicSymbol_of_isCoprime h₂ ha.of_mul_left_right, one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealPrimeRepresentative_irreducible (p : EisensteinIdealPrime) :
    Irreducible (idealPrimeRepresentative p) := by
  apply Associates.irreducible_mk.mp
  have h : Associates.mk (Quotient.out p.val) = p.val := Associates.quot_out _
  simpa only [idealPrimeRepresentative, h] using p.property

lemma idealExponentGenerator_ne_zero (ν : EisensteinIdealExponent) :
    idealExponentGenerator ν ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (idealPrimeRepresentative_irreducible p).ne_zero

lemma idealExponentNorm_ge_one (ν : EisensteinIdealExponent) : 1 ≤ idealExponentNorm ν := by
  change (1 : ℝ) ≤ (normNat (idealExponentGenerator ν) : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (normNat_ne_zero (idealExponentGenerator_ne_zero ν))

lemma idealExponentNorm_pos (ν : EisensteinIdealExponent) : 0 < idealExponentNorm ν :=
  zero_lt_one.trans_le (idealExponentNorm_ge_one ν)

lemma idealMoebiusSeries_mul_zeta : idealMoebiusSeries * idealZeta = 1 := by
  apply MvPowerSeries.inv_mul_cancel
  change (1 : ℝ) ≠ 0
  norm_num

/-- The usual convolution definition of the ideal von Mangoldt function. -/
def idealVonMangoldt : EisensteinArithmeticFunction := idealMoebiusSeries * idealLogNorm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealExponentOf_primeRepresentative (p : EisensteinIdealPrime) :
    idealExponentOf (idealPrimeRepresentative p) = Finsupp.single p 1 := by
  have h : Associates.factors' (idealPrimeRepresentative p) = {p} := by
    apply WithTop.coe_inj.mp
    rw [← Associates.factors_mk _ (idealPrimeRepresentative_irreducible p).ne_zero]
    have he : Associates.mk (idealPrimeRepresentative p) = p.val := Associates.quot_out p.val
    rw [he]
    exact Associates.factors_self p.property
  simp [idealExponentOf,h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

/-- Multiplying the zeta series by a finite Euler product excludes
precisely the prime divisors occurring in that product. -/
lemma coeff_zeta_finiteIdealMoebius (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν (idealZeta * finiteIdealMoebius S) =
      if ∀ p ∈ S, ν p = 0 then 1 else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => simp [finiteIdealMoebius, idealZeta, MvPowerSeries.coeff_apply]
  | @insert p S hp ih =>
    have he : idealZeta * finiteIdealMoebius (insert p S) =
        (idealZeta * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, coeff_mul_one_sub_X, ih, ih]
    simp only [tsub_single_away S hp, Finset.forall_mem_insert]
    by_cases h : ν p = 0
    · simp [h]
    · have hn : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr h
      simp [h, hn]

/-- For a coefficient whose prime support lies in `S`, the genuine
Dirichlet inverse is computed by the finite Euler product over `S`. -/
lemma coeff_idealMoebiusSeries_eq_finite (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hν : ν.support ⊆ S) :
    MvPowerSeries.coeff ν idealMoebiusSeries =
      MvPowerSeries.coeff ν (finiteIdealMoebius S) := by
  have he : idealMoebiusSeries * (idealZeta * finiteIdealMoebius S) =
      finiteIdealMoebius S := by
    rw [← mul_assoc, idealMoebiusSeries_mul_zeta, one_mul]
  rw [← he, MvPowerSeries.coeff_mul]
  symm
  rw [Finset.sum_eq_single (ν, 0)]
  · simp [coeff_zeta_finiteIdealMoebius]
  · intro a ha hne
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
    have hle : a.2 ≤ ν := by
      rw [← hsum]
      exact le_add_of_nonneg_left zero_le
    have hz : ¬ ∀ p ∈ S, a.2 p = 0 := by
      intro hzero
      have ha2 : a.2 = 0 := by
        ext p
        by_cases hp : p ∈ S
        · exact hzero p hp
        · have hn : ν p = 0 := Finsupp.notMem_support_iff.mp (fun h => hp (hν h))
          exact Nat.eq_zero_of_le_zero (hn ▸ hle p)
      have ha1 : a.1 = ν := by simpa [ha2] using hsum
      exact hne (Prod.ext ha1 ha2)
    rw [coeff_zeta_finiteIdealMoebius, ite_eq_right hz, mul_zero]
  · intro h
    exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero ν))).elim

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealExponentOf_eq_of_associated {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associated a b) : idealExponentOf a = idealExponentOf b := by
  have he := congrArg Associates.factors (Associates.mk_eq_mk_iff_associated.mpr h)
  rw [Associates.factors_mk a ha,Associates.factors_mk b hb] at he
  exact congrArg Multiset.toFinsupp (WithTop.coe_inj.mp he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- All nonzero ideals of norm at most `Y`, including ideals above three. -/
def fullIdealBall (Y : ℝ) : Finset EisensteinIdealExponent :=
  (nonzeroNormBall Y).image idealExponentOf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularLatticeModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual squarefree angular model in the low Type-I argument.
Its norm factor is absorbed into the test function, and its cancellation
is obtained from the proved primary-lattice estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def angularSmoothModel (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (U : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u then theta ℓ (r*u)*(idealMoebius (r*u):ℂ)^2*
    (cStar*norm (r*u)^(-1/6:ℝ):ℝ)*W (norm u/U) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

/-- The angular power-weighted sum before multiplying by `cStar`. -/
def angularWeightedPrimeSum (ℓ : ℤ) (X : ℝ) : ℂ :=
  primeCutoffSum (fun p => theta ℓ p * ((norm p ^ (-1 / 6 : ℝ) : ℝ) : ℂ)) X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma residueChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (x : Residues q) : ‖χ x‖ ≤ 1 := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  by_cases hx : IsUnit x
  · obtain ⟨u,rfl⟩ := hx
    have he : ‖χ (u : Residues q)‖ = 1 :=
      Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact he.le
  · rw [MulChar.map_nonunit χ hx,norm_zero]
    exact zero_le_one

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothApproximation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform smooth dual approximation at each fixed infinity type,
derived from the precise published completion and classical Gamma
inputs. The original sum retains every primitive local Euler factor. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def angularRetainedIntegral (W : ℝ → ℂ) (χdual : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A k Z J t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A k
        ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power saving from the proved actual-sequence contradictions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cubicInstanceMoment (x : ShortMomentInstance ι Eisenstein) : ℝ :=
  ∑ p ∈ x.rows, ‖∏ i, x.family.cubicValue 0 i p‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryCharacterNonprincipal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma exists_primary_residue_lift {q : Eisenstein} (hq : primary q) (y : Eisenstein) :
    ∃ x : Eisenstein, primary x ∧
      Ideal.Quotient.mk (modulus q) x = Ideal.Quotient.mk (modulus q) y := by
  obtain ⟨u,v,huv⟩ := (primary_coprime_three hq)
  refine ⟨q*u+3*v*y,?_,?_⟩
  · refine ⟨v*(y-1),?_⟩
    linear_combination huv
  · apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨u*(1-y),?_⟩
    linear_combination y*huv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDualDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact dyadic decomposition of the retained full-ideal polynomial.
The square-root normalization changes only coefficients, not characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealDyad (S : Finset EisensteinIdealExponent) (j : ℕ) : Finset EisensteinIdealExponent :=
  S.filter (fun ν => idealDyadIndex ν = j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorLocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local detection of the squarefree cubic conductor. A nontrivial
prime character survives every inducing modulus, as witnessed by CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residue_crt_one {p Q : Eisenstein} (h : IsCoprime p Q) (y : Eisenstein) :
    ∃ x : Eisenstein, p ∣ x-y ∧ Q ∣ x-1 := by
  obtain ⟨u,v,huv⟩ := h
  refine ⟨p*u+Q*v*y,⟨u*(1-y),?_⟩,⟨v*(y-1),?_⟩⟩
  · linear_combination y*huv
  · linear_combination huv

lemma isCoprime_of_dvd_sub_one {q x : Eisenstein} (hx : q ∣ x-1) : IsCoprime q x := by
  apply isCoprime_of_residue_isUnit
  rw [residue_eq_of_dvd_sub hx,map_one]
  exact isUnit_one

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothShortFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def smoothShortTwist {q : Eisenstein} (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (X t : ℝ) (n : Eisenstein) : ℂ :=
  η (Ideal.Quotient.mk (modulus q) n)*mellinPhase t (norm n)*W (norm n/(X/2))

lemma smoothShortTwist_norm {q : Eisenstein} (hq : q ≠ 0)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (hW : ∀ x, ‖W x‖ ≤ 1)
    (X t : ℝ) (n : Eisenstein) : ‖smoothShortTwist η W X t n‖ ≤ 1 := by
  rw [smoothShortTwist,norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_mul (residueChar_norm_le_one hq η _) (hW _)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primary factor tuples in the distinguished-prime expansion.
Ordering a subset contributes its factorial; the remaining primary factor
is the literal complementary product, not an abstract coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedPrimeWeight (ψ : ℝ → ℝ) (w z : ℝ) (p : Eisenstein) : ℂ :=
  (ψ (norm p/w)-ψ (norm p/z):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal primary-divisor Möbius expansion used in the small-R
branch, and its exact splitting at a prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cutoffMoebius (ψ : ℝ → ℝ) (w : ℝ) (d : Eisenstein) : ℂ :=
  (idealMoebius d:ℂ)*∏ p ∈ primaryPrimeFactors d, (ψ (norm p/w):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal independent coefficients from the stopping construction.
The selected-side test may contain the first-stage failure and crossing
conditions; the remaining-side test is a separate condition on its divisor.
No coprimality condition is inserted between the two sides. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryPairSupport (S T : Finset Eisenstein) : Finset Eisenstein :=
  (S ×ˢ T).image (fun p => p.1*p.2)

def primaryPairFiber (S T : Finset Eisenstein) (b : Eisenstein) :
    Finset (Eisenstein × Eisenstein) :=
  (S ×ˢ T).filter (fun p => p.1*p.2 = b)

def primaryPairCoefficient (S T : Finset Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  ∑ p ∈ primaryPairFiber S T b, w p

def stoppedBeta (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein) : ℂ :=
  primaryPairCoefficient R D
    (fun p => if selected p.1 p.2 then v p.1*cutoffMoebius ψ w p.2 else 0) b

def stoppedAlpha (E U : Finset Eisenstein) (ψ : ℝ → ℝ) (w : ℝ)
    (remaining : Eisenstein → Prop) (a : Eisenstein) : ℂ :=
  primaryPairCoefficient E U
    (fun p => if remaining p.1 then cutoffMoebius ψ w p.1 else 0) a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished-tuple weight occurring in stopped coefficients.
Its multiplicity is bounded in terms of the fixed tuple length, so the
literal beta coefficient has one divisor-count loss independently of bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distinguishedTupleCoefficient (S : ι → Finset Eisenstein)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ) (r : Eisenstein) : ℂ :=
  ((Fintype.card ι).factorial:ℂ)⁻¹ *
    orderedConvolution S (fun i p => W i p*distinguishedPrimeWeight ψ w z p) r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first stopping bin is selected from actual finite prime bins.
Only the final bin and its selected count are exposed as outer indices. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeBin (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) : Finset Eisenstein :=
  s.filter (fun p => b p = j)

def primeBinPrefix (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) : Finset Eisenstein :=
  s.filter (fun p => b p < j)

def primeSurrogate (s : Finset Eisenstein) (b : Eisenstein → ℕ) (ell : ℕ → ℝ) : ℝ :=
  ∏ p ∈ s, ell (b p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIntervalGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stopped crossing tests with one prime left free. A distinguished
prime enters by its actual norm; a selected-bin prime leaves every
surrogate prefix unchanged while its bin is fixed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largestPrimePredicate (code : Eisenstein → ℕ) (s : Finset Eisenstein)
    (p : Eisenstein) : Prop :=
  ∀ q ∈ s, normNat q < normNat p ∨ (normNat q = normNat p ∧ code q ≤ code p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargestPrimeSelection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def primeTieCode (p : Eisenstein) : ℕ :=
  Encodable.encode (Function.invFun (fun z : ℤ × ℤ => ofCoords z.1 z.2) p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleCoordinate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing one distinguished coordinate is an exact finite bijection.
On squarefree prime tuples the largest-prime coordinate is unique. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateComplementTuples (S : ι → Finset Eisenstein) (i : ι) : Finset (ι → Eisenstein) :=
  Fintype.piFinset (Function.update S i {1})

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative uncollected tuple weights. These retain the absolute
complementary mass; no cancellation of collected coefficients is used. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complementAbsoluteWeight (S : ι → Finset Eisenstein) (i : ι)
    (W : ι → Eisenstein → ℂ) (r : Eisenstein) : ℝ :=
  ∑ g ∈ (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r),
    ∏ j ∈ Finset.univ.erase i, ‖W j (g j)‖

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplementAbsoluteMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear complementary mass after a distinguished prime is removed.
The absolute tuple weights are collected before applying rough divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complementProductSupport (S : ι → Finset Eisenstein) (i : ι) : Finset Eisenstein :=
  (coordinateComplementTuples S i).image (fun g => ∏ j, g j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimeIntervals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete selected-side stopping predicates. Replacing one prime
within its fixed bin leaves every selected-bin surrogate test unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppingPrimeSetTest (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j k : ℕ) (Z : ℝ) (r : Eisenstein) : Prop :=
  (∀ p ∈ s, bin p ≤ j) ∧ (primeBin s bin j).card = k ∧
    norm r*primeSurrogate s bin ell/ell j < Z ∧
    Z ≤ norm r*primeSurrogate s bin ell

def stoppingSideTest (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    (j k : ℕ) (Z : ℝ) (r d : Eisenstein) : Prop :=
  stoppingPrimeSetTest (primaryPrimeFactors d) bin ell j k Z r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPrimePredicate
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both actual stopping branches, including failure of the earlier
crossing test. Fixing the selected prime's bin fixes all these tests. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedSideTest (bin : Eisenstein → ℕ) (ell : ℕ → ℝ)
    (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r d : Eisenstein) : Prop :=
  stoppingSideTest bin ell j k Z r d ∧
    (early = true ∨ norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell < Q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete descending geometric binning of the actual prime norms.
The number of bins is logarithmic and all lower endpoints exceed one,
so the exact first-crossing construction applies without empty-bin cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def geometricPrimeBin (ρ B : ℝ) (p : Eisenstein) : ℕ :=
  geometricBinCount ρ B - ⌊Real.log (norm p)/Real.log ρ⌋₊

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSelectedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def stoppedSelectedPrimeSet (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r c e : Eisenstein) : Finset Eisenstein :=
  ((((primeCutoff B).filter (fun p => a < norm p ∧ norm p ≤ b)).filter
    (fun p => IsCoprime p (c*(r*e)))).filter
    (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p ∧
      geometricPrimeBin ρ B p = j)).filter
    (fun p => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
      j₀ k h Z Q early r (p*c))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDistinguishedRow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime cancellation with the literal distinguished-coordinate bin,
output interval and both stopping tests. The interval is derived, not
assumed to describe the stopping support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedDistinguishedPrimeSet (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (c d e : Eisenstein) : Finset Eisenstein :=
  (((primeCutoff B).filter (fun p => IsCoprime p e)).filter
    (fun p => largestPrimePredicate primeTieCode (primaryPrimeFactors (c*d)) p)).filter
    (fun p => geometricPrimeBin ρ B p = j ∧
      (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
      stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early (c*p) d)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def normalizedVonMangoldt (a : Eisenstein) : ℝ :=
  MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt / Real.log (norm a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual error in replacing a convolution of prime indicators by
normalized von Mangoldt coefficients has sparse prime-power support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeLogConvolutionError (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  orderedConvolution S (fun i a => (normalizedVonMangoldt a:ℂ)*w i a) b-
    orderedConvolution S (fun i a => (primeIndicator a:ℂ)*w i a) b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeOrdinaryBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-sieve orientation on actual ramified/cube frequency blocks. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def coprimeResidualSupport (R J : Finset Eisenstein)
    (P : Finset (Eisenstein × Eisenstein)) : Finset Eisenstein :=
  ((R.product J).product P).image (fun t => t.1.1*t.2.1*t.2.2^2*t.1.2^3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeSieveAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All three sieve orientations on the same concrete noncube frequency block. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimePairs (S T : Finset Eisenstein) : Finset (Eisenstein × Eisenstein) :=
  (S.product T).filter (fun p => IsCoprime p.1 p.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal stopped character sum as a squarefree coefficient row.
The norm phase preserves its energy, and the energy is derived from the
actual distinguished coefficient rather than supplied as a hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stoppedIntervalSupport (ι : Type*) [Fintype ι] [DecidableEq ι]
    (X a b : ℝ) (e : Eisenstein) : Finset Eisenstein :=
  (primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
    (primaryElementBall X)).filter
      (fun n => Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b)

def stoppedRowCoefficient (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) : ℂ :=
  stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X)
    (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X)
      (fun i p => W i (norm p)) primeDetectorCutoff w z)
    primeDetectorCutoff w selected n * normTwist u n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular stopped coefficient and its exact character row.
Angular multiplication preserves the proved pointwise and energy bounds;
cube factors and divisor exclusions remain literal finite identities. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def angularStoppedRowCoefficient (ℓ : ℤ) (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) : ℂ :=
  stoppedRowCoefficient X w z u W selected n * theta ℓ n

def angularStoppedCharacterSum (ℓ : ℤ) (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) : ℂ :=
  ∑ n ∈ stoppedIntervalSupport ι X a b e,
    angularStoppedRowCoefficient ℓ X w z u W selected n * cubicSymbol n v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coreDyadicCubeFactors (B : ℝ) (i j : ℕ) : Finset Eisenstein :=
  nonzeroNormBall ((B/coreDyadicConductor i j)^(1/3:ℝ))

def coreDyadicBlock (B : ℝ) (i j : ℕ) : Finset Eisenstein :=
  coprimeResidualSupport (nonzeroNormBall 729) (coreDyadicCubeFactors B i j)
    (coprimePairs (squarefreePrimaryDyad i) (squarefreePrimaryDyad j))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormCoprimeWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from a bounded range of Mellin shifts to the full coprime
Poisson integral, with the exact coarse envelope for its remaining shifts. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeMellinEnvelope (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ) : ℝ :=
  ∑ s ∈ U.powerset, (H.card:ℝ)*
    ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖)^2+
     (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖)^2)/2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedMellinRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def angularStoppedDivisorMass (ℓ : ℤ) (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H U : Finset Eisenstein) : ℝ :=
  ∑ d ∈ U.powerset, ∑ h ∈ H,
    ‖∑ n ∈ (stoppedIntervalSupport ι X a b e).filter (fun n => (∏ p ∈ d,p) ∣ n),
      angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n h‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedDivisorPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def angular_stoppedDivisorRowMass (ℓ : ℤ) (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H s : Finset Eisenstein) : ℝ :=
  ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
    (fun n => (∏ p ∈ s,p) ∣ n),
    angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedSquareMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine squarefree corrected variance, with its exact finite
support reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def correctedSquareMass (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℝ) (A : ℝ) : ℝ :=
  ∑' a : Eisenstein, if primary a then (idealMoebius a:ℝ)^2*V (norm a/A)*
    ‖correctedDispersionPolynomial S β u a‖^2 else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CorrectedBilinearScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic saving furnished by corrected Cauchy--Schwarz. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def correctedBilinearSum (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist u (a*b))-
    (cStar:ℂ)*dispersionModel B β u*
      (∑ a ∈ P, α a*normTwist u a*(if Squarefree a then (1:ℂ) else 0)*
        ((norm a^(-1/6:ℝ):ℝ):ℂ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicNeighborhoodAdmissible (δ H D C κ : ℝ)
    (x : ConductorMomentInstance ι Eisenstein) : Prop :=
  (∀ i, x.family.length 0 i ≤ x.scale^(1-δ)) ∧
  (x.scale/C ≤ ∏ i, x.family.length 0 i) ∧
  (∏ i, x.family.length 0 i) ≤ C*x.scale ∧
  1 ≤ x.conductorScale ∧
  (x.scale^(1-κ) ≤ x.conductorScale ∧ x.conductorScale ≤ x.scale^(1+κ)) ∧
  (∀ p ∈ x.rows, gramDyad x.conductorScale p) ∧
  (x.rows.card:ℝ) ≤ x.scale^D ∧
  (∀ p ∈ x.rows, ∀ i, ‖x.family.cubicValue 0 i p‖ ≤ x.scale^H)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeDispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cube/noncube splitting of the coprime portion of the variance.
No diagonal or shared-prime contribution is silently included here. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeDispersionGram (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    dispersionAmplitude β u a*star (dispersionAmplitude β u b)*primaryCharacterGram b a W A else 0

def cubePoissonContribution (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ)*
      ∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then
        gramDualTerm b a W A h else 0
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeFiniteError
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the literal principal-frequency error over the coprime Gram pairs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeCubeMainTerm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorPoissonRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def divisorFourierPhase (d h : Eisenstein) : ℂ :=
  (Real.fourierChar (tracePair (((Function.invFun (fun h : Eisenstein => d*h) h):Eisenstein):ℂ)
    (1/(3*traceLambda))):ℂ)

@[simp] lemma norm_divisorFourierPhase (d h : Eisenstein) : ‖divisorFourierPhase d h‖ = 1 := by
  unfold divisorFourierPhase
  exact Circle.norm_coe _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorFrequencyDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyads used by the divisor Poisson sum are dyads of d*h.
They form an exact finite-fiber partition, with no lost multiplicity. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorFrequencyDyad (d : Eisenstein) (hd : d ≠ 0) (j : ℕ) : Finset Eisenstein :=
  (frequencyDyad j).preimage (fun h => d*h) (fun _ _ _ _ he => mul_left_cancel₀ hd he)

@[simp] lemma mem_divisorFrequencyDyad {d : Eisenstein} {hd : d ≠ 0} {j : ℕ} {h : Eisenstein} :
    h ∈ divisorFrequencyDyad d hd j ↔ d*h ∈ frequencyDyad j := Finset.mem_preimage

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonGramRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the coprime term from the exact common-factor expansion.
Only nonunit common factors remain, so roughness shortens every row. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonGramBlock (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (Z : ℝ) (k : Eisenstein) : ℂ :=
  ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k, if IsCoprime a b then
    u (k*a)*star (u (k*b))*primaryCharacterGram (k*a) (k*b) W Z else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CommonZeroMode
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero mode in a common-factor block is a single original row.
Its signed Möbius sum is the exact finite coprimality density. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonGramZeroMode (S : Finset Eisenstein) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) (A : ℝ) (k : Eisenstein) : ℂ :=
  ∑ s ∈ (primaryPrimeFactors k).powerset,
    let m := ∏ p ∈ s,p
    (idealMoebius m:ℂ)*coprimePoissonDyad (residualRows S k) {0}
      (commonBlockCoefficient v k m) W (A/norm m)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BilinearKernelIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factored correction and the original squarefree product kernel
are related by the explicit shared-prime contribution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def centeredGauss (a : Eisenstein) : ℂ :=
  gauss a-(cStar:ℂ)*(idealMoebius a:ℂ)^2*((norm a^(-1/6:ℝ):ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSharpCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sharp Fourier cutoff for actual prime sums

A fixed integer norm contains at most a conjugate pair of primary primes.
Thus collecting prime coefficients by norm supplies the coefficient bound
needed in the endpoint-kernel argument, without a norm-counting hypothesis.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def collectedPrimeCoefficient (P : Finset Eisenstein) (c : Eisenstein → ℂ) (n : ℤ) : ℂ :=
  ∑ p ∈ P.filter (fun p => (normNat p : ℤ) = n), c p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CenteredProductMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of the smooth total-product factor in a
centered bilinear Gauss sum. The norm height is shifted by the true Mellin
frequency, and absolute integrability follows from the smooth weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def centeredProductPolynomial (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) : ℂ :=
  ∑ a ∈ A, ∑ b ∈ B, α a*β b*theta ℓ (a*b)*centeredGauss (a*b)*normTwist u (a*b)

def centeredProductSmoothed (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ) (X u : ℝ) : ℂ :=
  ∑ a ∈ A, ∑ b ∈ B,
    α a*β b*theta ℓ (a*b)*centeredGauss (a*b)*normTwist u (a*b)*W (norm (a*b)/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedOuterCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular twist of the actual stopped outer coefficient.
Its primary-support energy and divisor bounds are unchanged. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def angularStoppedAlpha (ℓ : ℤ) (E U : Finset Eisenstein) (ψ : ℝ → ℝ)
    (w : ℝ) (remaining : Eisenstein → Prop) (a : Eisenstein) : ℂ :=
  stoppedAlpha E U ψ w remaining a * theta ℓ a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDyadPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sharp dyads with the strict lower endpoint used by stopped rows.
The partition is finite and its count depends only on the norm envelope. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedNormDyadIndex (n : Eisenstein) : ℕ := Nat.log 2 (normNat n-1)

def stoppedNormDyad (S : Finset Eisenstein) (j : ℕ) : Finset Eisenstein :=
  S.filter (fun n => stoppedNormDyadIndex n = j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseStoppingLabels
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual final-bin and two-occupancy index set in the stopping
construction has logarithmic size. No complete occupancy vector occurs. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] Classical.propDecidable

/-- The exact remaining-side predicate in the stopping split. -/
def stoppingRemainingTest (bin : Eisenstein → ℕ) (j l : ℕ) (e : Eisenstein) : Prop :=
  (∀ p ∈ primaryPrimeFactors e, j ≤ bin p) ∧
    (primeBin (primaryPrimeFactors e) bin j).card = l

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppingProductSlice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product slices for the original finite support. Divisibility
supplies the norm bound needed by the stopping construction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryProductSlice (S : Finset Eisenstein) (X : ℝ) (a : Eisenstein) :
    Finset Eisenstein :=
  (primaryElementBall X).filter (fun m => a*m ∈ S)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeResidueLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift a prime-to-modulus residue while avoiding any prescribed nonzero
factor. This keeps the actual cubic-character witness away from the cube
part of its numerator. -/
noncomputable section
namespace CubicFirstMoment

lemma isCoprime_of_residue_congr {q x y : Eisenstein}
    (hxy : q ∣ x-y) (hy : IsCoprime q y) : IsCoprime q x := by
  apply isCoprime_of_residue_isUnit
  rw [residue_eq_of_dvd_sub hxy]
  exact residue_isUnit_of_isCoprime hy

/-- Every residue prime to `q` has a representative prime to `q*c`. -/
theorem exists_coprime_residue_lift {q a c : Eisenstein}
    (hc : c ≠ 0) (ha : IsCoprime q a) :
    ∃ x : Eisenstein, q ∣ x-a ∧ IsCoprime (q*c) x := by
  have H : ∀ c : Eisenstein, c ≠ 0 →
      ∃ x : Eisenstein, q ∣ x-a ∧ IsCoprime (q*c) x := by
    intro c
    refine UniqueFactorizationMonoid.induction_on_prime c ?_ ?_ ?_
    · intro h
      exact (h rfl).elim
    · intro u hu _
      exact ⟨a,by simp,(isCoprime_mul_unit_right_left hu q a).mpr ha⟩
    · intro b p hb hp ih _
      obtain ⟨y,hy,hcop⟩ := ih hb
      by_cases hpq : p ∣ q
      · refine ⟨y,hy,?_⟩
        have hpy := hcop.of_mul_left_left.of_isCoprime_of_dvd_left hpq
        simpa only [mul_left_comm q p b] using hpy.mul_left hcop
      · by_cases hpb : p ∣ b
        · refine ⟨y,hy,?_⟩
          have hpy := hcop.of_mul_left_right.of_isCoprime_of_dvd_left hpb
          simpa only [mul_left_comm q p b] using hpy.mul_left hcop
        · have hpqb : IsCoprime (q*b) p :=
            ((hp.coprime_iff_not_dvd.mpr hpq).mul_right
              (hp.coprime_iff_not_dvd.mpr hpb)).symm
          obtain ⟨x,hxy,hxp⟩ := residue_crt_one hpqb y
          refine ⟨x,?_,?_⟩
          · have hqx : q ∣ x-y := (dvd_mul_right q b).trans hxy
            convert dvd_add hqx hy using 1
            all_goals try with_reducible_and_instances rfl
            ring
          · have hcop' := isCoprime_of_residue_congr hxy hcop
            have hpx := isCoprime_of_dvd_sub_one hxp
            simpa only [mul_left_comm q p b] using hpx.mul_left hcop'
  exact H c hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeSquarefreeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal mixed-term model with μ²(ra), and its quantitative
comparison with the unrestricted squarefree mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeSquarefreeModelMass (r : Eisenstein) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then (idealMoebius (r*a):ℂ)^2*
    W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubeModelOverlap
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The difference between the full model square and its coprime
pair sum is supported on shared-prime pairs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubeModelTerm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  (A^(2/3:ℝ)/9:ℝ)*cubeProfileIntegral V*((‖dispersionModel S β u‖^2:ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicSupplementaryPeriodicityProof
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Modulo `9v` periodicity of the actual cubic numerator symbol.

The ramified factor is treated by reciprocity against an auxiliary primary
argument. The unit factor follows from Euler's finite-field definition. This
proves the elementary specialization recorded in DR v3, §1.2 (1.4)--(1.5),
including the zero values at common prime factors. -/
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Explicit classification of the six Eisenstein units. -/
lemma eisenstein_unit_eq_signed_omega {u : Eisenstein} (hu : IsUnit u) :
    ∃ j : ℕ, u = omegaE^j ∨ u = -(omegaE^j) := unit_eq_signed_omega hu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyFractionSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation of the actual reduced Eisenstein fractions in the additive sieve. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_fraction_cross_norm {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    (a b z : Eisenstein) :
    norm (a*r-b*q-z*q*r) = norm q*norm r*
      ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := by
  have hqc : (q:ℂ) ≠ 0 := fun h => hq (Subtype.ext h)
  have hrc : (r:ℂ) ≠ 0 := fun h => hr (Subtype.ext h)
  have he : ((a*r-b*q-z*q*r:Eisenstein):ℂ) =
      (q:ℂ)*(r:ℂ)*((a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)) := by
    push_cast
    field_simp
  simp only [norm,Complex.normSq_eq_norm_sq]
  rw [he,_root_.norm_mul,_root_.norm_mul,mul_pow,mul_pow]

lemma eisenstein_fraction_separation {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q)
    (a b z : Eisenstein) (hgap : a*r-b*q-z*q*r ≠ 0) :
    1/Q^2 ≤ ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := by
  have hq0 := norm_pos_of_ne_zero hq
  have hr0 := norm_pos_of_ne_zero hr
  have hQ : 0 < Q := hq0.trans_le hqQ
  have hprod : norm q*norm r ≤ Q^2 := by
    simpa only [pow_two] using mul_le_mul hqQ hrQ hr0.le hQ.le
  have hcross := one_le_norm hgap
  rw [eisenstein_fraction_cross_norm hq hr a b z] at hcross
  apply (div_le_iff₀ (sq_pos_of_pos hQ)).mpr
  calc
    1 ≤ norm q*norm r*‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := hcross
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hprod (sq_nonneg _)

lemma reduced_fraction_associated_denominators {q r a b z : Eisenstein}
    (hqa : IsCoprime q a) (hrb : IsCoprime r b)
    (he : a*r-b*q-z*q*r = 0) : Associated q r := by
  have hqr : q ∣ r := by
    apply hqa.dvd_of_dvd_mul_left
    refine ⟨b+z*r,?_⟩
    linear_combination he
  have hrq : r ∣ q := by
    apply hrb.dvd_of_dvd_mul_left
    refine ⟨a-z*q,?_⟩
    linear_combination -he
  exact associated_of_dvd_dvd hqr hrq

lemma eisenstein_fraction_eq_of_close {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q) (a b z : Eisenstein)
    (hclose : ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 < 1/Q^2) :
    (a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ) = (z:ℂ) := by
  have hg : a*r-b*q-z*q*r = 0 := by
    by_contra hne
    exact (not_le_of_gt hclose) (eisenstein_fraction_separation hq hr hqQ hrQ a b z hne)
  have hn := eisenstein_fraction_cross_norm hq hr a b z
  rw [hg,show norm (0:Eisenstein) = 0 by simp [norm]] at hn
  have hq0 := norm_pos_of_ne_zero hq
  have hr0 := norm_pos_of_ne_zero hr
  have hsq : ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 = 0 := by
    exact (mul_eq_zero.mp hn.symm).resolve_left (mul_pos hq0 hr0).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

lemma translated_fraction_eq_of_close {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q)
    (a b u v : Eisenstein)
    (hclose : ‖((a:ℂ)/(q:ℂ)+(u:ℂ))-((b:ℂ)/(r:ℂ)+(v:ℂ))‖^2 < 1/Q^2) :
    (a:ℂ)/(q:ℂ)+(u:ℂ) = (b:ℂ)/(r:ℂ)+(v:ℂ) := by
  have he : (a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-((v-u:Eisenstein):ℂ) =
      ((a:ℂ)/(q:ℂ)+(u:ℂ))-((b:ℂ)/(r:ℂ)+(v:ℂ)) := by push_cast; ring
  have h := eisenstein_fraction_eq_of_close hq hr hqQ hrQ a b (v-u) (by rwa [he])
  push_cast at h
  linear_combination h

/-- All associates have a uniformly bounded multiplicity; an explicit lattice
bound suffices, so the large sieve does not require classifying the six units. -/
lemma associated_denominator_count (S : Finset Eisenstein) (q : Eisenstein) :
    ((S.filter (fun r => Associated q r)).card:ℝ) ≤ 18 := by
  classical
  have hsub : S.filter (fun r => Associated q r) ⊆
      (nonzeroNormBall 1).image (fun u => q*u) := by
    intro r hr
    obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hr).2
    apply Finset.mem_image.mpr
    refine ⟨(u:Eisenstein),?_,hu⟩
    exact mem_nonzeroNormBall.mpr ⟨(norm_of_isUnit u.isUnit).le,u.ne_zero⟩
  have hc := Finset.card_le_card hsub
  have hi := Finset.card_image_le (s := nonzeroNormBall 1) (f := fun u => q*u)
  have hn : ((nonzeroNormBall 1).card:ℝ) ≤ 18 := by
    simpa only [mul_one] using nonzeroNormBall_card_le (show (0:ℝ) ≤ 1 by norm_num)
  have hnat : (S.filter (fun r => Associated q r)).card ≤ (nonzeroNormBall 1).card := hc.trans hi
  exact (show ((S.filter (fun r => Associated q r)).card:ℝ) ≤
    ((nonzeroNormBall 1).card:ℝ) by exact_mod_cast hnat).trans hn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence and exponential decay of the actual ideal theta series. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CubicFirstMoment

def idealTheta (A : ℝ) (χ : EisensteinIdealExponent → ℂ) (t : ℝ) : ℂ :=
  ∑' ν, χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ideal-to-element reindexing for a unit-invariant residue theta series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealTheta_units_finite : Finite (Eisensteinˣ) := by
  let f : Eisensteinˣ → {u : Eisenstein // u ∈ nonzeroNormBall 1} := fun u =>
    ⟨u,mem_nonzeroNormBall.mpr ⟨by rw [norm_of_isUnit u.isUnit],u.ne_zero⟩⟩
  exact Finite.of_injective f (fun u v h => Units.ext (congrArg Subtype.val h))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Eisenstein theta sum, including its zero term, equals the
ideal theta sum with its exact unit multiplicity. -/
noncomputable section
namespace CubicFirstMoment

lemma residueTheta_unit_multiplicity_ne_zero : (Nat.card (Eisensteinˣ):ℂ) ≠ 0 := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  exact_mod_cast Nat.card_pos.ne'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def principalThetaConstant : ℂ := (Nat.card (Eisensteinˣ):ℂ)⁻¹

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedCubicValues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two exact cubic-symbol values detect the unit and ramified factors.
Their values are computed from the finite Euler definition. -/
noncomputable section
namespace CubicFirstMoment

lemma primary_neg_two : primary (-2:Eisenstein) := ⟨-1,by ring⟩

lemma normNat_neg_two : normNat (-2:Eisenstein)=4 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq (-2:ℂ) = (4:ℝ)
  norm_num

lemma cubicSymbol_neg_two_omega : cubicSymbol (-2:Eisenstein) omegaE = omega := by
  rw [cubicSymbol_omega_norm primary_neg_two,normNat_neg_two]
  norm_num

lemma cubicSymbol_neg_two_lambda : cubicSymbol (-2:Eisenstein) lambdaE = 1 := by
  have he : (-2:Eisenstein) ∣ lambdaE-1 := ⟨-omegaE,by dsimp [lambdaE]; ring⟩
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub he)]
  simpa using (cubicSymbol_pow_upper primary_neg_two (1:Eisenstein) 0)

lemma primary_seven_factor : primary (1+3*omegaE) := ⟨omegaE,by ring⟩

lemma normNat_seven_factor : normNat (1+3*omegaE)=7 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq ((1:ℂ)+3*omega) = (7:ℝ)
  have h := coordinates_norm 1 3
  norm_num at h
  exact h

lemma primaryPrime_seven_factor : primaryPrime (1+3*omegaE) :=
  ⟨primary_seven_factor,prime_of_normNat_prime (by rw [normNat_seven_factor]; norm_num)⟩

lemma cubicSymbol_seven_factor_lambda : cubicSymbol (1+3*omegaE) lambdaE = omega^2 := by
  rw [cubicSymbol_prime primaryPrime_seven_factor]
  apply cubicSymbol_euler_value primaryPrime_seven_factor
    (residue_isUnit_of_isCoprime (primary_coprime_lambda primary_seven_factor)) (2:Fin 3)
  rw [normNat_seven_factor]
  norm_num only
  apply residue_eq_of_dvd_sub
  refine ⟨1+omegaE,?_⟩
  dsimp [lambdaE]
  ring

lemma cubicSymbol_seven_factor_omega : cubicSymbol (1+3*omegaE) omegaE = omega^2 := by
  rw [cubicSymbol_omega_norm primary_seven_factor,normNat_seven_factor]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedCubicNonprincipal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonprincipality in the unit/ramified part, detected by the primary
arguments -2 and 1+3 omega. -/
noncomputable section
namespace CubicFirstMoment

lemma ramified_cube_of_three_dvd {u : Eisenstein} {j k : ℕ}
    (hu : u=omegaE^j ∨ u=-(omegaE^j)) (hj : 3 ∣ j) (hk : 3 ∣ k) :
    ∃ c : Eisenstein, c^3=u*lambdaE^k := by
  obtain ⟨a,rfl⟩ := hj
  obtain ⟨b,rfl⟩ := hk
  have he : omegaE^(3*a)=1 := by rw [pow_mul,omegaE_cube,one_pow]
  have hl : (lambdaE^b)^3=lambdaE^(3*b) := by rw [←pow_mul]; congr 1; omega
  rcases hu with rfl | rfl
  · exact ⟨lambdaE^b,by rw [he,one_mul,hl]⟩
  · exact ⟨-(lambdaE^b),by rw [he,neg_one_mul,neg_pow]; norm_num; exact hl⟩

lemma unit_coprime_every (u x : Eisenstein) (hu : IsUnit u) : IsCoprime u x :=
  (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the cubic theta Fourier expansion on its actual
common cusp frequency lattice lambda^{-4} Z[omega]. The coefficient here includes the
factor 1/|mu| when the Whittaker function is evaluated at |mu|v. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaFrequency (n : Eisenstein) : ℂ := (n:ℂ)/traceLambda^4

def cubicThetaSeriesTerm (a : Eisenstein → ℂ) (z : ℂ) (v : ℝ) (n : Eisenstein) : ℂ :=
  if n = 0 then 0 else a n*cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)*
    (Real.fourierChar (tracePair (cubicThetaFrequency n) z) : ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locally uniform convergence and continuity of the actual cusp Fourier
series in horizontal position and positive height. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaNonconstant (a : Eisenstein → ℂ) (p : ℂ × ℝ) : ℂ :=
  ∑' n : Eisenstein, cubicThetaSeriesTerm a p.1 p.2 n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisenstein
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic Eisenstein series on the principal group, before analytic
continuation. The bottom-row reindexing proves its actual automorphy;
no transformation formula for the theta coefficients is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaEisensteinTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  star r.phase*(r.height p:ℂ)^s

def cubicThetaEisenstein (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaEisensteinTerm r p s

lemma cubicThetaEisensteinTerm_translate (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0 < p.2) (s : ℂ) :
    cubicThetaEisensteinTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s =
      cubicThetaKubotaValue g*cubicThetaEisensteinTerm (r.rightMul g) p s := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g) = 1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaEisensteinTerm,cubicThetaEisensteinTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*(r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p):ℂ)^s) := by
      rw [hu,one_mul]
    _ = _ := by ring

/-- Automorphy follows by the exact bijection of primitive bottom rows.
Absolute convergence in the initial half-plane is proved separately. -/
theorem cubicThetaEisenstein_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0 < p.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s =
      cubicThetaKubotaValue g*cubicThetaEisenstein p s := by
  unfold cubicThetaEisenstein
  simp_rw [cubicThetaEisensteinTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaEisensteinTerm r p s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinConvergence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the actual cubic Eisenstein series in
Re(s)>2, proved from the Eisenstein lattice and the positive height form. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_eisenstein_one_add_norm {t : ℝ} (ht : 1 < t) :
    Summable (fun n : Eisenstein => (1+norm n)^(-t)) := by
  have hsingle : Summable (fun n : Eisenstein => if n = 0 then (1:ℝ) else 0) := by
    apply (hasSum_single 0 ?_).summable
    intro n hn
    simp [hn]
  apply (hsingle.add (summable_eisenstein_norm_rpow ht)).of_nonneg_of_le
  · intro n
    exact Real.rpow_nonneg (by linarith [norm_nonneg n]) _
  · intro n
    by_cases hn : n = 0
    · simpa [hn,norm] using (Real.rpow_nonneg (show (0:ℝ) ≤ 0 from le_rfl) (-t))
    · have h := Real.rpow_le_rpow_of_nonpos (norm_pos_of_ne_zero hn)
        (show norm n ≤ 1+norm n by linarith) (show -t ≤ 0 by linarith)
      simpa only [hn,ite_false, if_false,zero_add] using h

lemma cubicThetaEisensteinTerm_bound (r : CubicThetaBottomRow) {p : ℂ × ℝ}
    (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    ‖cubicThetaEisensteinTerm r p s‖ ≤
      (p.2*cubicThetaHeightConstant p)^s.re*
        ((1+norm r.c)^(-s.re/2)*(1+norm r.d)^(-s.re/2)) := by
  have hC := cubicThetaHeightConstant_pos hp
  have hN : 0 < 1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  rw [cubicThetaEisensteinTerm,norm_mul,norm_star,r.phase_norm,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (r.height_pos hp)]
  calc
    _ ≤ ((p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d))^s.re :=
      Real.rpow_le_rpow (r.height_pos hp).le (r.height_le hp) (by linarith)
    _ = (p.2*cubicThetaHeightConstant p)^s.re*(1+norm r.c+norm r.d)^(-s.re) := by
      rw [Real.div_rpow (mul_pos hp hC).le hN.le,Real.rpow_neg hN.le]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cubicTheta_two_norm_decay (norm_nonneg r.c) (norm_nonneg r.d) (by linarith : 0 ≤ s.re))
      (Real.rpow_nonneg (mul_pos hp hC).le _)

theorem cubicThetaEisenstein_summable {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun r : CubicThetaBottomRow => cubicThetaEisensteinTerm r p s) := by
  have ht : 1 < s.re/2 := by linarith
  have hsum := summable_eisenstein_one_add_norm ht
  have hprod : Summable (fun cd : Eisenstein × Eisenstein =>
      (1+norm cd.1)^(-(s.re/2))*(1+norm cd.2)^(-(s.re/2))) :=
    summable_mul_of_summable_norm hsum.norm hsum.norm
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r t he
    apply CubicThetaBottomRow.ext
    · exact (Prod.mk.inj he).1
    · exact (Prod.mk.inj he).2
  apply ((hprod.mul_left ((p.2*cubicThetaHeightConstant p)^s.re)).comp_injective hi).of_norm_bounded
  intro r
  simpa only [neg_div,Function.comp_apply] using cubicThetaEisensteinTerm_bound r hp hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaEisensteinWeight (c d : Eisenstein) : ℂ :=
  if primary d ∧ IsCoprime c d then cubicSymbol d c else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact absolutely convergent unfolding from primitive rows to the
two Eisenstein lattice coordinates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaAdmissiblePair (cd : Eisenstein × Eisenstein) : Prop :=
  (3:Eisenstein) ∣ cd.1 ∧ primary cd.2 ∧ IsCoprime cd.1 cd.2

def cubicThetaBottomRowEquiv : CubicThetaBottomRow ≃ {cd // cubicThetaAdmissiblePair cd} where
  toFun r := ⟨(r.c,r.d),r.c_three,r.d_primary,r.coprime⟩
  invFun cd := ⟨cd.val.1,cd.val.2,cd.property.1,cd.property.2.1,cd.property.2.2⟩
  left_inv r := by cases r; rfl
  right_inv cd := by apply Subtype.ext; rfl

def cubicThetaEisensteinGridTerm (cd : Eisenstein × Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if cubicThetaAdmissiblePair cd then
    cubicSymbol cd.2 cd.1*
      ((p.2/(Complex.normSq ((cd.1:ℂ)*p.1+cd.2)+norm cd.1*p.2^2):ℝ):ℂ)^s
  else 0

lemma cubicThetaEisensteinGridTerm_admissible (cd : {cd // cubicThetaAdmissiblePair cd})
    (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm cd.val p s =
      cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm cd) p s := by
  simp only [cubicThetaEisensteinGridTerm,cd.property,ite_true, if_true,cubicThetaEisensteinTerm,
    cubicThetaBottomRowEquiv,CubicThetaBottomRow.phase,CubicThetaBottomRow.height,star_star]
  rfl

lemma cubicThetaEisensteinGrid_summable {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Summable (fun cd : Eisenstein × Eisenstein => cubicThetaEisensteinGridTerm cd p s) := by
  have hsub : Summable (fun cd : {cd // cubicThetaAdmissiblePair cd} =>
      cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm cd) p s) :=
    (cubicThetaEisenstein_summable hp hs).comp_injective cubicThetaBottomRowEquiv.symm.injective
  have hgsub : Summable (fun cd : {cd // cubicThetaAdmissiblePair cd} =>
      cubicThetaEisensteinGridTerm cd.val p s) := by
    apply hsub.congr
    intro cd
    exact (cubicThetaEisensteinGridTerm_admissible cd p s).symm
  have hi : Summable ({cd | cubicThetaAdmissiblePair cd}.indicator
      (fun cd => cubicThetaEisensteinGridTerm cd p s)) :=
    (summable_subtype_iff_indicator (s := {cd | cubicThetaAdmissiblePair cd})).mp hgsub
  apply hi.congr
  intro cd
  by_cases hc : cubicThetaAdmissiblePair cd <;>
    simp [Set.indicator,cubicThetaEisensteinGridTerm,hc]

theorem cubicThetaEisenstein_eq_grid (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisenstein p s = ∑' cd : Eisenstein × Eisenstein, cubicThetaEisensteinGridTerm cd p s := by
  calc
    _ = ∑' cd : {cd // cubicThetaAdmissiblePair cd},
        cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm cd) p s :=
      (cubicThetaBottomRowEquiv.symm.tsum_eq (fun r => cubicThetaEisensteinTerm r p s)).symm
    _ = ∑' cd : {cd // cubicThetaAdmissiblePair cd}, cubicThetaEisensteinGridTerm cd.val p s := by
      apply tsum_congr
      intro cd
      exact (cubicThetaEisensteinGridTerm_admissible cd p s).symm
    _ = ∑' cd : Eisenstein × Eisenstein,
        if cubicThetaAdmissiblePair cd then cubicThetaEisensteinGridTerm cd p s else 0 :=
      tsum_subtype {cd | cubicThetaAdmissiblePair cd} (fun cd => cubicThetaEisensteinGridTerm cd p s)
    _ = _ := by
      apply tsum_congr
      intro cd
      by_cases h : cubicThetaAdmissiblePair cd <;> simp [cubicThetaEisensteinGridTerm,h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowRadius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scaling and absolute convergence of a nonzero Eisenstein row
in the radial coordinate used for the Gaussian Mellin integral. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRowRadius (c : Eisenstein) (p : ℂ × ℝ) (d : Eisenstein) : ℝ :=
  Complex.normSq (p.1+(d:ℂ)/(c:ℂ))+p.2^2

lemma cubicThetaRowRadius_pos (c d : Eisenstein) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < cubicThetaRowRadius c p d :=
  add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hp)

lemma cubicThetaRowRadius_scale {c : Eisenstein} (hc : c ≠ 0)
    (p : ℂ × ℝ) (d : Eisenstein) :
    norm c*cubicThetaRowRadius c p d =
      Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2 := by
  have hcC : (c:ℂ) ≠ 0 := fun h => hc (Subtype.ext h)
  unfold cubicThetaRowRadius
  rw [mul_add]
  congr 1
  change Complex.normSq (c:ℂ)*Complex.normSq (p.1+(d:ℂ)/(c:ℂ)) = _
  rw [← map_mul, mul_add, mul_div_cancel₀ _ hcC]

lemma cubicThetaEisensteinGridTerm_row {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (d : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm (c,d) p s = cubicThetaEisensteinWeight c d*
      ((p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2):ℝ):ℂ)^s := by
  by_cases hd : primary d ∧ IsCoprime c d <;>
    simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,
      cubicThetaEisensteinWeight,hc,hd]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaRowRadius_complex_power {c : Eisenstein} (hc : c ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) (d : Eisenstein) (s : ℂ) :
    ((p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2):ℝ):ℂ)^s =
      ((p.2/norm c:ℝ):ℂ)^s*(cubicThetaRowRadius c p d:ℂ)^(-s) := by
  have hN := norm_pos_of_ne_zero hc
  have hR := cubicThetaRowRadius_pos c d hp
  rw [← cubicThetaRowRadius_scale hc]
  rw [show p.2/(norm c*cubicThetaRowRadius c p d) =
    (p.2/norm c)/cubicThetaRowRadius c p d by ring]
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (div_pos hp hN).le hR.le,
    div_eq_mul_inv, Complex.cpow_neg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicTheta_row_power {v : ℝ} (hv : 0<v) {c : Eisenstein} (hc : c≠0) (s : ℂ) :
    ((v/norm c:ℝ):ℂ)^s=(v:ℂ)^s*(norm c:ℂ)^(-s) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hv.le
    (norm_pos_of_ne_zero hc).le,div_eq_mul_inv,Complex.cpow_neg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of each nonzero actual Eisenstein row term with a
translated hyperbolic kernel, and its eigenvalue equation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRowRadius_cartesian (c d : Eisenstein) (x y v : ℝ) :
    cubicThetaRowRadius c (cubicThetaCartesianPoint x y v) d=
      (x+((d:ℂ)/(c:ℂ)).re)^2+(y+((d:ℂ)/(c:ℂ)).im)^2+v^2 := by
  simp only [cubicThetaRowRadius,cubicThetaCartesianPoint,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,sub_zero]
  ring

theorem cubicThetaEisensteinGridTerm_cartesian {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (d : Eisenstein)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint x y v) s=
      (cubicThetaEisensteinWeight c d*(norm c:ℂ)^(-s))*
        cubicThetaCartesianKernel s (x+((d:ℂ)/(c:ℂ)).re) (y+((d:ℂ)/(c:ℂ)).im) v := by
  rw [cubicThetaEisensteinGridTerm_row hc,
    cubicThetaRowRadius_complex_power hc0 (p:=cubicThetaCartesianPoint x y v) hv,
    cubicThetaRowRadius_cartesian]
  rw [show (cubicThetaCartesianPoint x y v).2=v from rfl,cubicTheta_row_power hv hc0]
  unfold cubicThetaCartesianKernel
  ring

theorem cubicThetaEisensteinGridTerm_eigenvalue {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (d : Eisenstein)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint x y v) s := by
  rw [cubicThetaHyperbolicOperator_congr
    (fun a b t ht => cubicThetaEisensteinGridTerm_cartesian hc hc0 d s a b ht) x y hv,
    cubicThetaHyperbolicOperator_translate,cubicThetaHyperbolicOperator_kernel s _ _ hv,
    cubicThetaEisensteinGridTerm_cartesian hc hc0 d s x y hv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAllGridEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every literal Eisenstein grid summand satisfies the same spectral
equation, including the distinguished cusp row and the zero extension. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinGridTerm_zero (d : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm (0,d) p s=if d=1 then (p.2:ℂ)^s else 0 := by
  by_cases hd : d=1
  · subst d
    simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,primary_one,
      cubicSymbol_one_lower,norm,isCoprime_zero_left]
  · have hp : ¬(primary d ∧ IsCoprime (0:Eisenstein) d) := by
      intro h
      exact hd (primary_unit_eq_one (isCoprime_zero_left.mp h.2) h.1)
    simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hd,hp]

theorem cubicThetaEisensteinGrid_eigenvalue (c d : Eisenstein) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint x y v) s := by
  by_cases hc0 : c=0
  · subst c
    simp only [cubicThetaEisensteinGridTerm_zero,cubicThetaCartesianPoint]
    by_cases hd : d=1
    · simp only [ite_eq_left hd]
      exact cubicThetaHyperbolicOperator_height s x y hv
    · simp only [ite_eq_right hd,cubicThetaHyperbolicOperator,deriv_const',deriv_const,
        mul_zero,sub_zero,add_zero]
  · by_cases hc : (3:Eisenstein)∣c
    · exact cubicThetaEisensteinGridTerm_eigenvalue hc hc0 d s x y hv
    · have he : (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)=
          (fun _ _ _ => (0:ℂ)) := by
        funext a b t
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]
      rw [he]
      simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc,
        cubicThetaHyperbolicOperator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact frequency powers in the fixed-angular theta Mellin transform. -/
noncomputable section
namespace CubicFirstMoment

/-- The frequency multiplier produced by the derivative of order |ell|,
with its signed angular component kept explicit. -/
def cubicThetaAngularCoefficient (a : Eisenstein → ℂ) (ℓ : ℤ) (n : Eisenstein) : ℂ :=
  (‖cubicThetaFrequency n‖:ℂ)^ℓ.natAbs*theta ℓ n*a n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularExponential
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential cusp decay survives every fixed angular frequency power. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAngularExpConstant (C : ℝ) (ℓ : ℤ) : ℝ :=
  (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ))*
    ∑' n : Eisenstein, norm n^(-5/3:ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCongruenceCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite set of coset charts for the actual principal level-three
subgroup. Finiteness comes from the already constructed residue ring. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFiniteCongruenceCover :
    ∃ S : Finset SL(2,Eisenstein), ∀ g : SL(2,Eisenstein),
      ∃ δ ∈ S, ∃ k : cubicThetaPrincipalGroup, g=δ*k.val := by
  classical
  let : Finite (Residues (3:Eisenstein)) := finite_residues (by norm_num)
  let : Fintype (Residues (3:Eisenstein)) := Fintype.ofFinite _
  let f : SL(2,Eisenstein) →* SL(2,Residues (3:Eisenstein)) := Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))
  let R := f.range
  let : Fintype R := Fintype.ofFinite R
  let rep : R → SL(2,Eisenstein) := fun x => Classical.choose x.property
  have hrep (x : R) : f (rep x)=x.val := Classical.choose_spec x.property
  refine ⟨Finset.univ.image rep,?_⟩
  intro g
  let x : R := ⟨f g,g,rfl⟩
  let δ := rep x
  have hδ : f δ=f g := hrep x
  have hk : δ⁻¹*g ∈ cubicThetaPrincipalGroup := by
    change f (δ⁻¹*g)=1
    rw [map_mul,map_inv,hδ,inv_mul_cancel]
  let k : cubicThetaPrincipalGroup := ⟨δ⁻¹*g,hk⟩
  refine ⟨δ,Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩,k,?_⟩
  change g=δ*(δ⁻¹*g)
  group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSiegelReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicTheta_nearest_normSq_bound (z : ℂ) :
    Complex.normSq (z-(nearestEisenstein z:ℂ)) ≤ 3/4 := by
  let a := z.re+z.im/Real.sqrt 3
  let b := 2*z.im/Real.sqrt 3
  have he : z-(nearestEisenstein z:ℂ)=
      ((a-round a:ℝ):ℂ)+((b-round b:ℝ):ℂ)*omega := by
    conv_lhs => lhs; rw [complex_coordinates z]
    simp only [nearestEisenstein,ofCoords_coe]
    dsimp [a,b]
    push_cast
    ring
  have ha : (a-round a)^2 ≤ (1/2:ℝ)^2 := sq_le_sq.mpr (by simpa using abs_sub_round a)
  have hb : (b-round b)^2 ≤ (1/2:ℝ)^2 := sq_le_sq.mpr (by simpa using abs_sub_round b)
  rw [he,real_coordinates_norm]
  nlinarith [sq_nonneg (a-round a+b-round b)]

def cubicThetaFullTranslation (m : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![1,m;0,1],by simp [Matrix.det_fin_two]⟩

lemma cubicThetaFullTranslation_complex (m : Eisenstein) :
    cubicThetaFullComplex (cubicThetaFullTranslation m)=cubicThetaTranslationMatrix (m:ℂ) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCoreCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaCompactCore (S : Finset SL(2,Eisenstein)) (V : ℝ) : Set (ℂ × ℝ) :=
  ⋃ δ∈S, cubicThetaMobius (cubicThetaFullComplex δ⁻¹) '' cubicThetaSiegelCore V

def cubicThetaCuspCharts (S : Finset SL(2,Eisenstein)) (V : ℝ) : Set (ℂ × ℝ) :=
  ⋃ δ∈S, cubicThetaMobius (cubicThetaFullComplex δ⁻¹) '' {q | q∈cubicThetaSiegelSet ∧ V<q.2}

lemma cubicThetaCompactCore_compact (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    IsCompact (cubicThetaCompactCore S V) := by
  apply S.isCompact_biUnion
  intro δ _
  apply (cubicThetaSiegelCore_compact V).image_of_continuousOn
  exact cubicThetaMobius_continuousOn _ (fun _ hp => cubicThetaSiegelCore_positive hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic separation of the high cusp. Two points above height one
can be equivalent under the principal group only by the actual period
lattice 3 times the Eisenstein integers. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipal_parabolic (g : cubicThetaPrincipalGroup) (hc : g.val 1 0=0) :
    g.val 0 0=1 ∧ g.val 1 1=1 := by
  have hu := cubicThetaPrincipalGroup_column_coprime g
  rw [hc] at hu
  have ha := primary_unit_eq_one (isCoprime_zero_right.mp hu)
    (cubicThetaPrincipalGroup_diagonal_primary g).1
  have hd := cubicThetaPrincipalGroup_det g
  rw [ha,hc,one_mul,mul_zero,sub_zero] at hd
  exact ⟨ha,hd⟩

lemma cubicThetaPrincipal_high_translation (g : cubicThetaPrincipalGroup)
    {p : CubicThetaPoint} (hp : 1<p.val.2) (hq : 1<(g • p).val.2) :
    ∃ w : Eisenstein, (g • p).val=(p.val.1+(3:ℂ)*(w:ℂ),p.val.2) := by
  have hq' : 1<(cubicThetaMobius (cubicThetaFullComplex g.val) p.val).2 := hq
  have hc := cubicThetaMobius_high_overlap g.val hp hq'
  obtain ⟨ha,hd⟩ := cubicThetaPrincipal_parabolic g hc
  obtain ⟨w,hw⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
  refine ⟨w,?_⟩
  change cubicThetaMobius (cubicThetaFullComplex g.val) p.val=_
  have ha' : cubicThetaFullComplex g.val 0 0=1 := congrArg (fun z : Eisenstein => (z:ℂ)) ha
  have hd' : cubicThetaFullComplex g.val 1 1=1 := congrArg (fun z : Eisenstein => (z:ℂ)) hd
  have hc' : cubicThetaFullComplex g.val 1 0=0 := congrArg (fun z : Eisenstein => (z:ℂ)) hc
  have hb' : cubicThetaFullComplex g.val 0 1=(3:ℂ)*(w:ℂ) := by
    change ((g.val 0 1:Eisenstein):ℂ)=(3:ℂ)*(w:ℂ)
    have he := congrArg (fun z : Eisenstein => (z:ℂ)) hw
    change ((g.val 0 1:Eisenstein):ℂ)=((3:Eisenstein):ℂ)*(w:ℂ) at he
    exact he
  simp [cubicThetaMobius,cubicThetaMobiusDenominator,cubicThetaMobiusNumerator,ha',hd',hc',hb']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance cubicThetaPrincipalGroup_countable : Countable cubicThetaPrincipalGroup := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let : Countable (Matrix (Fin 2) (Fin 2) Eisenstein) := by
    change Countable (Fin 2 → Fin 2 → Eisenstein)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hi : Function.Injective (fun g : Matrix.SpecialLinearGroup (Fin 2) Eisenstein => g.val) := by
    intro g h he
    exact Subtype.ext he
  let : Countable (Matrix.SpecialLinearGroup (Fin 2) Eisenstein) := hi.countable
  have hj : Function.Injective (fun g : cubicThetaPrincipalGroup => g.val) := by
    intro g h he
    exact Subtype.ext he
  exact hj.countable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPointHeight_full_smul_le (g : SL(2,Eisenstein)) (p : CubicThetaPoint) :
    cubicThetaPointHeight (g • p) ≤ max (cubicThetaPointHeight p) (1/cubicThetaPointHeight p) := by
  by_cases hc : g 1 0=0
  · have hdet : g 0 0*g 1 1=1 := by
      simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
    have hu : IsUnit (g 1 1) := isUnit_iff_exists_inv'.mpr ⟨g 0 0,hdet⟩
    have hc' : cubicThetaFullComplex g 1 0=0 := congrArg (fun z : Eisenstein => (z:ℂ)) hc
    have hd' : Complex.normSq (cubicThetaFullComplex g 1 1)=1 := norm_of_isUnit hu
    change p.val.2/cubicThetaMobiusDenominator (cubicThetaFullComplex g) p.val≤_
    simp only [cubicThetaMobiusDenominator,hc',zero_mul,zero_add,hd',
      Complex.normSq_zero,add_zero,div_one]
    exact le_max_left _ _
  · have hb := cubicThetaMobius_height_product_le g hc p.property
    have hb' : cubicThetaPointHeight (g • p)≤1/cubicThetaPointHeight p :=
      (le_div_iff₀ (cubicThetaPointHeight_pos p)).mpr hb
    exact hb'.trans (le_max_right _ _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaQuotientCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaCompactCore_positive (S : Finset SL(2,Eisenstein)) (V : ℝ)
    {p : ℂ × ℝ} (hp : p∈cubicThetaCompactCore S V) : 0<p.2 := by
  obtain ⟨δ,hδ⟩ := mem_iUnion.mp hp
  obtain ⟨_,q,hq,rfl⟩ := mem_iUnion.mp hδ
  exact cubicThetaMobius_height_pos _ (cubicThetaSiegelCore_positive hq)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPoincareTerm (ψ : C_c(CubicThetaPoint,ℂ))
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) : ℂ :=
  star (cubicThetaKubotaValue g)*ψ (g • p)

lemma cubicThetaPoincareTerm_translate (ψ : C_c(CubicThetaPoint,ℂ))
    (g h : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaPoincareTerm ψ g (h • p)=
      cubicThetaKubotaValue h*cubicThetaPoincareTerm ψ (g*h) p := by
  have hu : cubicThetaKubotaValue h*star (cubicThetaKubotaValue h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (cubicThetaKubotaValue h*star (cubicThetaKubotaValue h))*
      cubicThetaPoincareTerm ψ g (h • p) := by rw [hu,one_mul]
    _ = _ := by
      simp only [cubicThetaPoincareTerm,cubicThetaKubotaValue_mul,star_mul,mul_smul]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPoincareSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPointInclusion_action (g : cubicThetaPrincipalGroup)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPointInclusion.symm (cubicThetaMobius (cubicThetaPrincipalComplex g) y)=
      g • cubicThetaPointInclusion.symm y := by
  have hy' : y∈cubicThetaPointInclusion.target := by
    rwa [cubicThetaPointInclusion_target]
  have hgy : cubicThetaMobius (cubicThetaPrincipalComplex g) y∈cubicThetaPointInclusion.target := by
    rw [cubicThetaPointInclusion_target]
    exact cubicThetaMobius_height_pos _ hy
  have h₁ := cubicThetaPointInclusion.right_inv hy'
  have h₂ := cubicThetaPointInclusion.right_inv hgy
  change (cubicThetaPointInclusion.symm y).val=y at h₁
  change (cubicThetaPointInclusion.symm (cubicThetaMobius (cubicThetaPrincipalComplex g) y)).val=_ at h₂
  apply Subtype.ext
  change (cubicThetaPointInclusion.symm (cubicThetaMobius (cubicThetaPrincipalComplex g) y)).val=
    cubicThetaMobius (cubicThetaPrincipalComplex g) (cubicThetaPointInclusion.symm y).val
  simpa only [h₁] using h₂

lemma cubicThetaPoincareTerm_contDiffAt (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ ∞ (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) (g : cubicThetaPrincipalGroup)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    ContDiffAt ℝ ∞ (fun x => cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y := by
  have hopen : IsOpen {x : ℂ × ℝ | 0<x.2} := isOpen_lt continuous_const continuous_snd
  have hs := hψ.contDiffAt (hopen.mem_nhds (cubicThetaMobius_height_pos
    (cubicThetaPrincipalComplex g) hy))
  have hcomp := hs.comp y (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g) hy)
  have hc : ContDiffAt ℝ ∞ (fun _ : ℂ × ℝ => star (cubicThetaKubotaValue g)) y := contDiffAt_const
  apply (hc.mul hcomp).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hy] with x hx
  simp only [cubicThetaPoincareTerm,Function.comp_def,cubicThetaPointInclusion_action g hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrincipalTranslation_coordinates (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaPointCoordinates (cubicThetaPrincipalTranslation w • p)=
      ((cubicThetaPointCoordinates p).1+3*(w:ℂ),(cubicThetaPointCoordinates p).2) := by
  change cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) p.val=_
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
  push_cast
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridAnalytic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate analyticity of every actual Eisenstein summand in the
positive upper half-space. -/
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisensteinGrid_analytic (c d : Eisenstein) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateAnalytic
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s) x y v := by
  by_cases hc0 : c=0
  · subst c
    simp only [CubicThetaCoordinateAnalytic,cubicThetaEisensteinGridTerm_zero,cubicThetaCartesianPoint]
    by_cases hd : d=1
    · simp only [ite_eq_left hd]
      exact ⟨analyticAt_const,analyticAt_const,cubicThetaHeightPower_analytic s hv⟩
    · simp only [ite_eq_right hd]
      exact ⟨analyticAt_const,analyticAt_const,analyticAt_const⟩
  · by_cases hc : (3:Eisenstein)∣c
    · exact cubicThetaCoordinateAnalytic_congr
        (fun a b t ht => cubicThetaEisensteinGridTerm_cartesian hc hc0 d s a b ht) hv
        (cubicThetaCoordinateAnalytic_translated s
          (cubicThetaEisensteinWeight c d*(norm c:ℂ)^(-s))
          ((d:ℂ)/(c:ℂ)).re ((d:ℂ)/(c:ℂ)).im x y hv)
    · have he : (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)=
          (fun _ _ _ => (0:ℂ)) := by
        funext a b t
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]
      rw [he]
      exact ⟨analyticAt_const,analyticAt_const,analyticAt_const⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateAxis
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate lines used for the spatial derivatives of the series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinateLine_analytic (k : CubicThetaAxis) (cd : Eisenstein × Eisenstein)
    (s : ℂ) (x y v t : ℝ) (ht : 0<(cubicThetaCoordinateLine k x y v t).2) :
    AnalyticAt ℝ (fun w : ℝ => cubicThetaEisensteinGridTerm cd
      (cubicThetaCoordinateLine k x y v w) s) t := by
  cases k with
  | x => exact (cubicThetaEisensteinGrid_analytic cd.1 cd.2 s t y ht).1
  | y => exact (cubicThetaEisensteinGrid_analytic cd.1 cd.2 s x t ht).2.1
  | height => exact (cubicThetaEisensteinGrid_analytic cd.1 cd.2 s x y ht).2.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridJets
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative bounds for all actual grid summands, with the zero row and
the inadmissible-pair extension included. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisensteinGrid_jetBound (c d : Eisenstein) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)
      s x y v := by
  by_cases hc0 : c=0
  · subst c
    simp only [cubicThetaEisensteinGridTerm_zero,cubicThetaCartesianPoint]
    by_cases hd : d=1
    · simp only [ite_eq_left hd]
      exact cubicThetaHeightPower_jetBound s x y hv
    · simp only [ite_eq_right hd]
      exact cubicThetaZero_jetBound s x y v
  · by_cases hc : (3:Eisenstein)∣c
    · exact cubicThetaCoordinateJetBound_congr
        (fun a b t ht => cubicThetaEisensteinGridTerm_cartesian hc hc0 d s a b ht) hv
        (cubicThetaCoordinateJetBound_translate
          (cubicThetaEisensteinWeight c d*(norm c:ℂ)^(-s))
          ((d:ℂ)/(c:ℂ)).re ((d:ℂ)/(c:ℂ)).im x y v
          (cubicThetaCartesian_jetBound s _ _ hv))
    · have he : (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)=
          (fun _ _ _ => (0:ℂ)) := by
        funext a b t
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]
      rw [he]
      exact cubicThetaZero_jetBound s x y v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common summable majorant for the literal grid, uniform in a
positive-height region with bounded height constant. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGridDecay (s : ℂ) (cd : Eisenstein × Eisenstein) : ℝ :=
  (1+norm cd.1)^(-s.re/2)*(1+norm cd.2)^(-s.re/2)

lemma cubicThetaGridDecay_nonneg (s : ℂ) (cd : Eisenstein × Eisenstein) :
    0 ≤ cubicThetaGridDecay s cd := by
  unfold cubicThetaGridDecay
  exact mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg cd.1]) _)
    (Real.rpow_nonneg (by linarith [norm_nonneg cd.2]) _)

lemma cubicThetaGridDecay_summable {s : ℂ} (hs : 2 < s.re) :
    Summable (cubicThetaGridDecay s) := by
  have h := summable_eisenstein_one_add_norm (show 1 < s.re/2 by linarith)
  change Summable (fun cd : Eisenstein × Eisenstein =>
    (1+norm cd.1)^(-s.re/2)*(1+norm cd.2)^(-s.re/2))
  simpa only [neg_div] using summable_mul_of_summable_norm h.norm h.norm

theorem cubicThetaEisensteinGridTerm_bound (cd : Eisenstein × Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    ‖cubicThetaEisensteinGridTerm cd p s‖ ≤
      (p.2*cubicThetaHeightConstant p)^s.re*cubicThetaGridDecay s cd := by
  by_cases hc : cubicThetaAdmissiblePair cd
  · have h := cubicThetaEisensteinTerm_bound (cubicThetaBottomRowEquiv.symm ⟨cd,hc⟩) hp hs
    rw [←cubicThetaEisensteinGridTerm_admissible ⟨cd,hc⟩] at h
    exact h
  · simp only [cubicThetaEisensteinGridTerm,hc,ite_false, if_false,norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (mul_pos hp (cubicThetaHeightConstant_pos hp)).le _)
      (cubicThetaGridDecay_nonneg s cd)

lemma cubicThetaEisensteinGridTerm_uniform_bound (cd : Eisenstein × Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) {H : ℝ}
    (hH : p.2*cubicThetaHeightConstant p ≤ H) :
    ‖cubicThetaEisensteinGridTerm cd p s‖ ≤ H^s.re*cubicThetaGridDecay s cd := by
  apply (cubicThetaEisensteinGridTerm_bound cd hp hs).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (mul_pos hp (cubicThetaHeightConstant_pos hp)).le hH (by linarith))
    (cubicThetaGridDecay_nonneg s cd)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridLocalJets
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable bounds for both derivatives on an actual coordinate
neighborhood. No derivative or normal-convergence assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinateLine_jetBound (k : CubicThetaAxis)
    (cd : Eisenstein × Eisenstein) (s : ℂ) (x y v t : ℝ)
    (ht : 0<(cubicThetaCoordinateLine k x y v t).2) :
    ‖deriv (fun w => cubicThetaEisensteinGridTerm cd
        (cubicThetaCoordinateLine k x y v w) s) t‖ ≤
      ‖cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s‖*
        (cubicThetaFirstJetConstant s/(cubicThetaCoordinateLine k x y v t).2) ∧
    ‖deriv (deriv (fun w => cubicThetaEisensteinGridTerm cd
        (cubicThetaCoordinateLine k x y v w) s)) t‖ ≤
      ‖cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s‖*
        (cubicThetaSecondJetConstant s/(cubicThetaCoordinateLine k x y v t).2^2) := by
  cases k with
  | x => exact cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s t y ht .x
  | y => exact cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s x t ht .y
  | height => exact cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s x y ht .height

theorem cubicThetaCoordinate_local_jets (k : CubicThetaAxis) (s : ℂ)
    (hs : 2 < s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ∃ r : ℝ, 0 < r ∧ ∃ u₁ u₂ : (Eisenstein × Eisenstein) → ℝ,
      Summable u₁ ∧ Summable u₂ ∧
      ∀ cd t, t ∈ Set.Ioo (cubicThetaCoordinateCenter k x y v-r)
        (cubicThetaCoordinateCenter k x y v+r) →
      0<(cubicThetaCoordinateLine k x y v t).2 ∧
      ‖deriv (fun w => cubicThetaEisensteinGridTerm cd
          (cubicThetaCoordinateLine k x y v w) s) t‖ ≤ u₁ cd ∧
      ‖deriv (deriv (fun w => cubicThetaEisensteinGridTerm cd
          (cubicThetaCoordinateLine k x y v w) s)) t‖ ≤ u₂ cd := by
  obtain ⟨r,hr,hbudget⟩ := cubicThetaCoordinate_local_budget k x y hv
  let a := v/2
  let H := v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1
  let u₁ := fun cd => (H^s.re*(cubicThetaFirstJetConstant s/a))*cubicThetaGridDecay s cd
  let u₂ := fun cd => (H^s.re*(cubicThetaSecondJetConstant s/a^2))*cubicThetaGridDecay s cd
  refine ⟨r,hr,u₁,u₂,(cubicThetaGridDecay_summable hs).mul_left _,
    (cubicThetaGridDecay_summable hs).mul_left _,?_⟩
  intro cd t ht
  obtain ⟨ha,hH⟩ := hbudget t ht
  have ha0 : 0<a := by dsimp [a]; positivity
  have hp : 0<(cubicThetaCoordinateLine k x y v t).2 := ha0.trans ha
  have hbound := cubicThetaEisensteinGridTerm_uniform_bound cd hp hs hH.le
  have hj := cubicThetaCoordinateLine_jetBound k cd s x y v t hp
  have hn := cubicThetaJetConstants_nonneg s
  refine ⟨hp,?_,?_⟩
  · have h := uniform_ratio_bound hj.1 hbound (_root_.norm_nonneg _) hn.1 ha0 ha.le
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [u₁,H]
    ring
  · have hasq : a^2 ≤ (cubicThetaCoordinateLine k x y v t).2^2 :=
      (sq_le_sq₀ ha0.le hp.le).mpr ha.le
    have h := uniform_ratio_bound hj.2 hbound (_root_.norm_nonneg _) hn.2
      (sq_pos_of_pos ha0) hasq
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [u₂,H]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGridDifferentiation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual termwise first and second differentiation of the Eisenstein
grid on its initial half-plane. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGrid_coordinate_derivs (k : CubicThetaAxis)
    (s : ℂ) (hs : 2 < s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    let f := fun cd : Eisenstein × Eisenstein => fun t : ℝ =>
      cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s
    let t := cubicThetaCoordinateCenter k x y v
    deriv (fun w => ∑' cd, f cd w) t=(∑' cd, deriv (f cd) t) ∧
    deriv (deriv (fun w => ∑' cd, f cd w)) t=(∑' cd, deriv (deriv (f cd)) t) ∧
    Summable (fun cd => deriv (f cd) t) ∧
    Summable (fun cd => deriv (deriv (f cd)) t) := by
  obtain ⟨r,hr,u₁,u₂,hu₁,hu₂,hbound⟩ := cubicThetaCoordinate_local_jets k s hs x y hv
  dsimp only
  have hx : cubicThetaCoordinateCenter k x y v ∈
      Set.Ioo (cubicThetaCoordinateCenter k x y v-r) (cubicThetaCoordinateCenter k x y v+r) :=
    ⟨by linarith,by linarith⟩
  refine cubicTheta_twice_deriv_tsum hu₁ hu₂ hx ?_ ?_ ?_ ?_
  · intro cd t ht
    exact cubicThetaCoordinateLine_analytic k cd s x y v t (hbound cd t ht).1
  · intro cd t ht
    exact (hbound cd t ht).2.1
  · intro cd t ht
    exact (hbound cd t ht).2.2
  · simpa only [cubicThetaCoordinateLine_center] using
      (cubicThetaEisensteinGrid_summable (p:=cubicThetaCartesianPoint x y v) hv hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming cutoff series uses the actual primitive bottom rows.
Above the arithmetic cusp threshold at most one row contributes. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaIncomingRows_unique {p : ℂ × ℝ} (hp : 0<p.2)
    {r t : CubicThetaBottomRow} (hr : 1 < r.height p) (ht : 1<t.height p) : r=t := by
  let g := r.completion
  let q := cubicThetaMobius (cubicThetaPrincipalComplex g) p
  have hq : 0<q.2 := cubicThetaMobius_height_pos _ hp
  have hq1 : 1<q.2 := by
    change 1<(cubicThetaBottomRow r.completion).height p
    rwa [r.completion_row]
  have hinv : cubicThetaMobius (cubicThetaPrincipalComplex g⁻¹) q=p := by
    dsimp [q]
    rw [cubicThetaMobius_comp _ _ hp,← map_mul,inv_mul_cancel,map_one,cubicThetaMobius_one]
  have htq : 1<(t.rightMul g⁻¹).height q := by
    rw [CubicThetaBottomRow.height_rightMul _ _ hq,hinv]
    exact ht
  have htz : t.rightMul g⁻¹=cubicThetaZeroRow :=
    (CubicThetaBottomRow.c_zero_iff _).mp
      ((t.rightMul g⁻¹).high_height_c_zero hq1 htq)
  have hrz : r.rightMul g⁻¹=cubicThetaZeroRow := by
    calc
      _ = (cubicThetaBottomRow g).rightMul g⁻¹ := by
        rw [show cubicThetaBottomRow g=r from r.completion_row]
      _ = cubicThetaBottomRow (g*g⁻¹) := cubicThetaBottomRow_mul _ _
      _ = cubicThetaZeroRow := by rw [mul_inv_cancel]; rfl
  exact (CubicThetaBottomRow.rightMulEquiv g⁻¹).injective (hrz.trans htz.symm)

def cubicThetaIncomingTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicThetaCuspCutoff (r.height p)*cubicThetaEisensteinTerm r p s

lemma cubicThetaIncomingTerm_high {r : CubicThetaBottomRow} {p : ℂ × ℝ} {s : ℂ}
    (h : cubicThetaIncomingTerm r p s≠0) : 1 < r.height p := by
  by_contra hn
  have hz := cubicThetaCuspCutoff_zero (le_of_not_gt hn)
  exact h (by simp only [cubicThetaIncomingTerm,hz,zero_mul])

lemma cubicThetaIncomingTerm_finite {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    (Function.support (fun r => cubicThetaIncomingTerm r p s)).Finite := by
  apply Set.Subsingleton.finite
  intro r hr t ht
  exact cubicThetaIncomingRows_unique hp
    (cubicThetaIncomingTerm_high hr) (cubicThetaIncomingTerm_high ht)

def cubicThetaIncomingEisenstein (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaIncomingTerm r p s

lemma cubicThetaIncomingTerm_translate (r : CubicThetaBottomRow) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingTerm (r.rightMul g) p s := by
  rw [cubicThetaIncomingTerm,cubicThetaIncomingTerm,
    ← CubicThetaBottomRow.height_rightMul r g hp,cubicThetaEisensteinTerm_translate r g hp s]
  ring

theorem cubicThetaIncomingEisenstein_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaIncomingEisenstein (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaIncomingEisenstein p s := by
  unfold cubicThetaIncomingEisenstein
  simp_rw [cubicThetaIncomingTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaIncomingTerm r p s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingLocalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact positive-height set meets only finitely many incoming
row supports. The bound is arithmetic and is uniform in the spectral
parameter, so the resulting finite-sum identities support differentiation. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaIncomingRows_compact {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ r∉S, r.height p<1 := by
  classical
  have hc : ContinuousOn (fun p : ℂ × ℝ => p.2*cubicThetaHeightConstant p) K := by
    intro p hp
    unfold cubicThetaHeightConstant
    fun_prop (disch := exact pow_ne_zero _ (hpos p hp).ne')
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r t h
    exact CubicThetaBottomRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hfin : {r : CubicThetaBottomRow | norm r.c≤B ∧ norm r.d≤B}.Finite :=
    ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  refine ⟨hfin.toFinset,?_⟩
  intro p hp r hr
  apply lt_of_not_ge
  intro hhigh
  have hn : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hrow : 1+norm r.c+norm r.d≤p.2*cubicThetaHeightConstant p :=
    by simpa only [one_mul] using
      (le_div_iff₀ hn).mp (hhigh.trans (r.height_le (hpos p hp)))
  have hb : p.2*cubicThetaHeightConstant p≤B :=
    (le_abs_self _).trans (hB p hp)
  apply hr
  apply hfin.mem_toFinset.mpr
  constructor <;> linarith [norm_nonneg r.c,norm_nonneg r.d]

theorem cubicThetaIncomingEisenstein_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaIncomingEisenstein p s=∑ r∈S, cubicThetaIncomingTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ?_⟩
  apply tsum_eq_sum
  intro r hr
  unfold cubicThetaIncomingTerm
  rw [cubicThetaCuspCutoff_zero (hS p hp r hr).le,zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingSmooth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint spatial smoothness of the actual incoming arithmetic series.
The compact row bound makes the sum locally finite before differentiation. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaIncomingTerm r q s) p := by
  have hh := r.height_contDiffAt hp
  have hc := cubicThetaCuspCutoff_smooth.contDiffAt.comp p hh
  have hpow := (cubicThetaHeightPower_analytic s (r.height_pos hp)).contDiffAt.comp p hh
  exact hc.mul (contDiffAt_const.mul hpow)

theorem cubicThetaIncomingEisenstein_contDiffOn (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaIncomingEisenstein p s)
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum hK hKpos
  have he : (fun q => cubicThetaIncomingEisenstein q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaIncomingTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaIncomingTerm r q s) p :=
    ContDiffAt.sum (fun r _ => cubicThetaIncomingTerm_contDiffAt r s hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic forcing series is locally a finite sum,
uniformly in the spectral parameter. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaForcingTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  star r.phase*cubicThetaIncomingForcing s (r.height p)

def cubicThetaForcingSeries (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaForcingTerm r p s

lemma cubicThetaForcingTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaForcingTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaForcingTerm (r.rightMul g) p s := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g)=1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaForcingTerm,cubicThetaForcingTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*cubicThetaIncomingForcing s
          (r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p))) := by rw [hu,one_mul]
    _ = _ := by ring

theorem cubicThetaForcingSeries_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaForcingSeries (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaForcingSeries p s := by
  unfold cubicThetaForcingSeries
  simp_rw [cubicThetaForcingTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaForcingTerm r p s)

theorem cubicThetaForcingSeries_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaIncomingEisenstein p s=∑ r∈S, cubicThetaIncomingTerm r p s ∧
      cubicThetaForcingSeries p s=∑ r∈S, cubicThetaForcingTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ⟨?_,?_⟩⟩
  · apply tsum_eq_sum
    intro r hr
    unfold cubicThetaIncomingTerm
    rw [cubicThetaCuspCutoff_zero (hS p hp r hr).le,zero_mul]
  · apply tsum_eq_sum
    intro r hr
    unfold cubicThetaForcingTerm
    rw [cubicThetaIncomingForcing_zero s (Or.inl (hS p hp r hr)),mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcingSmooth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual forcing follows from the compact cutoff
and the locally finite arithmetic row expansion. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaForcingTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaForcingTerm r q s) p :=
  contDiffAt_const.mul ((cubicThetaIncomingForcing_contDiffAt s (r.height_pos hp)).comp p
    (r.height_contDiffAt hp))

theorem cubicThetaForcingSeries_contDiffOn (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaForcingSeries p s)
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_compact_sum hK hKpos
  have he : (fun q => cubicThetaForcingSeries q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaForcingTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact (hS q hq s).2
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaForcingTerm r q s) p :=
    ContDiffAt.sum (fun r _ => cubicThetaForcingTerm_contDiffAt r s hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAnnularSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed open-annulus transport of a continuous radial profile.
At most one actual primitive row contributes at any point. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaBottomRow_countable : Countable CubicThetaBottomRow := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  exact Function.Injective.countable (f:=fun r : CubicThetaBottomRow => (r.c,r.d))
    (fun _ _ h => CubicThetaBottomRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

def cubicThetaAnnularTerm (f : C(CubicThetaForcingBand,ℂ))
    (r : CubicThetaBottomRow) (p : CubicThetaPoint) : ℂ :=
  if 1 < r.height p.val ∧ r.height p.val<2 then
    star r.phase*f (projIcc 1 2 (by norm_num) (r.height p.val)) else 0

def cubicThetaAnnularSeries (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaAnnularTerm f r p

lemma cubicThetaAnnularTerm_high {f : C(CubicThetaForcingBand,ℂ)}
    {r : CubicThetaBottomRow} {p : CubicThetaPoint}
    (h : cubicThetaAnnularTerm f r p≠0) : 1 < r.height p.val ∧ r.height p.val<2 := by
  by_contra hn
  exact h (ite_eq_right hn)

lemma cubicThetaAnnularTerm_support (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    (Function.support (fun r => cubicThetaAnnularTerm f r p)).Subsingleton := by
  intro r hr t ht
  exact cubicThetaIncomingRows_unique p.property
    (cubicThetaAnnularTerm_high hr).1 (cubicThetaAnnularTerm_high ht).1

lemma cubicThetaAnnularTerm_measurable (f : C(CubicThetaForcingBand,ℂ))
    (r : CubicThetaBottomRow) : Measurable (cubicThetaAnnularTerm f r) := by
  have hh := r.pointHeight_continuous
  have hm : MeasurableSet {p : CubicThetaPoint | 1 < r.height p.val ∧ r.height p.val<2} :=
    ((isOpen_lt continuous_const hh).inter (isOpen_lt hh continuous_const)).measurableSet
  exact (continuous_const.mul (f.continuous.comp (continuous_projIcc.comp hh))).measurable.ite
    hm measurable_const

lemma cubicThetaAnnularSeries_measurable (f : C(CubicThetaForcingBand,ℂ)) :
    Measurable (cubicThetaAnnularSeries f) :=
  Measurable.tsum (fun r => cubicThetaAnnularTerm_measurable f r)

lemma cubicThetaAnnularTerm_norm (f : C(CubicThetaForcingBand,ℂ))
    (r : CubicThetaBottomRow) (p : CubicThetaPoint) :
    ‖cubicThetaAnnularTerm f r p‖≤‖f‖ := by
  unfold cubicThetaAnnularTerm
  split_ifs
  · rw [norm_mul,norm_star,r.phase_norm,one_mul]
    exact f.norm_coe_le_norm _
  · simpa only [norm_zero] using _root_.norm_nonneg f

lemma cubicThetaAnnularSeries_norm (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    ‖cubicThetaAnnularSeries f p‖≤‖f‖ := by
  classical
  by_cases h : ∃ r, cubicThetaAnnularTerm f r p≠0
  · obtain ⟨r,hr⟩ := h
    have he : cubicThetaAnnularSeries f p=cubicThetaAnnularTerm f r p := by
      apply tsum_eq_single
      intro t ht
      by_contra hn
      exact ht ((cubicThetaAnnularTerm_support f p) hn hr)
    rw [he]
    exact cubicThetaAnnularTerm_norm f r p
  · have hz : ∀ r, cubicThetaAnnularTerm f r p=0 := by simpa using h
    simp only [cubicThetaAnnularSeries,hz,tsum_zero,norm_zero]
    exact _root_.norm_nonneg f

lemma cubicThetaAnnularSeries_add (f g : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    cubicThetaAnnularSeries (f+g) p=cubicThetaAnnularSeries f p+cubicThetaAnnularSeries g p := by
  have he (r : CubicThetaBottomRow) : cubicThetaAnnularTerm (f+g) r p=
      cubicThetaAnnularTerm f r p+cubicThetaAnnularTerm g r p := by
    unfold cubicThetaAnnularTerm
    split_ifs <;> simp only [ContinuousMap.add_apply,mul_add,add_zero]
  simp_rw [cubicThetaAnnularSeries,he]
  exact (summable_of_hasFiniteSupport (cubicThetaAnnularTerm_support f p).finite).tsum_add
    (summable_of_hasFiniteSupport (cubicThetaAnnularTerm_support g p).finite)

lemma cubicThetaAnnularSeries_smul (c : ℂ) (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    cubicThetaAnnularSeries (c • f) p=c*cubicThetaAnnularSeries f p := by
  have he (r : CubicThetaBottomRow) : cubicThetaAnnularTerm (c • f) r p=
      c*cubicThetaAnnularTerm f r p := by
    unfold cubicThetaAnnularTerm
    split_ifs
    · simp only [ContinuousMap.smul_apply,smul_eq_mul]
      ring
    · simp only [mul_zero]
  simp_rw [cubicThetaAnnularSeries,he]
  exact tsum_mul_left

lemma cubicThetaAnnularSeries_forcing (s : ℂ) (p : CubicThetaPoint) :
    cubicThetaAnnularSeries (cubicThetaForcingProfile s) p=cubicThetaForcingSeries p.val s := by
  apply tsum_congr
  intro r
  unfold cubicThetaAnnularTerm cubicThetaForcingTerm
  split_ifs with h
  · rw [projIcc_of_mem (by norm_num) ⟨h.1.le,h.2.le⟩,cubicThetaForcingProfile_apply]
  · have hv : r.height p.val≤1 ∨ 2 ≤ r.height p.val := by
      simpa only [not_and_or,not_lt] using h
    rw [cubicThetaIncomingForcing_zero_closed s hv,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRowMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform denominator bound for nonconstant rows in any integral
cusp. This bound is independent of the congruence class of the row. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCuspRowDenominator (c d : Eisenstein) (z : ℂ) (v : ℝ) : ℝ :=
  Complex.normSq ((c:ℂ)*z+d)+norm c*v^2

lemma cubicThetaCuspRowDenominator_lower (c d : Eisenstein) (z : ℂ) (v : ℝ) :
    norm c*v^2 ≤ cubicThetaCuspRowDenominator c d z v := by
  exact le_add_of_nonneg_left (Complex.normSq_nonneg _)

lemma cubicThetaCuspRowDenominator_pos {c : Eisenstein} (hc : c≠0)
    (d : Eisenstein) (z : ℂ) {v : ℝ} (hv : 0<v) :
    0 < cubicThetaCuspRowDenominator c d z v :=
  (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hv)).trans_le
    (cubicThetaCuspRowDenominator_lower c d z v)

lemma cubicThetaCuspRowDenominator_horizontal {c : Eisenstein} (hc : c≠0)
    (d : Eisenstein) (z : ℂ) {v R : ℝ} (hv : 1≤v) (hz : Complex.normSq z≤R) :
    1+norm d≤(3+2*R)*cubicThetaCuspRowDenominator c d z v := by
  let D := cubicThetaCuspRowDenominator c d z v
  have hD : norm c*v^2≤D := cubicThetaCuspRowDenominator_lower c d z v
  have hc0 := norm_nonneg c
  have hcv : norm c≤D := (le_mul_of_one_le_right hc0 (by nlinarith : 1≤v^2)).trans hD
  have hD0 : 0≤D := hc0.trans hcv
  have hR : 0≤R := (Complex.normSq_nonneg z).trans hz
  have hs : Complex.normSq (((c:ℂ)*z+d)-((c:ℂ)*z))≤
      2*Complex.normSq ((c:ℂ)*z+d)+2*Complex.normSq ((c:ℂ)*z) := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    nlinarith [sq_nonneg (((c:ℂ)*z+d).re+((c:ℂ)*z).re),
      sq_nonneg (((c:ℂ)*z+d).im+((c:ℂ)*z).im)]
  rw [add_sub_cancel_left,Complex.normSq_mul] at hs
  change norm d≤2*Complex.normSq ((c:ℂ)*z+d)+2*(norm c*Complex.normSq z) at hs
  have hprod : norm c*Complex.normSq z≤D*R :=
    mul_le_mul hcv hz (Complex.normSq_nonneg z) hD0
  have hsq : Complex.normSq ((c:ℂ)*z+d)≤D :=
    le_add_of_nonneg_right (mul_nonneg hc0 (sq_nonneg v))
  have hd : norm d≤2*D+2*(D*R) := by
    nlinarith
  have hD1 : 1≤D := (one_le_norm hc).trans hcv
  nlinarith

lemma cubicThetaCuspRowHeight_power {c : Eisenstein} (hc : c≠0)
    (d : Eisenstein) (z : ℂ) {v R σ : ℝ} (hv : 1≤v) (hz : Complex.normSq z≤R)
    (hσ : 2≤σ) :
    (v/cubicThetaCuspRowDenominator c d z v)^σ≤
      (3+2*R)^2*v^(4-σ)*norm c^(-(σ-2))*(1+norm d)^(-2:ℝ) := by
  have hv0 : 0<v := lt_of_lt_of_le zero_lt_one hv
  have hc0 := norm_pos_of_ne_zero hc
  have hD := cubicThetaCuspRowDenominator_pos hc d z hv0
  have hR : 0≤R := (Complex.normSq_nonneg z).trans hz
  have hC : 0<3+2*R := by linarith
  have hd : 0<1+norm d := by linarith [norm_nonneg d]
  have hlo : (1+norm d)/(3+2*R) ≤ cubicThetaCuspRowDenominator c d z v :=
    (div_le_iff₀ hC).mpr (by
      simpa only [mul_comm] using cubicThetaCuspRowDenominator_horizontal hc d z hv hz)
  have h₁ := Real.rpow_le_rpow_of_nonpos (mul_pos hc0 (sq_pos_of_pos hv0))
    (cubicThetaCuspRowDenominator_lower c d z v) (by linarith : -(σ-2)≤0)
  have h₂ := Real.rpow_le_rpow_of_nonpos (div_pos hd hC) hlo (by norm_num : (-2:ℝ)≤0)
  have hs : (cubicThetaCuspRowDenominator c d z v)^(-σ)=
      (cubicThetaCuspRowDenominator c d z v)^(-(σ-2))*
        (cubicThetaCuspRowDenominator c d z v)^(-2:ℝ) := by
    rw [← Real.rpow_add hD]
    congr 1
    ring
  have he₂ : ((1+norm d)/(3+2*R))^(-2:ℝ)=
      (3+2*R)^2*(1+norm d)^(-2:ℝ) := by
    rw [Real.div_rpow hd.le hC.le]
    simp only [Real.rpow_neg hd.le,Real.rpow_neg hC.le,Real.rpow_two]
    field_simp [hd.ne',hC.ne']
  have he₁ : v^σ*(v^2)^(-(σ-2))=v^(4-σ) := by
    rw [← Real.rpow_natCast_mul hv0.le,← Real.rpow_add hv0]
    congr 1
    push_cast
    ring
  calc
    _ = v^σ*(cubicThetaCuspRowDenominator c d z v)^(-σ) := by
      rw [Real.div_rpow hv0.le hD.le,Real.rpow_neg hD.le,div_eq_mul_inv]
    _ = v^σ*((cubicThetaCuspRowDenominator c d z v)^(-(σ-2))*
        (cubicThetaCuspRowDenominator c d z v)^(-2:ℝ)) := by rw [hs]
    _ ≤ v^σ*((norm c*v^2)^(-(σ-2))*((1+norm d)/(3+2*R))^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂
        (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (mul_pos hc0 (sq_pos_of_pos hv0)).le _))
        (Real.rpow_nonneg hv0.le _)
    _ = _ := by
      rw [Real.mul_rpow hc0.le (sq_nonneg v),he₂]
      calc
        _ = (3+2*R)^2*(v^σ*(v^2)^(-(σ-2)))*norm c^(-(σ-2))*(1+norm d)^(-2:ℝ) := by ring
        _ = _ := by rw [he₁]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic difference between Eisenstein and incoming
series, with its absolutely convergent row expansion and all-cusp bound. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticRemainder (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicThetaEisenstein p s-cubicThetaIncomingEisenstein p s

def cubicThetaRemainderRow (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  (1-cubicThetaCuspCutoff (r.height p))*cubicThetaEisensteinTerm r p s

lemma cubicThetaRemainderRow_eq (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaRemainderRow r p s=cubicThetaEisensteinTerm r p s-cubicThetaIncomingTerm r p s := by
  unfold cubicThetaRemainderRow cubicThetaIncomingTerm
  ring

lemma cubicThetaRemainderRow_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) : Summable (fun r => cubicThetaRemainderRow r p s) := by
  simp_rw [cubicThetaRemainderRow_eq]
  exact (cubicThetaEisenstein_summable hp hs).sub
    (summable_of_hasFiniteSupport (cubicThetaIncomingTerm_finite hp s))

theorem cubicThetaArithmeticRemainder_eq_sum {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaArithmeticRemainder p s=∑' r : CubicThetaBottomRow, cubicThetaRemainderRow r p s := by
  simp_rw [cubicThetaRemainderRow_eq]
  exact ((cubicThetaEisenstein_summable hp hs).tsum_sub
    (summable_of_hasFiniteSupport (cubicThetaIncomingTerm_finite hp s))).symm

lemma cubicThetaArithmeticRemainder_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaArithmeticRemainder p s := by
  unfold cubicThetaArithmeticRemainder
  rw [cubicThetaEisenstein_automorphy g hp,cubicThetaIncomingEisenstein_automorphy g hp]
  ring

lemma cubicThetaRemainderRow_norm (r : CubicThetaBottomRow) {p : ℂ × ℝ}
    (hp : 0<p.2) (s : ℂ) :
    ‖cubicThetaRemainderRow r p s‖≤2*(r.height p)^s.re := by
  have hcut : ‖1-cubicThetaCuspCutoff (r.height p)‖≤2 :=
    (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith [cubicThetaCuspCutoff_norm (r.height p)])
  rw [cubicThetaRemainderRow,norm_mul,cubicThetaEisensteinTerm,norm_mul,norm_star,
    r.phase_norm,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (r.height_pos hp)]
  exact mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg (r.height_pos hp).le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSpatialContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint spatial continuity of the actual Eisenstein sum, from its
uniform summable majorant on a positive-height neighborhood. -/
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinTerm_continuousAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaEisensteinTerm r q s) p := by
  have hden : Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2≠0 := by
    intro h
    have he := r.height_pos hp
    simp [CubicThetaBottomRow.height,h] at he
  have hh : ContinuousAt (fun q => r.height q) p := by
    unfold CubicThetaBottomRow.height
    fun_prop
  have hpow : ContinuousAt (fun t : ℝ => (t:ℂ)^s) (r.height p) :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (r.height_pos hp).ne')
  exact continuousAt_const.mul (hpow.comp hh)

lemma cubicThetaEisensteinGridTerm_continuousAt (cd : Eisenstein × Eisenstein) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaEisensteinGridTerm cd q s) p := by
  by_cases hc : cubicThetaAdmissiblePair cd
  · have he : (fun q => cubicThetaEisensteinGridTerm cd q s)=
        (fun q => cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm ⟨cd,hc⟩) q s) :=
      funext (fun q => cubicThetaEisensteinGridTerm_admissible ⟨cd,hc⟩ q s)
    rw [he]
    exact cubicThetaEisensteinTerm_continuousAt _ s hp
  · simp only [cubicThetaEisensteinGridTerm,hc,ite_false, if_false]
    exact continuousAt_const

theorem cubicThetaEisenstein_continuousAt {s : ℂ} (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaEisenstein q s) p := by
  let H := p.2*cubicThetaHeightConstant p+1
  let U : Set (ℂ × ℝ) := {q | 0<q.2 ∧ q.2*cubicThetaHeightConstant q<H}
  have hb : ContinuousAt (fun q : ℂ × ℝ => q.2*cubicThetaHeightConstant q) p := by
    unfold cubicThetaHeightConstant
    have hn : p.2^2≠0 := pow_ne_zero _ hp.ne'
    fun_prop
  have hU : U ∈ 𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt hp).and
      (hb.eventually_lt_const (by dsimp [H]; linarith))
  have hsum := continuousOn_tsum
    (s:=U) (fun cd q hq => (cubicThetaEisensteinGridTerm_continuousAt cd s hq.1).continuousWithinAt)
    ((cubicThetaGridDecay_summable hs).mul_left (H^s.re))
    (fun cd q hq => cubicThetaEisensteinGridTerm_uniform_bound cd hq.1 hs hq.2.le)
  have he : (fun q : ℂ × ℝ => cubicThetaEisenstein q s)=
      (fun q => ∑' cd, cubicThetaEisensteinGridTerm cd q s) :=
    funext (fun q => cubicThetaEisenstein_eq_grid q s)
  rw [he]
  exact hsum.continuousAt hU

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticSection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic Eisenstein-minus-incoming difference is a genuine
continuous automorphic section in the initial convergence half-plane. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticRemainder_continuousAt {s : ℂ} (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaArithmeticRemainder q s) p := by
  have hi := (cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  exact (cubicThetaEisenstein_continuousAt hs hp).sub hi.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSpatialDerivativeBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A joint Frechet derivative bound for the actual Eisenstein summands.
The three proved coordinate bounds control the product-space operator norm. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaEisensteinTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaEisensteinTerm r q s) p := by
  exact contDiffAt_const.mul ((cubicThetaHeightPower_analytic s (r.height_pos hp)).contDiffAt.comp p
    (r.height_contDiffAt hp))

lemma cubicThetaEisensteinGridTerm_contDiffAt (cd : Eisenstein × Eisenstein) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaEisensteinGridTerm cd q s) p := by
  classical
  by_cases hc : cubicThetaAdmissiblePair cd
  · have he : (fun q => cubicThetaEisensteinGridTerm cd q s)=
        (fun q => cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm ⟨cd,hc⟩) q s) :=
      funext (fun q => cubicThetaEisensteinGridTerm_admissible ⟨cd,hc⟩ q s)
    rw [he]
    exact cubicThetaEisensteinTerm_contDiffAt _ s hp
  · simp only [cubicThetaEisensteinGridTerm,hc,ite_false, if_false]
    exact contDiffAt_const

theorem cubicThetaEisensteinGridTerm_fderiv_bound
    (cd : Eisenstein × Eisenstein) (s : ℂ) {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖fderiv ℝ (fun q => cubicThetaEisensteinGridTerm cd q s) p‖≤
      3*(‖cubicThetaEisensteinGridTerm cd p s‖*(cubicThetaFirstJetConstant s/p.2)) := by
  have he : cubicThetaCartesianPoint p.1.re p.1.im p.2=p := by
    apply Prod.ext
    · exact Complex.re_add_im p.1
    · rfl
  have hd := (cubicThetaEisensteinGridTerm_contDiffAt cd s hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := cubicThetaFDeriv_coordinates p.1.re p.1.im p.2 (he ▸ hd)
  rw [he] at hc
  have hj := cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s p.1.re p.1.im hp
  apply cubicThetaComplexProduct_opNorm_le _
    (mul_nonneg (_root_.norm_nonneg _) (div_nonneg (cubicThetaJetConstants_nonneg s).1 hp.le))
  · rw [hc.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .x).1
  · rw [hc.2.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .y).1
  · rw [hc.2.2]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .height).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaJointRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint C1 regularity of the literal arithmetic Eisenstein series.
The locally uniform derivative majorant is proved from its actual rows. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaEisensteinGrid_local_fderiv_bound (s : ℂ) (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : Eisenstein × Eisenstein → ℝ, Summable u ∧
      ∀ cd q, q∈Metric.ball p r → 0<q.2 ∧
        ‖fderiv ℝ (fun z => cubicThetaEisensteinGridTerm cd z s) q‖≤u cd := by
  let a := p.2/2
  let H := p.2*cubicThetaHeightConstant p+1
  have ha : 0<a := half_pos hp
  have hc : ContinuousAt (fun q : ℂ × ℝ => q.2*cubicThetaHeightConstant q) p := by
    unfold cubicThetaHeightConstant
    have hn : p.2^2≠0 := pow_ne_zero _ hp.ne'
    fun_prop
  have hU : {q : ℂ × ℝ | a<q.2 ∧ q.2*cubicThetaHeightConstant q<H}∈𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt (by dsimp [a]; linarith)).and
      (hc.eventually_lt_const (by dsimp [H]; linarith))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  let u := fun cd => (3*(H^s.re*(cubicThetaFirstJetConstant s/a)))*cubicThetaGridDecay s cd
  refine ⟨r,hr,u,(cubicThetaGridDecay_summable hs).mul_left _,?_⟩
  intro cd q hq
  obtain ⟨haq,hH⟩ := hsub hq
  have hq0 := ha.trans haq
  refine ⟨hq0,?_⟩
  have hf := cubicThetaEisensteinGridTerm_uniform_bound cd hq0 hs hH.le
  have hrat : cubicThetaFirstJetConstant s/q.2 ≤ cubicThetaFirstJetConstant s/a :=
    div_le_div_of_nonneg_left (cubicThetaJetConstants_nonneg s).1 ha haq.le
  calc
    _ ≤ 3*(‖cubicThetaEisensteinGridTerm cd q s‖*(cubicThetaFirstJetConstant s/q.2)) :=
      cubicThetaEisensteinGridTerm_fderiv_bound cd s hq0
    _ ≤ 3*((H^s.re*cubicThetaGridDecay s cd)*(cubicThetaFirstJetConstant s/a)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hf hrat (div_nonneg (cubicThetaJetConstants_nonneg s).1 hq0.le)
          ((_root_.norm_nonneg _).trans hf)) (by norm_num)
    _ = u cd := by dsimp [u]; ring

theorem cubicThetaEisenstein_contDiffAt_one {s : ℂ} (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q => cubicThetaEisenstein q s) p := by
  obtain ⟨r,hr,u,hu,hb⟩ := cubicThetaEisensteinGrid_local_fderiv_bound s hs hp
  let f := fun cd : Eisenstein × Eisenstein => fun q => cubicThetaEisensteinGridTerm cd q s
  let df := fun cd : Eisenstein × Eisenstein => fun q => fderiv ℝ (f cd) q
  have hdf cd q (hq : q∈Metric.ball p r) : HasFDerivAt (f cd) (df cd q) q :=
    ((cubicThetaEisensteinGridTerm_contDiffAt cd s (hb cd q hq).1).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hd q (hq : q∈Metric.ball p r) :
      HasFDerivAt (fun q => ∑' cd, f cd q) (∑' cd, df cd q) q :=
    hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball p r).isPreconnected
      hdf (fun cd q hq => (hb cd q hq).2) (Metric.mem_ball_self hr)
      (cubicThetaEisensteinGrid_summable hp hs) hq
  have hdc : ContinuousOn (fun q => ∑' cd, df cd q) (Metric.ball p r) := by
    apply continuousOn_tsum _ hu (fun cd q hq => (hb cd q hq).2)
    intro cd q hq
    exact ((cubicThetaEisensteinGridTerm_contDiffAt cd s (hb cd q hq).1).fderiv_right
      (m:=0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt.continuousWithinAt
  have hc : ContDiffOn ℝ 1 (fun q => ∑' cd, f cd q) (Metric.ball p r) := by
    rw [show (1:ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun q hq => (hd q hq).differentiableAt.differentiableWithinAt,by norm_num,?_⟩
    apply contDiffOn_zero.mpr
    exact hdc.congr (fun q hq => (hd q hq).fderiv)
  have he : (fun q => cubicThetaEisenstein q s)=(fun q => ∑' cd, f cd q) :=
    funext (fun q => cubicThetaEisenstein_eq_grid q s)
  rw [he]
  exact hc.contDiffAt (Metric.ball_mem_nhds p hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEnergy
attribute [-instance] _root_.instMeasurableSpace
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

lemma cubicThetaArithmeticRemainder_contDiffOn_one {s : ℂ} (hs : 2 < s.re) :
    ContDiffOn ℝ 1 (fun p => cubicThetaArithmeticRemainder p s)
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  exact ((cubicThetaEisenstein_contDiffAt_one hs hp).sub
    (((cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).of_le (by norm_num))).contDiffWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Twice continuous coordinate differentiability of the literal
Eisenstein sum, from the existing local summable derivative bounds. -/
noncomputable section
open Set
open scoped Topology ContDiff
namespace CubicFirstMoment

theorem cubicThetaEisenstein_coordinate_contDiffAt
    (k : CubicThetaAxis) (s : ℂ) (hs : 2 < s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s)
      (cubicThetaCoordinateCenter k x y v) := by
  obtain ⟨r,hr,u₁,u₂,hu₁,hu₂,hbound⟩ := cubicThetaCoordinate_local_jets k s hs x y hv
  have he : (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s)=
      (fun t => ∑' cd, cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s) :=
    funext (fun t => cubicThetaEisenstein_eq_grid _ _)
  rw [he]
  exact cubicTheta_twice_contDiffAt_tsum hu₁ hu₂ ⟨by linarith,by linarith⟩
    (fun cd t ht => cubicThetaCoordinateLine_analytic k cd s x y v t (hbound cd t ht).1)
    (fun cd t ht => (hbound cd t ht).2.1)
    (fun cd t ht => (hbound cd t ht).2.2)
    (fun t ht => cubicThetaEisensteinGrid_summable (hbound (0,0) t ht).1 hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinSpectral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual, absolutely convergent Eisenstein series satisfies the
hyperbolic spectral equation on Re(s)>2. The two spatial differentiations
are justified by the proved local summable bounds. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisenstein_eigenvalue (s : ℂ) (hs : 2 < s.re) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaEisenstein (cubicThetaCartesianPoint x y v) s := by
  have hx := cubicThetaEisensteinGrid_coordinate_derivs .x s hs x y hv
  have hy := cubicThetaEisensteinGrid_coordinate_derivs .y s hs x y hv
  have ht := cubicThetaEisensteinGrid_coordinate_derivs .height s hs x y hv
  dsimp only [cubicThetaCoordinateLine,cubicThetaCoordinateCenter] at hx hy ht
  let F := fun cd : Eisenstein × Eisenstein => fun a b t =>
    cubicThetaEisensteinGridTerm cd (cubicThetaCartesianPoint a b t) s
  have hsA : Summable (fun cd => (v:ℂ)^2*
      (deriv (deriv (fun t => F cd t y v)) x+
       deriv (deriv (fun t => F cd x t v)) y+
       deriv (deriv (fun t => F cd x y t)) v)) :=
    ((hx.2.2.2.add hy.2.2.2).add ht.2.2.2).mul_left _
  have hsB : Summable (fun cd => (v:ℂ)*deriv (fun t => F cd x y t) v) :=
    ht.2.2.1.mul_left _
  have he : (fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s)=
      (fun a b t => ∑' cd, F cd a b t) := by
    funext a b t
    exact cubicThetaEisenstein_eq_grid _ _
  rw [he,cubicThetaEisenstein_eq_grid]
  unfold cubicThetaHyperbolicOperator
  change (v:ℂ)^2*(deriv (deriv (fun t => ∑' cd, F cd t y v)) x+
      deriv (deriv (fun t => ∑' cd, F cd x t v)) y+
      deriv (deriv (fun t => ∑' cd, F cd x y t)) v)-
        (v:ℂ)*deriv (fun t => ∑' cd, F cd x y t) v=
      s*(s-2)*(∑' cd, F cd x y v)
  rw [hx.2.1,hy.2.1,ht.2.1,ht.1]
  calc
    _ = ∑' cd, cubicThetaHyperbolicOperator (F cd) x y v := by
      unfold cubicThetaHyperbolicOperator
      rw [hsA.tsum_sub hsB,tsum_mul_left,tsum_mul_left,
        (hx.2.2.2.add hy.2.2.2).tsum_add ht.2.2.2,hx.2.2.2.tsum_add hy.2.2.2]
    _ = ∑' cd, s*(s-2)*F cd x y v := by
      apply tsum_congr
      intro cd
      exact cubicThetaEisensteinGrid_eigenvalue cd.1 cd.2 s x y hv
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowHeightEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual primitive row height, with arbitrary complex power,
satisfies the hyperbolic spectral equation. This removes the nonzero
cubic phase from the already proved literal grid equation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaGridTerm_row_height (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm (r.c,r.d) p s=
      star r.phase*(r.height p:ℂ)^s := by
  have hr : cubicThetaAdmissiblePair (r.c,r.d) := ⟨r.c_three,r.d_primary,r.coprime⟩
  simp only [cubicThetaEisensteinGridTerm,hr,ite_true, if_true,CubicThetaBottomRow.phase,
    star_star,CubicThetaBottomRow.height]

theorem cubicThetaRowHeightPower_eigenvalue (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => (r.height (cubicThetaCartesianPoint a b t):ℂ)^s) x y v=
      s*(s-2)*(r.height (cubicThetaCartesianPoint x y v):ℂ)^s := by
  have h := cubicThetaEisensteinGrid_eigenvalue r.c r.d s x y hv
  simp_rw [cubicThetaGridTerm_row_height r] at h
  rw [cubicThetaHyperbolicOperator_const_mul] at h
  have hn : star r.phase≠0 := by
    intro hz
    have hnorm : ‖star r.phase‖=1 := by rw [norm_star,r.phase_norm]
    rw [hz,norm_zero] at hnorm
    exact zero_ne_one hnorm
  apply mul_left_cancel₀ hn
  calc
    _ = s*(s-2)*(star r.phase*(r.height (cubicThetaCartesianPoint x y v):ℂ)^s) := h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRowHeightChain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two chain coefficients for the literal arithmetic row height
follow from its power-one and power-two spectral equations. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaRowHeightCoordinates (r : CubicThetaBottomRow) (x y v : ℝ) : ℝ :=
  r.height (cubicThetaCartesianPoint x y v)

lemma cubicThetaRowHeightCoordinates_contDiff (r : CubicThetaBottomRow)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaRowHeightCoordinates r t y v) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRowHeightCoordinates r x t v) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRowHeightCoordinates r x y t) v := by
  have hr := r.height_contDiffAt (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  constructor
  · exact (hr.comp x hx.contDiffAt).of_le (by norm_num)
  constructor
  · exact (hr.comp y hy.contDiffAt).of_le (by norm_num)
  · exact (hr.comp v (by unfold cubicThetaCartesianPoint; fun_prop)).of_le (by norm_num)

theorem cubicThetaRowHeight_chain_coefficients (r : CubicThetaBottomRow)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHeightChainQuadratic (cubicThetaRowHeightCoordinates r) x y v=
      (cubicThetaRowHeightCoordinates r x y v:ℂ)^2 ∧
    cubicThetaHeightChainLinear (cubicThetaRowHeightCoordinates r) x y v=
      -(cubicThetaRowHeightCoordinates r x y v:ℂ) := by
  obtain ⟨hx,hy,ht⟩ := cubicThetaRowHeightCoordinates_contDiff r x y hv
  have hp : 0 < cubicThetaRowHeightCoordinates r x y v := r.height_pos hv
  have h₁ := cubicThetaHyperbolic_chain hx hy ht
    ((cubicThetaHeightPower_analytic 1 hp).contDiffAt (n:=2))
  have e₁ := cubicThetaRowHeightPower_eigenvalue r 1 x y hv
  change cubicThetaHyperbolicOperator
    (fun a b t => (cubicThetaRowHeightCoordinates r a b t:ℂ)^(1:ℂ)) x y v=_ at e₁
  rw [e₁,cubicThetaHeightPower_second_deriv 1 hp,cubicThetaHeightPower_deriv 1 hp] at h₁
  norm_num at h₁
  have hL : cubicThetaHeightChainLinear (cubicThetaRowHeightCoordinates r) x y v=
      -(cubicThetaRowHeightCoordinates r x y v:ℂ) := h₁.symm
  have h₂ := cubicThetaHyperbolic_chain hx hy ht
    ((cubicThetaHeightPower_analytic 2 hp).contDiffAt (n:=2))
  have e₂ := cubicThetaRowHeightPower_eigenvalue r 2 x y hv
  change cubicThetaHyperbolicOperator
    (fun a b t => (cubicThetaRowHeightCoordinates r a b t:ℂ)^(2:ℂ)) x y v=_ at e₂
  rw [e₂,cubicThetaHeightPower_second_deriv 2 hp,cubicThetaHeightPower_deriv 2 hp,hL] at h₂
  norm_num at h₂
  refine ⟨?_,hL⟩
  linear_combination -(1/2:ℂ)*h₂

theorem cubicThetaRowHeight_operator (r : CubicThetaBottomRow) {f : ℝ → ℂ}
    (x y : ℝ) {v : ℝ} (hv : 0<v)
    (hf : ContDiffAt ℝ 2 f (cubicThetaRowHeightCoordinates r x y v)) :
    cubicThetaHyperbolicOperator (fun a b t => f (cubicThetaRowHeightCoordinates r a b t)) x y v=
      cubicThetaHyperbolicOperator (fun _ _ t => f t) 0 0 (cubicThetaRowHeightCoordinates r x y v) := by
  obtain ⟨hx,hy,ht⟩ := cubicThetaRowHeightCoordinates_contDiff r x y hv
  obtain ⟨hQ,hL⟩ := cubicThetaRowHeight_chain_coefficients r x y hv
  rw [cubicThetaHyperbolic_chain hx hy ht hf,hQ,hL]
  simp only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingRowEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming term for each actual arithmetic row satisfies the
spectral equation, with the transported compact annular forcing. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

theorem cubicThetaIncomingTerm_equation (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingTerm r (cubicThetaCartesianPoint x y v) s+
        star r.phase*cubicThetaIncomingForcing s
          (r.height (cubicThetaCartesianPoint x y v)) := by
  have hp : 0 < cubicThetaRowHeightCoordinates r x y v := r.height_pos hv
  have hf : ContDiffAt ℝ 2 (fun t : ℝ => cubicThetaCuspCutoff t*(t:ℂ)^s)
      (cubicThetaRowHeightCoordinates r x y v) :=
    (cubicThetaCuspCutoff_smooth.contDiffAt.mul
      (cubicThetaHeightPower_analytic s hp).contDiffAt).of_le (by norm_num)
  have he : (fun a b t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s)=
      (fun a b t => star r.phase*(cubicThetaCuspCutoff
        (cubicThetaRowHeightCoordinates r a b t)*
          (cubicThetaRowHeightCoordinates r a b t:ℂ)^s)) := by
    funext a b t
    unfold cubicThetaIncomingTerm cubicThetaEisensteinTerm cubicThetaRowHeightCoordinates
    ring
  rw [he,cubicThetaHyperbolicOperator_const_mul,
    cubicThetaRowHeight_operator r x y hv hf,cubicThetaCutoffIncoming_equation s 0 0 hp]
  unfold cubicThetaIncomingTerm cubicThetaEisensteinTerm cubicThetaRowHeightCoordinates
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full incoming arithmetic series satisfies the exact forced
spectral equation. Every differentiation uses a locally finite row set. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma incoming_coordinate_smooth (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint t y v) s) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint x t v) s) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint x y t) s) v := by
  have hr := cubicThetaIncomingTerm_contDiffAt r s (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  have ht : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(hr.comp x hx.contDiffAt).of_le (by norm_num),
    (hr.comp y hy.contDiffAt).of_le (by norm_num),
    (hr.comp v ht.contDiffAt).of_le (by norm_num)⟩

lemma cubicThetaIncomingFinite_equation (S : Finset CubicThetaBottomRow)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => ∑ r∈S, cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*(∑ r∈S, cubicThetaIncomingTerm r (cubicThetaCartesianPoint x y v) s)+
        ∑ r∈S, cubicThetaForcingTerm r (cubicThetaCartesianPoint x y v) s := by
  have hcoords := fun r => incoming_coordinate_smooth r s x y hv
  rw [cubicThetaHyperbolicOperator_finite S
    (fun r a b t => cubicThetaIncomingTerm r (cubicThetaCartesianPoint a b t) s) x y v
    (fun r _ => (hcoords r).1) (fun r _ => (hcoords r).2.1) (fun r _ => (hcoords r).2.2)]
  simp_rw [cubicThetaIncomingTerm_equation _ s x y hv]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  rfl

theorem cubicThetaIncomingEisenstein_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingEisenstein (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingEisenstein (cubicThetaCartesianPoint x y v) s+
        cubicThetaForcingSeries (cubicThetaCartesianPoint x y v) s := by
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood
    (p:=cubicThetaCartesianPoint x y v) hv
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_compact_sum hK hKpos
  have he : (fun p => cubicThetaIncomingEisenstein p s)=ᶠ[𝓝 (cubicThetaCartesianPoint x y v)]
      (fun p => ∑ r∈S, cubicThetaIncomingTerm r p s) := by
    filter_upwards [hKn] with p hp
    exact (hS p hp s).1
  have hpK : cubicThetaCartesianPoint x y v∈K := mem_of_mem_nhds hKn
  have hg := cubicThetaHyperbolicOperator_germ
    (F:=fun p => cubicThetaIncomingEisenstein p s)
    (G:=fun p => ∑ r∈S, cubicThetaIncomingTerm r p s) x y v he
  have hf := cubicThetaIncomingFinite_equation S s x y hv
  have heq := congrArg₂ (fun u w : ℂ => s*(s-2)*u+w)
    (hS _ hpK s).1.symm (hS _ hpK s).2.symm
  exact hg.trans (hf.trans heq)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic remainder satisfies the same forced spectral
operator as the continued global weak response. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingEisenstein_coordinate_contDiffAt
    (k : CubicThetaAxis) (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingEisenstein (cubicThetaCoordinateLine k x y v t) s)
      (cubicThetaCoordinateCenter k x y v) := by
  have hp : 0<(cubicThetaCartesianPoint x y v).2 := hv
  have hi := (cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hline : ContDiffAt ℝ ∞ (cubicThetaCoordinateLine k x y v) (cubicThetaCoordinateCenter k x y v) := by
    cases k <;> unfold cubicThetaCoordinateLine cubicThetaCoordinateCenter cubicThetaCartesianPoint
    · exact ((Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const).contDiffAt
    · exact ((contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const).contDiffAt
    · exact (contDiff_const.prodMk contDiff_id).contDiffAt
  have hi' : ContDiffAt ℝ ∞ (fun p => cubicThetaIncomingEisenstein p s)
      (cubicThetaCoordinateLine k x y v (cubicThetaCoordinateCenter k x y v)) := by
    rw [cubicThetaCoordinateLine_center]
    exact hi
  have hj := hi'.comp (cubicThetaCoordinateCenter k x y v) hline
  simpa only [Function.comp_def,cubicThetaCoordinateLine_center] using hj.of_le (by norm_num : (2:ℕ∞ω)≤∞)

theorem cubicThetaArithmeticRemainder_equation {s : ℂ} (hs : 2 < s.re)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaArithmeticRemainder (cubicThetaCartesianPoint a b t) s) x y v-
      s*(s-2)*cubicThetaArithmeticRemainder (cubicThetaCartesianPoint x y v) s=
        -cubicThetaForcingSeries (cubicThetaCartesianPoint x y v) s := by
  have hE k := cubicThetaEisenstein_coordinate_contDiffAt k s hs x y hv
  have hI k := cubicThetaIncomingEisenstein_coordinate_contDiffAt k s x y hv
  have he : ∀ k, ContDiffAt ℝ 2
      (cubicThetaAxisFunction (fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s) k x y v)
      (cubicThetaCoordinateCenter k x y v) := by
    intro k
    cases k with
    | x => exact hE .x
    | y => exact hE .y
    | height => exact hE .height
  have hi : ∀ k, ContDiffAt ℝ 2
      (cubicThetaAxisFunction (fun a b t => cubicThetaIncomingEisenstein (cubicThetaCartesianPoint a b t) s) k x y v)
      (cubicThetaCoordinateCenter k x y v) := by
    intro k
    cases k with
    | x => exact hI .x
    | y => exact hI .y
    | height => exact hI .height
  unfold cubicThetaArithmeticRemainder
  rw [cubicThetaHyperbolicOperator_sub
    (F:=fun a b t => cubicThetaEisenstein (cubicThetaCartesianPoint a b t) s)
    (G:=fun a b t => cubicThetaIncomingEisenstein (cubicThetaCartesianPoint a b t) s) x y v he hi,
    cubicThetaEisenstein_eigenvalue s hs x y hv,cubicThetaIncomingEisenstein_equation s x y hv]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAxisDifferentials
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate derivatives are actual directional derivatives on
complex-horizontal and real-height space. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaAxisFirst_line (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    (x y v t : ℝ) :
    cubicThetaAxisFirst k f (cubicThetaCoordinateLine k x y v t)=
      deriv (fun w => f (cubicThetaCoordinateLine k x y v w)) t := by
  cases k <;> simp [cubicThetaAxisFirst,cubicThetaCoordinateLine,
    cubicThetaCoordinateCenter,cubicThetaCartesianPoint]

lemma cubicThetaAxisSecond_eq_fderiv (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    {p : ℂ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    cubicThetaAxisSecond k f p=
      fderiv ℝ (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) p (cubicThetaAxisVector k) := by
  have hfirst : cubicThetaAxisFirst k f=ᶠ[𝓝 p]
      (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact cubicThetaAxisFirst_eq_fderiv k f (hq.differentiableAt (by norm_num))
  have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) p :=
    (((hf.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num))
  have hl : ContinuousAt (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) :=
    (cubicThetaCoordinateLine_continuous k _ _ _).continuousAt
  have hc := cubicThetaCoordinateLine_center k p.1.re p.1.im p.2
  rw [cubicThetaCartesianPoint_self] at hc
  have hlt : Tendsto (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
      (𝓝 (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) (𝓝 p) := by
    simpa only [ContinuousAt,hc] using hl
  have he := hfirst.comp_tendsto hlt
  have haxis := cubicThetaAxisFirst_eq_fderiv k
    (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) hd
  unfold cubicThetaAxisFirst at haxis
  rw [← haxis]
  unfold cubicThetaAxisSecond
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [he] with t ht
  change cubicThetaAxisFirst k f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)=
    fderiv ℝ f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) (cubicThetaAxisVector k) at ht
  rw [← ht,cubicThetaAxisFirst_line]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSecondContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the pure second derivatives of the actual series.
Only the diagonal coordinate derivatives used by the Laplacian occur. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaAxisSecond_continuousOn (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ)
    {U : Set (ℂ × ℝ)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (cubicThetaAxisSecond k f) U := by
  intro p hp
  have hfp := hf.contDiffAt (hU.mem_nhds hp)
  have hd : ContDiffAt ℝ 1 (fun q => fderiv ℝ f q (cubicThetaAxisVector k)) p :=
    (hfp.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const
  have hdd : ContDiffAt ℝ 0 (fun q => fderiv ℝ
      (fun y => fderiv ℝ f y (cubicThetaAxisVector k)) q (cubicThetaAxisVector k)) p :=
    (hd.fderiv_right (m:=0) (by norm_num)).clm_apply contDiffAt_const
  have he : cubicThetaAxisSecond k f=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (fun y => fderiv ℝ f y (cubicThetaAxisVector k)) q (cubicThetaAxisVector k)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact cubicThetaAxisSecond_eq_fderiv k f (hf.contDiffAt (hU.mem_nhds hq))
  exact (hdd.continuousAt.congr_of_eventuallyEq he).continuousWithinAt

lemma cubicThetaEisenstein_axisSecond_sum (k : CubicThetaAxis) {s : ℂ} (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisSecond k (fun q => cubicThetaEisenstein q s) p=
      ∑' cd, cubicThetaAxisSecond k (fun q => cubicThetaEisensteinGridTerm cd q s) p := by
  have h := (cubicThetaEisensteinGrid_coordinate_derivs k s hs p.1.re p.1.im hp).2.1
  have he : (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) s)=
      (fun t => ∑' cd, cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) s) :=
    funext (fun t => cubicThetaEisenstein_eq_grid _ _)
  unfold cubicThetaAxisSecond
  rw [he]
  exact h

lemma cubicThetaEisensteinGrid_local_second_bound (k : CubicThetaAxis) (s : ℂ) (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : Eisenstein × Eisenstein → ℝ, Summable u ∧
      ∀ cd q, q∈Metric.ball p r → 0<q.2 ∧
        ‖cubicThetaAxisSecond k (fun y => cubicThetaEisensteinGridTerm cd y s) q‖≤u cd := by
  let a := p.2/2
  let H := p.2*cubicThetaHeightConstant p+1
  have ha : 0<a := half_pos hp
  have hc : ContinuousAt (fun q : ℂ × ℝ => q.2*cubicThetaHeightConstant q) p := by
    unfold cubicThetaHeightConstant
    have hn : p.2^2≠0 := pow_ne_zero _ hp.ne'
    fun_prop
  have hU : {q : ℂ × ℝ | a<q.2 ∧ q.2*cubicThetaHeightConstant q<H}∈𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt (by dsimp [a]; linarith)).and
      (hc.eventually_lt_const (by dsimp [H]; linarith))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  let u := fun cd => (H^s.re*(cubicThetaSecondJetConstant s/a^2))*cubicThetaGridDecay s cd
  refine ⟨r,hr,u,(cubicThetaGridDecay_summable hs).mul_left _,?_⟩
  intro cd q hq
  obtain ⟨haq,hH⟩ := hsub hq
  have hq0 := ha.trans haq
  refine ⟨hq0,?_⟩
  have hj := (cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s q.1.re q.1.im hq0 k).2
  have haxis : cubicThetaAxisFunction
      (fun a b t => cubicThetaEisensteinGridTerm cd (cubicThetaCartesianPoint a b t) s)
      k q.1.re q.1.im q.2=(fun t => cubicThetaEisensteinGridTerm cd
        (cubicThetaCoordinateLine k q.1.re q.1.im q.2 t) s) := by
    cases k <;> rfl
  rw [haxis] at hj
  change ‖cubicThetaAxisSecond k (fun y => cubicThetaEisensteinGridTerm cd y s) q‖≤
    ‖cubicThetaEisensteinGridTerm cd (cubicThetaCartesianPoint q.1.re q.1.im q.2) s‖*
      (cubicThetaSecondJetConstant s/q.2^2) at hj
  rw [cubicThetaCartesianPoint_self] at hj
  have hf := cubicThetaEisensteinGridTerm_uniform_bound cd hq0 hs hH.le
  have hrat : cubicThetaSecondJetConstant s/q.2^2 ≤ cubicThetaSecondJetConstant s/a^2 :=
    div_le_div_of_nonneg_left (cubicThetaJetConstants_nonneg s).2 (sq_pos_of_pos ha)
      (pow_le_pow_left₀ ha.le haq.le 2)
  calc
    _ ≤ ‖cubicThetaEisensteinGridTerm cd q s‖*(cubicThetaSecondJetConstant s/q.2^2) := hj
    _ ≤ (H^s.re*cubicThetaGridDecay s cd)*(cubicThetaSecondJetConstant s/a^2) :=
      mul_le_mul hf hrat (div_nonneg (cubicThetaJetConstants_nonneg s).2 (sq_nonneg _))
        ((_root_.norm_nonneg _).trans hf)
    _ = u cd := by dsimp [u]; ring

lemma cubicThetaEisenstein_axisSecond_continuous (k : CubicThetaAxis) {s : ℂ} (hs : 2 < s.re) :
    ContinuousOn (cubicThetaAxisSecond k (fun q => cubicThetaEisenstein q s))
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨r,hr,u,hu,hb⟩ := cubicThetaEisensteinGrid_local_second_bound k s hs hp
  have hc : ContinuousOn (fun q => ∑' cd, cubicThetaAxisSecond k
      (fun y => cubicThetaEisensteinGridTerm cd y s) q) (Metric.ball p r) := by
    apply continuousOn_tsum _ hu (fun cd q hq => (hb cd q hq).2)
    intro cd
    apply (cubicThetaAxisSecond_continuousOn k (fun y => cubicThetaEisensteinGridTerm cd y s)
      (isOpen_lt continuous_const continuous_snd) (fun q hq =>
        ((cubicThetaEisensteinGridTerm_contDiffAt cd s hq).of_le
          (show (2:ℕ∞ω)≤∞ by norm_num)).contDiffWithinAt)).mono
    intro q hq
    exact (hb cd q hq).1
  have he : cubicThetaAxisSecond k (fun q => cubicThetaEisenstein q s)=ᶠ[𝓝 p]
      (fun q => ∑' cd, cubicThetaAxisSecond k (fun y => cubicThetaEisensteinGridTerm cd y s) q) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact cubicThetaEisenstein_axisSecond_sum k hs hq
  exact ((hc.continuousAt (Metric.ball_mem_nhds p hr)).congr_of_eventuallyEq he).continuousWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticAxisRegularity
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic remainder has continuous pure second
coordinate derivatives and the corresponding actual line derivatives. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaArithmetic_axis_contDiffAt (k : CubicThetaAxis) {s : ℂ} (hs : 2 < s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ 2 (fun t => cubicThetaArithmeticRemainder
      (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t) s)
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) :=
  (cubicThetaEisenstein_coordinate_contDiffAt k s hs p.1.re p.1.im hp).sub
    (cubicThetaIncomingEisenstein_coordinate_contDiffAt k s p.1.re p.1.im hp)

lemma cubicThetaArithmetic_axisSecond_continuous (k : CubicThetaAxis) {s : ℂ} (hs : 2 < s.re) :
    ContinuousOn (cubicThetaAxisSecond k (fun p => cubicThetaArithmeticRemainder p s))
      {p : ℂ × ℝ | 0<p.2} := by
  have hE := cubicThetaEisenstein_axisSecond_continuous k hs
  have hI := cubicThetaAxisSecond_continuousOn k (fun p => cubicThetaIncomingEisenstein p s)
    (isOpen_lt continuous_const continuous_snd)
    ((cubicThetaIncomingEisenstein_contDiffOn s).of_le (by norm_num : (2:ℕ∞ω)≤∞))
  apply (hE.sub hI).congr
  intro p hp
  exact cubicThetaAxisSecond_sub k (fun q => cubicThetaEisenstein q s)
    (fun q => cubicThetaIncomingEisenstein q s) p
    (cubicThetaEisenstein_coordinate_contDiffAt k s hs p.1.re p.1.im hp)
    (cubicThetaIncomingEisenstein_coordinate_contDiffAt k s p.1.re p.1.im hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBoundedScaledMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire upper Mellin tails at a positive scale, for the two bounded coefficient families in the actual projected transformation. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

def cubicThetaBoundedScaledAxis (a : Eisenstein→ℂ) (ℓ : ℤ) (z : ℂ) (r t : ℝ) : ℂ :=
  cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,r*t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPoincareTerm_regular {n : ℕ∞} (ψ : C_c(CubicThetaPoint,ℂ))
    (hψ : ContDiffOn ℝ n (fun y => ψ (cubicThetaPointInclusion.symm y))
      {y : ℂ × ℝ | 0<y.2}) (g : cubicThetaPrincipalGroup)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    ContDiffAt ℝ n (fun x => cubicThetaPoincareTerm ψ g (cubicThetaPointInclusion.symm x)) y := by
  have hopen : IsOpen {x : ℂ × ℝ | 0<x.2} := isOpen_lt continuous_const continuous_snd
  have hs := hψ.contDiffAt (hopen.mem_nhds (cubicThetaMobius_height_pos
    (cubicThetaPrincipalComplex g) hy))
  have hcomp := hs.comp y ((cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g) hy).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hconst : ContDiffAt ℝ n (fun _ : ℂ × ℝ => star (cubicThetaKubotaValue g)) y := contDiffAt_const
  apply (hconst.mul hcomp).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hy] with x hx
  simp only [cubicThetaPoincareTerm,Function.comp_def,cubicThetaPointInclusion_action g hx]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspDisjointness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPointHeight_upper (a : SL(2,Eisenstein)) (ha : a 1 0=0) (p : CubicThetaPoint) :
    cubicThetaPointHeight (a • p)=cubicThetaPointHeight p := by
  have hdet : a 0 0*a 1 1=1 := by
    simpa only [Matrix.det_fin_two,ha,mul_zero,sub_zero] using a.property
  have hu : IsUnit (a 1 1) := isUnit_iff_exists_inv'.mpr ⟨a 0 0,hdet⟩
  have hc : cubicThetaFullComplex a 1 0=0 := congrArg (fun z : Eisenstein => (z:ℂ)) ha
  have hd : Complex.normSq (cubicThetaFullComplex a 1 1)=1 := norm_of_isUnit hu
  change p.val.2/cubicThetaMobiusDenominator (cubicThetaFullComplex a) p.val=p.val.2
  simp only [cubicThetaMobiusDenominator,hc,zero_mul,zero_add,hd,
    Complex.normSq_zero,add_zero,div_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaFrequencyBound (s : ℂ) : ℝ :=
  9*(∑' c : Eisenstein, (norm c)^(-(s.re-1)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRemainderBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute lattice summation gives a uniform bound for the literal
Eisenstein-minus-incoming remainder in every integral cusp. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCuspRemainderConstant (s : ℂ) (R : ℝ) : ℝ :=
  2*(3+2*R)^2*(∑' c : Eisenstein, (norm c)^(-(s.re-2)))*
    (∑' d : Eisenstein, (1+norm d)^(-2:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspLatticeWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The summable lattice weight controlling both values and first
spatial derivatives of the arithmetic remainder in each cusp. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaCuspLatticeMass (s : ℂ) : ℝ :=
  (∑' c : Eisenstein, norm c^(-(s.re-2)))*(∑' d : Eisenstein, (1+norm d)^(-2:ℝ))

def pairWeight (s : ℂ) (cd : Eisenstein × Eisenstein) : ℝ :=
  norm cd.1^(-(s.re-2))*(1+norm cd.2)^(-2:ℝ)

lemma pairWeight_summable {s : ℂ} (hs : 3 < s.re) : Summable (pairWeight s) := by
  have hc := summable_eisenstein_norm_rpow (show 1 < s.re-2 by linarith)
  have hd := summable_eisenstein_one_add_norm (by norm_num : (1:ℝ)<2)
  exact summable_mul_of_summable_norm hc.norm hd.norm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspCutoff
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unphased, scaled incoming cutoff is an actual invariant
scalar. Its arithmetic sum is locally finite at all scales at least one. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaScalarCuspTerm (N : ℝ) (r : CubicThetaBottomRow) (p : ℂ × ℝ) : ℂ :=
  cubicThetaCuspCutoff (r.height p/N)

def cubicThetaScalarCusp (N : ℝ) (p : ℂ × ℝ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaScalarCuspTerm N r p

lemma cubicThetaScalarCuspTerm_zero (N : ℝ) (hN : 0<N) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : r.height p≤N) : cubicThetaScalarCuspTerm N r p=0 :=
  cubicThetaCuspCutoff_zero ((div_le_one hN).mpr hp)

lemma cubicThetaScalarCuspTerm_high {N : ℝ} (hN : 1≤N) {r : CubicThetaBottomRow}
    {p : ℂ × ℝ} (h : cubicThetaScalarCuspTerm N r p≠0) : 1 < r.height p := by
  have hp : N < r.height p := by
    by_contra hn
    exact h (cubicThetaScalarCuspTerm_zero N (by linarith) r (le_of_not_gt hn))
  exact lt_of_le_of_lt hN hp

lemma cubicThetaScalarCusp_compact_sum {N : ℝ} (hN : 1≤N)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K,
      cubicThetaScalarCusp N p=∑ r∈S, cubicThetaScalarCuspTerm N r p := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hp
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact cubicThetaScalarCuspTerm_zero N (by linarith) r ((hS p hp r hr).le.trans hN)

lemma cubicThetaScalarCusp_smooth {N : ℝ} (hN : 1≤N) :
    ContDiffOn ℝ ∞ (cubicThetaScalarCusp N) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaScalarCusp_compact_sum hN hK hpos
  have he : cubicThetaScalarCusp N=ᶠ[𝓝 p] (fun q => ∑ r∈S, cubicThetaScalarCuspTerm N r q) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaScalarCuspTerm N r q) p :=
    ContDiffAt.sum (fun r _ => cubicThetaCuspCutoff_smooth.contDiffAt.comp p
      ((r.height_contDiffAt hp).div_const N))
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

lemma cubicThetaScalarCusp_invariant (N : ℝ) (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaPrincipalComplex g) p)=
      cubicThetaScalarCusp N p := by
  unfold cubicThetaScalarCusp cubicThetaScalarCuspTerm
  simp_rw [← CubicThetaBottomRow.height_rightMul _ g hp]
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaCuspCutoff (r.height p/N))

lemma cubicThetaScalarCusp_high {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ}
    (hp : 2*N≤p.2) : cubicThetaScalarCusp N p=1 := by
  have hp1 : 1<p.2 := by linarith
  have he : cubicThetaScalarCusp N p=cubicThetaScalarCuspTerm N cubicThetaZeroRow p := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hc := r.high_height_c_zero hp1 (cubicThetaScalarCuspTerm_high hN hn)
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp hc)
  rw [he]
  apply cubicThetaCuspCutoff_one
  have hz : cubicThetaZeroRow.height p=p.2 := by simp [CubicThetaBottomRow.height,cubicThetaZeroRow,norm]
  rw [hz]
  exact (le_div_iff₀ (by linarith : 0<N)).mpr hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaScalarCusp_norm {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖cubicThetaScalarCusp N p‖≤1 := by
  by_cases h : ∃ r, cubicThetaScalarCuspTerm N r p≠0
  · obtain ⟨r,hr⟩ := h
    have he : cubicThetaScalarCusp N p=cubicThetaScalarCuspTerm N r p := by
      apply tsum_eq_single
      intro t ht
      by_contra htn
      exact ht (cubicThetaIncomingRows_unique hp (cubicThetaScalarCuspTerm_high hN htn)
        (cubicThetaScalarCuspTerm_high hN hr))
    rw [he]
    exact cubicThetaCuspCutoff_norm _
  · have hz : ∀ r, cubicThetaScalarCuspTerm N r p=0 := by simpa only [not_exists,not_not] using h
    simp only [cubicThetaScalarCusp,hz,tsum_zero,norm_zero,zero_le_one]

def cubicThetaScalarCuspAt (δ : SL(2,Eisenstein)) (N : ℝ) (p : CubicThetaPoint) : ℂ :=
  cubicThetaScalarCusp N (δ⁻¹ • p).val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarCuspEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scaled cusp cutoffs have uniformly bounded hyperbolic gradient.
The bound uses the unique high primitive row and exact Mobius transport. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaScalarCusp_upper {N : ℝ} (hN : 1≤N) {p : ℂ × ℝ}
    (hp : 1<p.2) : cubicThetaScalarCusp N p=cubicThetaCuspCutoff (p.2/N) := by
  have he : cubicThetaScalarCusp N p=cubicThetaScalarCuspTerm N cubicThetaZeroRow p := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp
      (r.high_height_c_zero hp (cubicThetaScalarCuspTerm_high hN hn)))
  rw [he]
  simp only [cubicThetaScalarCuspTerm,CubicThetaBottomRow.height,cubicThetaZeroRow,norm]
  norm_num

lemma cubicThetaScalarCusp_local_zero {N : ℝ} (hN : 1<N) {p : ℂ × ℝ}
    (hp : 0<p.2) (hr : ∀ r : CubicThetaBottomRow, r.height p≤1) :
    cubicThetaScalarCusp N =ᶠ[𝓝 p] (fun _ => 0) := by
  classical
  obtain ⟨K,hKn,hK,hpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaScalarCusp_compact_sum hN.le hK hpos
  have hrows : ∀ᶠ q in 𝓝 p, ∀ r∈S, r.height q<N := by
    apply (eventually_all_finset S).mpr
    intro r _
    exact (r.height_contDiffAt hp).continuousAt.eventually (gt_mem_nhds ((hr r).trans_lt hN))
  filter_upwards [hKn,hrows] with q hq hrows
  rw [hS q hq]
  exact Finset.sum_eq_zero (fun r h => cubicThetaScalarCuspTerm_zero N
    (by linarith) r (hrows r h).le)

lemma cubicThetaScalarCusp_energy_invariant {N : ℝ} (hN : 1≤N)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) :
    p.2^2*cubicThetaFunctionEnergy (cubicThetaScalarCusp N) p=
      (cubicThetaMobius (cubicThetaPrincipalComplex g) p).2^2*
        cubicThetaFunctionEnergy (cubicThetaScalarCusp N)
          (cubicThetaMobius (cubicThetaPrincipalComplex g) p) := by
  have he : (fun q => cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaPrincipalComplex g) q))
      =ᶠ[𝓝 p] cubicThetaScalarCusp N := by
    filter_upwards [isOpen_lt continuous_const continuous_snd |>.mem_nhds hp] with q hq
    exact cubicThetaScalarCusp_invariant N g hq
  have hd := he.fderiv_eq (𝕜:=ℝ)
  have hf := (cubicThetaScalarCusp_smooth hN).contDiffAt
    (isOpen_lt continuous_const continuous_snd |>.mem_nhds
      (cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g) hp))
  have ht := cubicThetaFunctionEnergy_mobius (cubicThetaScalarCusp N)
    (cubicThetaPrincipalComplex g) hp (hf.differentiableAt (by simp))
  simpa only [cubicThetaFunctionEnergy,hd] using ht

lemma cubicThetaScalarCusp_energy_bound :
    ∃ B≥0, ∀ N : ℝ, 2≤N → ∀ p : ℂ × ℝ, 0<p.2 →
      p.2^2*cubicThetaFunctionEnergy (cubicThetaScalarCusp N) p≤B := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaCuspCutoff_deriv_bound
  refine ⟨B,hB,?_⟩
  intro N hN p hp
  have hN1 : 1≤N := by linarith
  have hupper (q : ℂ × ℝ) (hq : 1<q.2) :
      q.2^2*cubicThetaFunctionEnergy (cubicThetaScalarCusp N) q≤B := by
    have he : cubicThetaScalarCusp N =ᶠ[𝓝 q] (fun y => cubicThetaCuspCutoff (y.2/N)) := by
      filter_upwards [isOpen_lt continuous_const continuous_snd |>.mem_nhds hq] with y hy
      exact cubicThetaScalarCusp_upper hN1 hy
    have hd := he.fderiv_eq (𝕜:=ℝ)
    have hc : DifferentiableAt ℝ cubicThetaCuspCutoff (q.2/N) :=
      cubicThetaCuspCutoff_smooth.differentiable (by simp) _
    have hi : DifferentiableAt ℝ (fun t : ℝ => t/N) q.2 := differentiableAt_id.div_const N
    have hf : DifferentiableAt ℝ (fun t => cubicThetaCuspCutoff (t/N)) q.2 :=
      DifferentiableAt.comp (f:=fun t : ℝ => t/N) (g:=cubicThetaCuspCutoff) q.2 hc hi
    change q.2^2*cubicThetaTangentEnergy
      ((fderiv ℝ (cubicThetaScalarCusp N) q).comp _)≤B
    rw [hd]
    change q.2^2*cubicThetaFunctionEnergy (fun y => cubicThetaCuspCutoff (y.2/N)) q≤B
    rw [cubicThetaFunctionEnergy_vertical hf,cubicThetaCuspCutoff_scaled_energy]
    exact (hbound (q.2/N)).trans (by
      by_cases h : q.2/N∈Icc (1:ℝ) 2
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h]; exact hB)
  by_cases h : ∃ r : CubicThetaBottomRow, 1 < r.height p
  · obtain ⟨r,hr⟩ := h
    rw [cubicThetaScalarCusp_energy_invariant hN1 r.completion hp]
    apply hupper
    change 1<(cubicThetaBottomRow r.completion).height p
    rwa [r.completion_row]
  · have hr : ∀ r : CubicThetaBottomRow, r.height p≤1 := by
      simpa only [not_exists,not_lt] using h
    have he := (cubicThetaScalarCusp_local_zero (by linarith : 1<N) hp hr).fderiv_eq (𝕜:=ℝ)
    simp only [cubicThetaFunctionEnergy,he,fderiv_const_apply,ContinuousLinearMap.zero_comp,
      cubicThetaTangentEnergy,zero_apply,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero]
    exact hB

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveLocalization
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Products supported inside positive height extend continuously and
smoothly across the unused boundary, regardless of the other factor there. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaAxisFirst_continuous (k : CubicThetaAxis) {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (cubicThetaAxisFirst k φ) := by
  have he : cubicThetaAxisFirst k φ=(fun p => fderiv ℝ φ p (cubicThetaAxisVector k)) :=
    funext (fun p => cubicThetaAxisFirst_eq_fderiv k φ (hφ.differentiable one_ne_zero p))
  rw [he]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma cubicThetaAxisFirst_support (k : CubicThetaAxis) (φ : ℂ × ℝ → ℂ) :
    tsupport (cubicThetaAxisFirst k φ)⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hout
  apply hp
  have ht : φ=ᶠ[𝓝 p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hout
  have hl : Tendsto (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
      (𝓝 (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) (𝓝 p) := by
    have h : ContinuousAt (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
        (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) :=
      (cubicThetaCoordinateLine_continuous k p.1.re p.1.im p.2).continuousAt
    simpa only [ContinuousAt,cubicThetaCoordinateLine_center,cubicThetaCartesianPoint_self] using h
  have he := ht.comp_tendsto hl
  simp only [Function.comp_def] at he
  unfold cubicThetaAxisFirst
  simpa only [deriv_const] using he.deriv_eq

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGreenAlgebra
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact algebraic divergence identity for the hyperbolic density
v^-3 and the three real coordinate directions. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaCoordinateLaplacian (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (p.2:ℂ)^2*(cubicThetaAxisSecond .x f p+cubicThetaAxisSecond .y f p+
    cubicThetaAxisSecond .height f p)-(p.2:ℂ)*cubicThetaAxisFirst .height f p

def cubicThetaCoordinatePairing (φ f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  star (cubicThetaAxisFirst .x φ p)*cubicThetaAxisFirst .x f p+
    star (cubicThetaAxisFirst .y φ p)*cubicThetaAxisFirst .y f p+
    star (cubicThetaAxisFirst .height φ p)*cubicThetaAxisFirst .height f p

def cubicThetaCoordinateDivergence (k : CubicThetaAxis) (φ f : ℂ × ℝ → ℂ)
    (p : ℂ × ℝ) : ℂ :=
  cubicThetaWeightedTest φ p*cubicThetaAxisSecond k f p+
    cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p*cubicThetaAxisFirst k f p

lemma cubicThetaCoordinateLaplacian_hyperbolic (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) :
    cubicThetaCoordinateLaplacian f p=cubicThetaHyperbolicOperator
      (fun a b t => f (cubicThetaCartesianPoint a b t)) p.1.re p.1.im p.2 := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaCuspFourierWeight (h : Eisenstein) (W : C_c(ℝ,ℂ)) (p : CubicThetaPoint) : ℂ :=
  W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ)

lemma cubicThetaCuspFourierWeight_continuous (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    Continuous (cubicThetaCuspFourierWeight h W) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h))) :=
    Real.continuous_fourierChar.comp (by unfold tracePair; fun_prop)
  exact (W.continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
    (continuous_subtype_val.comp hc)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspFourierNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaFourierRadialTest (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) : ℂ :=
  ∫ v in Ioi (2:ℝ), star (W v)*(v:ℂ)^s*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supplementary character on primary elements modulo nine is
an additive character of their two integral coordinates. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedCharacter : AddChar Eisenstein ℂ where
  toFun t := cubicSymbol (1+3*t) lambdaE
  map_zero_eq_one' := by simp only [mul_zero,add_zero,cubicSymbol_one_lower]
  map_add_eq_mul' a b := by
    have ha : primary (1+3*a) := ⟨a,by ring⟩
    have hb : primary (1+3*b) := ⟨b,by ring⟩
    have hab : primary (1+3*(a+b)) := ⟨a+b,by ring⟩
    have he := cubicSymbol_lambda_periodic (primary_mul ha hb) hab
      (show (9:Eisenstein) ∣ (1+3*a)*(1+3*b)-(1+3*(a+b)) from ⟨a*b,by ring⟩)
    rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hb)] at he
    exact he.symm

lemma cubicThetaRamifiedCharacter_one : cubicThetaRamifiedCharacter 1=1 := by
  change cubicSymbol (1+3*(1:Eisenstein)) lambdaE=1
  rw [show (1+3*(1:Eisenstein))=(-2)*(-2) by ring,
    cubicSymbol_mul_lower (by norm_num) (by norm_num),cubicSymbol_neg_two_lambda]
  norm_num

lemma cubicThetaRamifiedCharacter_omega : cubicThetaRamifiedCharacter omegaE=omega^2 :=
  cubicSymbol_seven_factor_lambda

theorem cubicThetaRamifiedCharacter_coordinates (a b : ℤ) :
    cubicThetaRamifiedCharacter ((a:Eisenstein)+b*omegaE)=omega^(2*b) := by
  rw [AddChar.map_add_eq_mul]
  have ha : cubicThetaRamifiedCharacter (a:Eisenstein)=1 := by
    rw [show (a:Eisenstein)=a • (1:Eisenstein) by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaRamifiedCharacter_one,one_zpow]
  have hb : cubicThetaRamifiedCharacter ((b:Eisenstein)*omegaE)=(omega^2)^b := by
    rw [show (b:Eisenstein)*omegaE=b • omegaE by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaRamifiedCharacter_omega]
  rw [ha,hb,one_mul]
  rw [← zpow_natCast omega 2,← zpow_mul]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCharacterFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact additive frequency of the ramified supplementary character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedCharacter_trace (a b : ℤ) :
    tracePair (ofCoords a b:ℂ) ((2:ℂ)/(3*traceLambda))=(2*(b:ℝ))/3 := by
  have hd : dualRealCoords ![0,(2/3:ℝ)]=(2:ℂ)/(3*traceLambda) := by
    rw [dualRealCoords_eq]
    norm_num
    ring
  have hc : (ofCoords a b:ℂ)=eisensteinRealCoords ![(a:ℝ),(b:ℝ)] := by
    simp [eisensteinRealCoords_apply,ofCoords_coe]
  rw [hc,← hd,dualRealCoords_trace]
  simp [Fin.sum_univ_two]
  ring

theorem cubicThetaRamifiedCharacter_fourier (t : Eisenstein) :
    cubicThetaRamifiedCharacter t=
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (2*t)) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective t
  change cubicThetaRamifiedCharacter (ofCoords a b)=
    residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (2*ofCoords a b))
  rw [show ofCoords a b=(a:Eisenstein)+b*omegaE from rfl,
    cubicThetaRamifiedCharacter_coordinates]
  rw [residueFourierChar_mk]
  have ht : tracePair (((2:Eisenstein)*((a:Eisenstein)+b*omegaE):Eisenstein):ℂ)
      (1/((3:Eisenstein):ℂ)/traceLambda)=(2*(b:ℝ))/3 := by
    have hc := cubicThetaRamifiedCharacter_trace a b
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    unfold tracePair
    congr 2
    rw [ofCoords_coe]
    push_cast
    change (2:ℂ)*((a:ℂ)+(b:ℂ)*omega)*(1/3/traceLambda)=
      ((a:ℂ)+(b:ℂ)*omega)*(2/(3*traceLambda))
    ring
  have hs : (1:ℂ)/(((3:Eisenstein):ℂ)*traceLambda)=
      1/((3:Eisenstein):ℂ)/traceLambda := by ring
  rw [hs,ht]
  have hw : (Real.fourierChar (1/3:ℝ):ℂ)=omega := by
    rw [Real.fourierChar_apply]
    unfold omega
    congr 1
    push_cast
    ring
  have hw2 : (Real.fourierChar (2/3:ℝ):ℂ)=omega^2 := by
    rw [show (2/3:ℝ)=1/3+1/3 by ring,AddChar.map_add_eq_mul,Circle.coe_mul,hw]
    ring
  rw [show 2*(b:ℝ)/3=b • (2/3:ℝ) by simp; ring,
    AddChar.map_zsmul_eq_zpow,Circle.coe_zpow,hw2,
    ← zpow_natCast omega 2,← zpow_mul]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryNineFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality on the primary coset in the exact codifferent pairing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourier_nine_triple (h t : Eisenstein) :
    residueFourierChar 9 (by norm_num)
      (Ideal.Quotient.mk (modulus 9) (3*h*t))=
    residueFourierChar 3 (by norm_num)
      (Ideal.Quotient.mk (modulus 3) (h*t)) := by
  rw [residueFourierChar_mk,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  change (3:ℂ)*(h:ℂ)*(t:ℂ)*(1/(9*traceLambda))=
    ((h:ℂ)*(t:ℂ))*(1/(3*traceLambda))
  field_simp [traceLambda_ne_zero]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second finite character needed at the ramified place: the unit
omega, restricted to primary numerators. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaUnitCharacter : AddChar Eisenstein ℂ where
  toFun t := cubicSymbol (1+3*t) omegaE
  map_zero_eq_one' := by simp only [mul_zero,add_zero,cubicSymbol_one_lower]
  map_add_eq_mul' a b := by
    have ha : primary (1+3*a) := ⟨a,by ring⟩
    have hb : primary (1+3*b) := ⟨b,by ring⟩
    have hab : primary (1+3*(a+b)) := ⟨a+b,by ring⟩
    have he := cubicSymbol_omega_periodic (primary_mul ha hb) hab
      (show (9:Eisenstein) ∣ (1+3*a)*(1+3*b)-(1+3*(a+b)) from ⟨a*b,by ring⟩)
    rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hb)] at he
    exact he.symm

lemma cubicThetaUnitCharacter_one : cubicThetaUnitCharacter 1=omega^2 := by
  change cubicSymbol (1+3*(1:Eisenstein)) omegaE=omega^2
  rw [show (1+3*(1:Eisenstein))=(-2)*(-2) by ring,
    cubicSymbol_mul_lower (by norm_num) (by norm_num),cubicSymbol_neg_two_omega]
  ring

lemma cubicThetaUnitCharacter_omega : cubicThetaUnitCharacter omegaE=omega^2 :=
  cubicSymbol_seven_factor_omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitCharacterFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite additive frequency of the unit supplementary character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAddChar_eq_of_generators (φ ψ : AddChar Eisenstein ℂ)
    (h1 : φ 1=ψ 1) (hω : φ omegaE=ψ omegaE) : φ=ψ := by
  ext t
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective t
  change φ ((a:Eisenstein)+b*omegaE)=ψ ((a:Eisenstein)+b*omegaE)
  rw [AddChar.map_add_eq_mul,AddChar.map_add_eq_mul]
  have ha : (a:Eisenstein)=a • (1:Eisenstein) := by simp
  have hb : (b:Eisenstein)*omegaE=b • omegaE := by simp
  rw [ha,hb,AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,
    AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,h1,hω]

def cubicThetaUnitFourierCharacter : AddChar Eisenstein ℂ :=
  ((residueFourierChar 3 (by norm_num)).mulShift
    (Ideal.Quotient.mk (modulus 3) lambdaE)).compAddMonoidHom
      (Ideal.Quotient.mk (modulus 3)).toAddMonoidHom

lemma cubicThetaUnitFourierCharacter_apply (t : Eisenstein) :
    cubicThetaUnitFourierCharacter t=
      (Real.fourierChar (tracePair (t:ℂ) (1/3)):ℂ) := by
  change residueFourierChar 3 (by norm_num)
    (Ideal.Quotient.mk (modulus 3) lambdaE*Ideal.Quotient.mk (modulus 3) t)=_
  rw [← map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  change (traceLambda*(t:ℂ))*(1/(3*traceLambda))=(t:ℂ)*(1/3)
  field_simp [traceLambda_ne_zero]

theorem cubicThetaUnitCharacter_fourier (t : Eisenstein) :
    cubicThetaUnitCharacter t=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (lambdaE*t)) := by
  have hw : (Real.fourierChar (1/3:ℝ):ℂ)=omega := by
    rw [Real.fourierChar_apply]
    unfold omega
    congr 1
    push_cast
    ring
  have he : cubicThetaUnitCharacter=cubicThetaUnitFourierCharacter := by
    apply cubicThetaAddChar_eq_of_generators
    · rw [cubicThetaUnitCharacter_one,cubicThetaUnitFourierCharacter_apply]
      have ht : tracePair ((1:Eisenstein):ℂ) (1/3)=(1/3:ℝ)+(1/3:ℝ) := by
        norm_num [tracePair]
      rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul,hw]
      ring
    · rw [cubicThetaUnitCharacter_omega,cubicThetaUnitFourierCharacter_apply]
      have ht : tracePair (omegaE:ℂ) (1/3)=-(1/3:ℝ) := by
        change 2*(omega*(1/3:ℂ)).re=-(1/3:ℝ)
        norm_num [Complex.mul_re,omega_re]
      rw [ht,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,hw]
      exact star_omega.symm
  rw [he]
  change residueFourierChar 3 (by norm_num)
    (Ideal.Quotient.mk (modulus 3) lambdaE*Ideal.Quotient.mk (modulus 3) t)=_
  rw [← map_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedUnitGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite ramified sum with its unit character retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaUnitCharacter_power {a : Eisenstein} (ha : primary a) (r : ℕ) :
    (cubicSymbol a omegaE)^r=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) (lambdaE*(r:Eisenstein)*(a-1))) := by
  obtain ⟨t,ht⟩ := ha
  have he : a=1+3*t := by linear_combination ht
  have hc : cubicSymbol a omegaE=cubicThetaUnitCharacter t := by rw [he]; rfl
  rw [hc,cubicThetaUnitCharacter_fourier]
  have hp : (residueFourierChar 3 (by norm_num)
      (Ideal.Quotient.mk (modulus 3) (lambdaE*t)))^r=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (lambdaE*(r:Eisenstein)*t)) := by
    rw [show lambdaE*(r:Eisenstein)*t=r • (lambdaE*t) by simp; ring,map_nsmul,
      AddChar.map_nsmul_eq_pow]
  rw [hp,show lambdaE*(r:Eisenstein)*(a-1)=3*((lambdaE*(r:Eisenstein))*t)
    by rw [ht]; ring]
  simpa only [mul_assoc] using (cubicThetaFourier_nine_triple (lambdaE*(r:Eisenstein)) t).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedAllRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit finite ramified factor for all six global units. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaUnit_signed_power (e : Eisensteinˣ) :
    ∃ r : Fin 3, (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)) := by
  obtain ⟨r,hr⟩ := eisenstein_unit_eq_signed_omega e.isUnit
  refine ⟨⟨r%3,Nat.mod_lt _ (by norm_num)⟩,?_⟩
  simpa only [cube_pow_mod omegaE_cube] using hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMiddleSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaOmegaUnit : Eisensteinˣ :=
  Units.mkOfMulEqOne omegaE (omegaE^2) (by simpa only [←pow_succ'] using omegaE_cube)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNinePhase
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The modulus-nine phase needed for the remaining ramified residue.
Integer multiples of three times a primary frequency lie in its kernel. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNinePhase (h : Eisenstein) : ℂ :=
  residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)

lemma cubicThetaNinePhase_add (h k : Eisenstein) :
    cubicThetaNinePhase (h+k)=cubicThetaNinePhase h*cubicThetaNinePhase k := by
  unfold cubicThetaNinePhase
  rw [map_add,AddChar.map_add_eq_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNinePhaseSymbol
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The modulus-nine phase in the actual ramified residue is the
supplementary cubic character in the arithmetic theta formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNinePhase_coordinates (a b : ℤ) :
    cubicThetaNinePhase (ofCoords a b)=(Real.fourierChar ((b:ℝ)/9):ℂ) := by
  have hd : dualRealCoords ![0,(1/9:ℝ)]=1/(9*traceLambda) := by
    rw [dualRealCoords_eq]
    norm_num
    ring
  have hc : (ofCoords a b:ℂ)=eisensteinRealCoords ![(a:ℝ),(b:ℝ)] := by
    simp [eisensteinRealCoords_apply,ofCoords_coe]
  rw [cubicThetaNinePhase,residueFourierChar_mk]
  congr 2
  change tracePair (ofCoords a b:ℂ) (1/(9*traceLambda))=_
  rw [hc,←hd,dualRealCoords_trace]
  simp [Fin.sum_univ_two]
  ring

lemma cubicThetaNinePhase_one : cubicThetaNinePhase 1=1 := by
  have h := cubicThetaNinePhase_coordinates 1 0
  have he : ofCoords 1 0=(1:Eisenstein) := by
    apply Subtype.ext
    simp [ofCoords_coe]
  simpa only [he,Int.cast_zero,zero_div,AddChar.map_zero_eq_one,Circle.coe_one] using h

lemma cubicThetaNinePhase_three (t : Eisenstein) :
    cubicThetaNinePhase (3*t)=
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) t) := by
  unfold cubicThetaNinePhase
  simpa only [mul_one] using cubicThetaFourier_nine_triple t 1

lemma cubicThetaNinePhase_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaNinePhase h=cubicSymbol h (lambdaE^2) := by
  obtain ⟨t,ht⟩ := hh
  have he : h=1+3*t := by linear_combination ht
  have hp : primary (1+3*t) := ⟨t,by ring⟩
  rw [he,cubicThetaNinePhase_add,cubicThetaNinePhase_one,one_mul,
    cubicThetaNinePhase_three,cubicSymbol_pow_upper hp]
  change residueFourierChar 3 _ (Ideal.Quotient.mk (modulus 3) t)=
    (cubicThetaRamifiedCharacter t)^2
  rw [cubicThetaRamifiedCharacter_fourier,pow_two,←AddChar.map_add_eq_mul,←map_add]
  apply congrArg (residueFourierChar 3 (by norm_num))
  apply residue_eq_of_dvd_sub
  exact ⟨-t,by ring⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTransversal
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite right cosets used by the cubed-prime Hecke trace. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeTransversal (p : Eisenstein) : Set cubicThetaPrincipalGroup :=
  Classical.choose ((cubicThetaPrimeIwahori (p^3)).exists_isComplement_right 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitPhaseSymbol
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact matching of the unit phase and supplementary symbol in the
ramified arithmetic theta coefficient. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNinePhase_congr {a b : Eisenstein} (hab : (9:Eisenstein)∣a-b) :
    cubicThetaNinePhase a=cubicThetaNinePhase b :=
  congrArg (residueFourierChar 9 (by norm_num)) (residue_eq_of_dvd_sub hab)

lemma cubicThetaNinePhase_omega :
    cubicThetaNinePhase omegaE=(Real.fourierChar (1/9):ℂ) := by
  have he : ofCoords 0 1=omegaE := by
    apply Subtype.ext
    simp [ofCoords_coe,omegaE]
  simpa only [he,Int.cast_one] using cubicThetaNinePhase_coordinates 0 1

lemma cubicThetaNinePhase_omega_square :
    cubicThetaNinePhase (omegaE^2)=(Real.fourierChar (-1/9):ℂ) := by
  have he : ofCoords (-1) (-1)=omegaE^2 := by
    have h : ofCoords (-1) (-1)= -1-omegaE := by
      apply Subtype.ext
      simp [ofCoords_coe,omegaE,sub_eq_add_neg]
    rw [h]
    linear_combination -omegaE_quadratic
  simpa only [he,Int.cast_neg,Int.cast_one] using cubicThetaNinePhase_coordinates (-1) (-1)

lemma cubicThetaUnit_square_congruence (j : Fin 3) :
    (3:Eisenstein)∣(omegaE^(j:ℕ))^2-1-lambdaE*(4*(j:ℕ)) := by
  fin_cases j
  · norm_num
  · refine ⟨-2-3*omegaE,?_⟩
    norm_num only [Fin.val_one,pow_one,Nat.cast_one,mul_one]
    dsimp only [lambdaE]
    linear_combination omegaE_quadratic
  · refine ⟨-3-5*omegaE,?_⟩
    norm_num only [Fin.val_two,Nat.cast_ofNat,←pow_mul,Nat.reduceMul]
    dsimp only [lambdaE]
    linear_combination (omegaE^2-omegaE)*omegaE_quadratic

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedModel
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic theta coefficients obey the same exact
ramified phase relation as the actual normalized residue. Zero support is retained. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSymbol_cube_lower {d : Eisenstein} (hd : primary d)
    {v : Eisenstein} (hv : IsCoprime d v) : cubicSymbol (d^3) v=1 := by
  rw [show d^3=d*d*d by ring,cubicSymbol_mul_lower
    (mul_ne_zero (primary_ne_zero hd) (primary_ne_zero hd)) (primary_ne_zero hd),
    cubicSymbol_mul_lower (primary_ne_zero hd) (primary_ne_zero hd)]
  convert cubicSymbol_cube_of_isCoprime hd v hv using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma cubicThetaSymbol_primary_cube_part {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (e : Eisensteinˣ) :
    cubicSymbol (c*d^3) ((e:Eisenstein)^4*lambdaE^2)=
      cubicSymbol c ((e:Eisenstein)^4*lambdaE^2) := by
  have hv : IsCoprime d ((e:Eisenstein)^4*lambdaE^2) :=
    (isCoprime_mul_unit_left_right (e.isUnit.pow 4) d (lambdaE^2)).mpr
      (primary_coprime_lambda hd).pow_right
  rw [cubicSymbol_mul_lower (primary_ne_zero hc) (pow_ne_zero 3 (primary_ne_zero hd)),
    cubicThetaSymbol_cube_lower hd hv,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaShiftedInversion (b : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![b,-1;1,0],by simp [Matrix.det_fin_two]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSieveSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary coefficient selector of DR v3 (5.17)--(5.18). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimarySupport (n : Eisenstein) : Prop :=
  ∃ R : CubicThetaCoordinates n, R.order = 1 ∧ (R.unit:Eisenstein) = 1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVerticalTermDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first vertical derivatives of the fixed-angular Fourier terms. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSeriesTermVertical (a : Eisenstein → ℂ) (z : ℂ) (v : ℝ) (n : Eisenstein) : ℂ :=
  if n=0 then 0 else a n*cubicThetaWhittakerDerivative (‖cubicThetaFrequency n‖*v)*
    (‖cubicThetaFrequency n‖:ℂ)*(Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inversion of the cubic completion kernel. The Euler variable
for a prime ideal is first weighted, then replaced by its cube. Thus the
series identities below retain the actual cube-divisor support; they are
not ordinary (uncubed) convolution identities. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubeCompletionSeries (x : EisensteinIdealPrime → ℂ) : ComplexIdealSeries :=
  MvPowerSeries.expand 3 (by norm_num)
    (MvPowerSeries.rescale x (MvPowerSeries.map Complex.ofRealHom idealZeta))

def cubeInverseCompletionSeries (x : EisensteinIdealPrime → ℂ) : ComplexIdealSeries :=
  MvPowerSeries.expand 3 (by norm_num)
    (MvPowerSeries.rescale x (MvPowerSeries.map Complex.ofRealHom idealMoebiusSeries))

/-- The precise inverse-completion weight, including the norm phase
created by replacing the length by `U / (Nc)^3`. -/
def metaplecticCompletionWeight (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    (c : Eisenstein) : ℂ :=
  if IsCoprime c r then
    (Real.sqrt (norm c):ℂ)*theta (3*ℓ) c*(norm c:ℂ)^((3*t:ℝ)*Complex.I)
  else 0

@[simp] lemma metaplecticCompletionWeight_one (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    metaplecticCompletionWeight r ℓ t 1 = 1 := by
  simp [metaplecticCompletionWeight,norm_one_eq,isCoprime_one_left]

end CubicFirstMoment

end

end OAI
end


