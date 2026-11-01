-- Prove2me | Definitions.Def_OAIQ091C015
-- name    : OAIQ091C015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:24:46.740421+00:00
-- url     : https://prove2.me/theorems/d8d02373-8369-41c1-a854-c777794105da
-- title:
--   Definitions bundle OAIQ091C015 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 293 declarations of OpenAI's Lean: 78 definitions, 7 instances and 208 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.ShiftedCurvaturePositive`, `OAI.PositiveEinsteinFour.Geometry.actualOrientationDoubleCover`, `OAI.PositiveEinsteinFour.Geometry.blockRadialGradient`, `OAI.PositiveEinsteinFour.Geometry.frameMinusCoefficient`, `OAI.PositiveEinsteinFour.Geometry.framePlusCoefficient`, `OAI.PositiveEinsteinFour.Geometry.frameRegularizedWeight`, `OAI.PositiveEinsteinFour.Geometry.frameWeylMatrix`, `OAI.PositiveEinsteinFour.Geometry.generalCoefficientMap`, `OAI.PositiveEinsteinFour.Geometry.hessianVectorMap`, `OAI.PositiveEinsteinFour.Geometry.highestProjectionMap`, `OAI.PositiveEinsteinFour.Geometry.invariantHessianForm`, `OAI.PositiveEinsteinFour.Geometry.invariantRicciGradient`, `OAI.PositiveEinsteinFour.Geometry.kappaNormIntegrand`, `OAI.PositiveEinsteinFour.Geometry.normRegularizationParameter`, `OAI.PositiveEinsteinFour.Geometry.normalizedDeterminantShape`, `OAI.PositiveEinsteinFour.Geometry.orientationCoverPositiveFrames`, `OAI.PositiveEinsteinFour.Geometry.orientationLinearMatrix`, `OAI.PositiveEinsteinFour.Geometry.orientedEulerDensity`, `OAI.PositiveEinsteinFour.Geometry.orientedNormRegularization`, `OAI.PositiveEinsteinFour.Geometry.projectedWeightKernel`, `OAI.PositiveEinsteinFour.Geometry.rawGradientVector`, `OAI.PositiveEinsteinFour.Geometry.regularizedBlockNorm`, `OAI.PositiveEinsteinFour.Geometry.regularizedDeficit`, `OAI.PositiveEinsteinFour.Geometry.regularizedDeficitDerivative`, `OAI.PositiveEinsteinFour.Geometry.regularizedHessianWeight`, `OAI.PositiveEinsteinFour.Geometry.regularizedKappa`, `OAI.PositiveEinsteinFour.Geometry.regularizedKappaDerivative`, `OAI.PositiveEinsteinFour.Geometry.regularizedMatrixWeight`, `OAI.PositiveEinsteinFour.Geometry.regularizedRadialDerivative`, `OAI.PositiveEinsteinFour.Geometry.regularizedRadialSecond`, `OAI.PositiveEinsteinFour.Geometry.regularizedWeylRoot`, `OAI.PositiveEinsteinFour.Geometry.regularizedWeylRootFirst`, `OAI.PositiveEinsteinFour.Geometry.regularizedWeylRootSecond`, `OAI.PositiveEinsteinFour.Geometry.regularizedWeylWeight`, `OAI.PositiveEinsteinFour.Geometry.regularizedWeylWeightDerivative`, `OAI.PositiveEinsteinFour.Geometry.scalarNormExpression`, `OAI.PositiveEinsteinFour.Geometry.scalarVarianceWeight`, `OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure`, `OAI.PositiveEinsteinFour.Geometry.tensorGradientVector`, `OAI.PositiveEinsteinFour.Geometry.traceCoefficient` and 38 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_AveragedRadial`, `EinsteinFour_ContinuousRadialComparison`, `EinsteinFour_CoupledCasimir`, `EinsteinFour_CoupledOperator`, `EinsteinFour_CurvatureForm`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_DirichletFactorization`, `EinsteinFour_DirichletMatrix`, `EinsteinFour_FiniteRadialComparison`, `EinsteinFour_FourHeatAwayBound`, `EinsteinFour_FourHeatGaussianMoments`, `EinsteinFour_FrameRotation`, `EinsteinFour_GeodesicGeometry12`, `EinsteinFour_GeodesicGeometry13`, `EinsteinFour_HessianAssembly`, `EinsteinFour_HighestActionCoordinates`, `EinsteinFour_HighestCoordinates`, `EinsteinFour_HighestGram`, `EinsteinFour_HighestMinusCoordinates`, `EinsteinFour_HighestProjection`, `EinsteinFour_HighestVectorSpace`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_HodgeTheory11`, `EinsteinFour_JacobiCompression`, `EinsteinFour_JacobiCompressionLimit`, `EinsteinFour_JacobiDirichletLimit`, `EinsteinFour_JacobiKernelPowers`, `EinsteinFour_JacobiODELimit`, `EinsteinFour_JacobiPivots`, `EinsteinFour_JacobiRadialDeficit`, `EinsteinFour_JacobiRadialODE`, `EinsteinFour_JacobiSchemeMatrix`, `EinsteinFour_JacobiSineReference`, `EinsteinFour_JacobiSymmetricKernel`, `EinsteinFour_JacobiVolume`, `EinsteinFour_MatrixSlotCompression`, `EinsteinFour_MatrixSlotCubic`, `EinsteinFour_MetricBianchi`, `EinsteinFour_MetricCurvatureGreen`, `EinsteinFour_MetricDistance`, `EinsteinFour_MetricMatrixGreen`, `EinsteinFour_MetricMinusGreen`, `EinsteinFour_ModeCompression`, `EinsteinFour_OrientationCoverClopenSheet`, `EinsteinFour_OrientationCoverClosed`, `EinsteinFour_OrientationCoverCompactness`, `EinsteinFour_OrientationCoverDeckMetric`, `EinsteinFour_OrientationCoverDistanceDown`, `EinsteinFour_OrientationCoverMetricDoubleCover`, `EinsteinFour_OrientationCoverPathLift`, `EinsteinFour_OrientationCoverTopology`, `EinsteinFour_OrthonormalFrame`, `EinsteinFour_QuaternionGenerators`, `EinsteinFour_QuaternionLifts`, `EinsteinFour_QuaternionReflections`, `EinsteinFour_ReferenceCompression`, `EinsteinFour_RiemannianVolume`, `EinsteinFour_ScalarH1EllipticGain`, `EinsteinFour_ScalarH2Closure`, `EinsteinFour_ScalarIterationRegularity`, `EinsteinFour_ScalarL2EllipticGain`, `EinsteinFour_ScalarOpenIntegerEllipticGain`, `EinsteinFour_ScalarRegularity06`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_TensorPairing`, `EinsteinFour_TraceDecomposition`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylGeometry`, `EinsteinFour_WeylMatrixEquation`, `EinsteinFour_WeylNormal`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C036`, `OAIQ091C007`, `OAIQ091C008`, `OAIQ091C009`, `OAIQ091C010`, `OAIQ091C011` and `OAIQ091C012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ091C018`; the statements `OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost`, `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy`, `OAI_PositiveEinsteinFour_HighestHessian_coordinate_casimir`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_left`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_right`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_comm`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_self`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_right`, `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le`, `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square`, `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_plusPolynomial`, `OAI.PositiveEinsteinFour.HighestHessian.innerAction_casimir_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_energy_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_0_3_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_highest`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_1_3_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest`, `OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_3_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_3_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_3` and `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_3_3`; the proofs of `OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost`, `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_left`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_right`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_comm`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_self`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_right`, `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le`, `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_plusPolynomial`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_1_3_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_1_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_2_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_entry_2_3_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest`, `OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_0_3_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_1_3_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_1_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_2`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_2_3`, `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_3` and `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_3_3`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C036
import Definitions.Def_OAIQ091C007
import Definitions.Def_OAIQ091C008
import Definitions.Def_OAIQ091C009
import Definitions.Def_OAIQ091C010
import Definitions.Def_OAIQ091C011
import Definitions.Def_OAIQ091C012

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletMatrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite block matrices for the Jacobi determinant approximation. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix OrderDual

noncomputable section

/-- The determinant of an `L D Lᵀ` factorization is the product of the
three-dimensional pivots, with their original order retained. -/
theorem det_bidiagonal_factorization {N : ℕ} (A S : Fin N → NormalMatrix) :
    (lowerBidiagonal A * Matrix.blockDiagonal S * (lowerBidiagonal A).transpose).det =
      ∏ i, (S i).det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_lowerBidiagonal, one_mul, mul_one, Matrix.det_blockDiagonal]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace calculations for normalizing the finite Jacobi matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem scalarLift_mul {N : ℕ} (G H : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (G * H) = scalarLift G * scalarLift H := by
  simpa only [scalarLift, Matrix.kronecker, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul (1 : NormalMatrix) 1 G H)

theorem trace_eq_sum_block_traces {N : ℕ}
    (A : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) :
    A.trace = ∑ i, (blockAt A i i).trace := by
  simp only [Matrix.trace, Matrix.diag, blockAt, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- A scalar operation on the time nodes pairs only with the trace of each
normal curvature block. Cross-time commutation is not used. -/
theorem trace_scalarLift_mul_diagonal {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → NormalMatrix) :
    (scalarLift G * Matrix.blockDiagonal A).trace = ∑ i, G i i * (A i).trace := by
  rw [trace_eq_sum_block_traces]
  simp_rw [blockAt_mul_diagonal, blockAt_scalarLift, smul_mul_assoc,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

/-- The normalized perturbation has trace zero whenever every Weyl block
has trace zero, for any scalar time-node normalizer. -/
theorem trace_normalized_defect_zero {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0) :
    (scalarLift G * Matrix.blockDiagonal A * scalarLift G).trace = 0 := by
  rw [Matrix.trace_mul_cycle, ← scalarLift_mul, trace_scalarLift_mul_diagonal]
  simp only [hA, mul_zero, Finset.sum_const_zero]

/-- The trace of the normalized Jacobi matrix is precisely its dimension.
This is the trace bound used on the complementary block in compression. -/
theorem normalized_jacobi_trace {N : ℕ} (G L : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → NormalMatrix) (a : ℝ)
    (hG : G * L * G = 1) (hA : ∀ i, (A i).trace = 0) :
    (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G).trace =
      3 * N := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, ← scalarLift_mul,
    ← scalarLift_mul, hG, scalarLift_one, Matrix.trace_one,
    mul_smul_comm, smul_mul_assoc, Matrix.trace_smul,
    trace_normalized_defect_zero G A hA]
  simp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModeCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression onto a common scalar time mode in the three normal directions. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The first-mode block of the normalized Jacobi matrix is exactly the
weighted curvature average. -/
theorem normalized_mode_compression {N : ℕ}
    (G L : Matrix (Fin N) (Fin N) ℝ) (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) (a g : ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hGsymm : Gᵀ = G) (hG : G * L * G = 1)
    (heigen : G *ᵥ w = g • w) :
    (modeEmbedding w)ᵀ *
        (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) *
        modeEmbedding w =
      (1 : NormalMatrix) - (a * g) ^ 2 • (∑ i, w i ^ 2 • A i) := by
  have hLift : (scalarLift G)ᵀ = scalarLift G := by
    ext ⟨a, i⟩ ⟨b, j⟩
    change (1 : NormalMatrix) b a * G j i = (1 : NormalMatrix) a b * G i j
    rw [show G j i = G i j from congrFun (congrFun hGsymm i) j]
    simp only [Matrix.one_apply, eq_comm]
  have hright := scalarLift_mode_eigenvector G w g heigen
  have hleft : (modeEmbedding w)ᵀ * scalarLift G = g • (modeEmbedding w)ᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, hLift] using
      congrArg Matrix.transpose hright
  have hbase : scalarLift G * scalarLift L * scalarLift G = 1 := by
    rw [← scalarLift_mul, ← scalarLift_mul, hG, scalarLift_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, hbase, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, modeEmbedding_orthonormal w hw]
  have hdefect : (modeEmbedding w)ᵀ *
        (scalarLift G * (a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) * modeEmbedding w =
      (a * g) ^ 2 • (∑ i, w i ^ 2 • A i) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft]
    rw [Matrix.mul_assoc ((g • (modeEmbedding w)ᵀ) * (a ^ 2 • Matrix.blockDiagonal A)),
      hright]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mode_compression_diagonal]
    congr 1
    ring
  rw [hdefect]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FiniteRadialComparison
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite determinant comparison before the mesh limit. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem det_scalarLift {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    (scalarLift G).det = G.det ^ 3 := by
  simpa only [scalarLift, Matrix.kronecker, Matrix.det_one, one_pow,
    Fintype.card_fin, one_mul] using Matrix.det_kronecker (1 : NormalMatrix) G

/-- Normalizing by a scalar comparison matrix divides the determinant by
the cube of its scalar determinant. -/
theorem det_normalized_matrix {N : ℕ}
    (G L : Matrix (Fin N) (Fin N) ℝ)
    (K : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (hG : G * L * G = 1) :
    (scalarLift G * K * scalarLift G).det = K.det / L.det ^ 3 := by
  have hd : G.det * L.det * G.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hG
  have hL : L.det ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, zero_mul] at hd
    exact zero_ne_one hd
  have hg : G.det ^ 2 = 1 / L.det := by
    apply (eq_div_iff hL).mpr
    nlinarith [hd]
  rw [Matrix.det_mul, Matrix.det_mul, det_scalarLift]
  calc
    G.det ^ 3 * K.det * G.det ^ 3 = (G.det ^ 2) ^ 3 * K.det := by ring
    _ = K.det / L.det ^ 3 := by rw [hg]; ring

/-- The first scalar mode bounds the determinant of the normalized
Jacobi matrix. Positivity and the scalar eigenmode are explicit here;
the orthogonal completion and complementary trace estimate are proved. -/
theorem finite_normalized_radial_comparison {N : ℕ} (hN : 0 < N)
    (G L : Matrix (Fin N) (Fin N) ℝ) (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) (a g : ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hGsymm : Gᵀ = G) (hG : G * L * G = 1)
    (heigen : G *ᵥ w = g • w) (hA : ∀ i, (A i).trace = 0)
    (hpos : (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) *
      scalarLift G).PosDef) :
    (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G).det ≤
      ((1 : NormalMatrix) - (a * g) ^ 2 • (∑ i, w i ^ 2 • A i)).det := by
  have hcomp := normalized_mode_compression G L A w a g hw hGsymm hG heigen
  have htrcomp : ((modeEmbedding w)ᴴ *
      (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) *
      modeEmbedding w).trace = 3 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hcomp, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_sum]
    simp [Matrix.trace_smul, hA]
  have hcard : Fintype.card (Fin 3 × Fin N) =
      Fintype.card (Fin 3) + Fintype.card (Fin (3 * N - 3)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hb := det_le_isometric_compression_of_card hcard (modeEmbedding w) hpos
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      modeEmbedding_orthonormal w hw)
    (by simpa using (normalized_jacobi_trace G L A a hG hA).le)
    (by simpa using htrcomp)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hcomp] using hb

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ReferenceCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the finite comparison to the actual scalar Dirichlet reference. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The scalar normalizer and its sine eigenmode are fully instantiated.
Only positivity of the actual curvature Dirichlet matrix remains here. -/
theorem reference_determinant_comparison {N : ℕ} (hN : 0 < N) (t : ℝ)
    (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0)
    (hfirst : 0 < firstEigenvalue t N) (hK : (curvatureDirichlet t A).PosDef) :
    (curvatureDirichlet t A).det / (referenceMatrix t N).det ^ 3 ≤
      ((1 : NormalMatrix) - ((t / (N + 1)) ^ 2 / firstEigenvalue t N) •
        (∑ i, unitFirstSineVector N i ^ 2 • A i)).det := by
  let L := referenceMatrix t N
  let G := scalarNormalizer L
  let w := unitFirstSineVector N
  let a := t / (N + 1)
  let g := 1 / Real.sqrt (firstEigenvalue t N)
  have hL : L.PosDef := scalarDirichlet_posDef N _ hfirst
  have hn : G * L * G = 1 := scalarNormalizer_normalizes hL
  have hsym : Gᵀ = G := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef L).isHermitian.eq
  have hlift : (scalarLift G)ᴴ = scalarLift G := by
    ext ⟨u, i⟩ ⟨v, j⟩
    change (1 : NormalMatrix) v u * G j i = (1 : NormalMatrix) u v * G i j
    rw [show G j i = G i j from congrFun (congrFun hsym i) j]
    simp only [Matrix.one_apply, eq_comm]
  have hunit : IsUnit (scalarLift G) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_scalarLift]
    exact (Matrix.isUnit_det_of_left_inverse hn).pow 3
  have hpos : (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) *
      scalarLift G).PosDef := by
    have hp := hK.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
    simpa only [hlift, curvatureDirichlet, L, a] using hp
  have heigen : G *ᵥ w = g • w :=
    scalarNormalizer_eigenvector hL hfirst (unitFirstSineVector_eigenvector N _)
  have hb := finite_normalized_radial_comparison hN G L A w a g
    (unitFirstSineVector_norm hN) hsym hn heigen hA hpos
  rw [det_normalized_matrix G L _ hn] at hb
  have hcoef : (a * g) ^ 2 = a ^ 2 / firstEigenvalue t N := by
    dsimp [g]
    simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt hfirst.le]
    ring
  rw [hcoef] at hb
  exact hb

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ContinuousRadialComparison
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the actual first-mode Dirichlet comparison to the radial limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

/-- The finite comparison passes to the actual sine-weighted curvature
integral. The two determinant convergence premises are supplied by the
Jacobi approximation, while positivity is supplied by preconjugacy. -/
theorem continuous_radial_comparison {t D : ℝ} (ht : 0 < t) (htπ : t < Real.pi)
    (A : ℝ → NormalMatrix) (htrace : ∀ s, (A s).trace = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • A s))
    (hLip : ∀ s r, ‖Averages.sineWeight s • A s - Averages.sineWeight r • A r‖ ≤
      L * |s - r|)
    (hpos : ∀ᶠ N in atTop, (curvatureDirichlet t (sampledCurvature A N)).PosDef)
    (hdet : Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (sampledCurvature A N)).det) atTop (nhds D))
    (href : Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 * (referenceMatrix t N).det ^ 3)
      atTop (nhds (Real.sin t ^ 3))) :
    D ≤ Real.sin t ^ 3 * ((1 : NormalMatrix) -
      (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s)).det := by
  have hs : 0 < Real.sin t ^ 3 := pow_pos (Real.sin_pos_of_pos_of_lt_pi ht htπ) 3
  have hmode := modeAverage_tendsto hL hc hLip
  have hcompression : Tendsto (fun N : ℕ => (1 : NormalMatrix) -
      ((t / (N + 1)) ^ 2 / firstEigenvalue t N) • modeAverage A N) atTop
      (nhds ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s))) :=
    tendsto_const_nhds.sub ((first_mode_coefficient_tendsto ht.le htπ).smul hmode)
  apply compression_comparison_limit hs hdet href hcompression
  filter_upwards [hpos, firstEigenvalue_eventually_pos ht.le htπ,
    eventually_gt_atTop (0 : ℕ)] with N hN heig hNpos
  have hcomp := reference_determinant_comparison hNpos t (sampledCurvature A N)
    (fun i => htrace _) heig hN
  have hstep : (t / (N + 1 : ℝ)) ^ 3 ≠ 0 := by positivity
  have hratio : ((t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (sampledCurvature A N)).det) /
      ((t / (N + 1)) ^ 3 * (referenceMatrix t N).det ^ 3) =
      (curvatureDirichlet t (sampledCurvature A N)).det / (referenceMatrix t N).det ^ 3 := by
    exact mul_div_mul_left _ _ hstep
  rw [hratio]
  exact hcomp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiCompressionLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.relativeDiscretePosition_zero _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the actual first-mode compression survives the mesh limit. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Filter
open scoped Matrix.Norms.Frobenius

noncomputable section

theorem reference_compression_posSemidef {N : ℕ} (hN : 0 < N) (t : ℝ)
    (A : Fin N → NormalMatrix) (hfirst : 0 < firstEigenvalue t N)
    (hK : (curvatureDirichlet t A).PosDef) :
    ((1 : NormalMatrix) - ((t / (N + 1)) ^ 2 / firstEigenvalue t N) •
      (∑ i, unitFirstSineVector N i ^ 2 • A i)).PosSemidef := by
  let L := referenceMatrix t N
  let G := scalarNormalizer L
  let w := unitFirstSineVector N
  let a := t / (N + 1)
  let g := 1 / Real.sqrt (firstEigenvalue t N)
  have hL : L.PosDef := scalarDirichlet_posDef N _ hfirst
  have hn : G * L * G = 1 := scalarNormalizer_normalizes hL
  have hsym : Gᵀ = G := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (scalarNormalizer_posSemidef L).isHermitian.eq
  have hlift : (scalarLift G)ᴴ = scalarLift G := by
    ext ⟨u, i⟩ ⟨v, j⟩
    change (1 : NormalMatrix) v u * G j i = (1 : NormalMatrix) u v * G i j
    rw [show G j i = G i j from congrFun (congrFun hsym i) j]
    simp only [Matrix.one_apply, eq_comm]
  have hp := hK.posSemidef.conjTranspose_mul_mul_same (scalarLift G)
  rw [hlift] at hp
  have hc := hp.conjTranspose_mul_mul_same (modeEmbedding w)
  have heigen : G *ᵥ w = g • w :=
    scalarNormalizer_eigenvector hL hfirst (unitFirstSineVector_eigenvector N _)
  have hcomp := normalized_mode_compression G L A w a g
    (unitFirstSineVector_norm hN) hsym hn heigen
  change ((modeEmbedding w)ᴴ *
    (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) *
    modeEmbedding w).PosSemidef at hc
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hcomp] at hc
  have hcoef : (a * g) ^ 2 = a ^ 2 / firstEigenvalue t N := by
    dsimp [g]
    simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt hfirst.le]
    ring
  rwa [hcoef] at hc

theorem continuous_radial_compression_posSemidef {t : ℝ}
    (ht : 0 ≤ t) (htπ : t < Real.pi) (A : ℝ → NormalMatrix)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • A s))
    (hLip : ∀ s r, ‖Averages.sineWeight s • A s - Averages.sineWeight r • A r‖ ≤
      L * |s - r|)
    (hpos : ∀ᶠ N in atTop, (curvatureDirichlet t (sampledCurvature A N)).PosDef) :
    ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
      (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s)).PosSemidef := by
  have hmode := modeAverage_tendsto hL hc hLip
  have hconv : Tendsto (fun N : ℕ => (1 : NormalMatrix) -
      ((t / (N + 1)) ^ 2 / firstEigenvalue t N) • modeAverage A N) atTop
      (nhds ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s))) := tendsto_const_nhds.sub
    ((first_mode_coefficient_tendsto ht htπ).smul hmode)
  apply Matrix.posSemidef_is_closed.mem_of_tendsto hconv
  filter_upwards [hpos, firstEigenvalue_eventually_pos ht htπ,
    eventually_gt_atTop (0 : ℕ)] with N hN heig hNpos
  exact reference_compression_posSemidef hNpos t (sampledCurvature A N) heig hN

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_DirichletFactorization
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tridiagonal Jacobi matrix and its ordered Schur pivots. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem det_dirichlet_pivots {N : ℕ} (S : Fin N → NormalMatrix)
    (hunit : ∀ k, IsUnit (S k).det) (hsym : ∀ k, (S k).transpose = S k) :
    (dirichletMatrix (pivotDiagonal S)).det = ∏ i, (S i).det := by
  rw [dirichlet_pivot_factorization S hunit hsym, det_bidiagonal_factorization]

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiPivots
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Dirichlet determinant is the determinant of the discrete
Jacobi solution, on the nonsingular range used before conjugacy. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem jacobiPivot_symmetric (D : ℕ → NormalMatrix)
    (hD : ∀ i, (D i).transpose = D i) (i : ℕ) :
    (jacobiPivot D i).transpose = jacobiPivot D i := by
  induction i with
  | zero => exact hD 0
  | succ i hi => simp only [jacobiPivot, Matrix.transpose_sub,
      Matrix.transpose_nonsing_inv, hD, hi]

/-- The determinant identity required for the preconjugate comparison.
The hypotheses on `Y` are its recurrence and nonsingularity. -/
theorem dirichlet_determinant_eq_jacobi (D Y : ℕ → NormalMatrix) (N : ℕ)
    (hD : ∀ i, (D i).transpose = D i)
    (h0 : Y 0 = 0) (h1 : Y 1 = 1)
    (hrec : ∀ i, Y (i + 2) = D i * Y (i + 1) - Y i)
    (hunit : ∀ i, 1 ≤ i → i ≤ N + 1 → IsUnit (Y i).det) :
    (dirichletMatrix (fun i : Fin N => D i.val)).det = (Y (N + 1)).det := by
  let S : Fin N → NormalMatrix := fun i => jacobiPivot D i.val
  have hratio (i : Fin N) : S i = Y (i.val + 2) * (Y (i.val + 1))⁻¹ :=
    jacobiPivot_eq_ratio D Y h0 h1 hrec i.val (fun k hk hki => hunit k hk (by omega))
  have hSunit (i : Fin N) : IsUnit (S i).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hratio, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero (hunit (i.val + 2) (by omega) (by omega)).ne_zero
      (inv_ne_zero (hunit (i.val + 1) (by omega) (by omega)).ne_zero)
  have hSsym (i : Fin N) : (S i).transpose = S i := jacobiPivot_symmetric D hD i.val
  have hdiag : (fun i : Fin N => D i.val) = pivotDiagonal S := by
    funext i
    exact (pivotDiagonal_jacobiPivot D i).symm
  rw [hdiag, det_dirichlet_pivots S hSunit hSsym]
  have hp := determinant_pivot_product (fun i => Y (i + 1)) N
    (fun i hi => (hunit (i + 1) (by omega) (by omega)).ne_zero)
  rw [← Fin.prod_univ_eq_prod_range] at hp
  calc
    (∏ i : Fin N, (S i).det) =
        ∏ i : Fin N, (Y (i.val + 2) * (Y (i.val + 1))⁻¹).det := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hratio]
    _ = (Y (N + 1)).det := by
      simpa only [Nat.add_assoc, h1, Matrix.det_one, div_one] using hp

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSchemeMatrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying the concrete Jacobi recurrence with the finite curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- All diagonal blocks of the discrete Jacobi recurrence are the actual
curvature blocks. This identity includes the time-index shift. -/
theorem curvatureDirichlet_determinant {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix)
    (hsym : ∀ i, (R i).transpose = R i)
    (hunit : ∀ i, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete R (t / (N + 1)) i).det) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).det =
      (normalizedDiscrete R (t / (N + 1)) (N + 1)).det := by
  have hh : t / (N + 1 : ℝ) ≠ 0 := div_ne_zero ht (by positivity)
  rw [curvatureDirichlet_eq]
  simp only [add_sub_cancel]
  apply dirichlet_determinant_eq_jacobi
    (fun i => (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • R (i + 1))
    (normalizedDiscrete R (t / (N + 1))) N
  · intro i
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsym]
  · exact normalizedDiscrete_zero _ _
  · exact normalizedDiscrete_one _ hh
  · exact normalizedDiscrete_recurrence R _
  · exact hunit

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiDirichletLimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Dirichlet determinant converges to the actual Jacobi determinant. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem curvatureDirichlet_det_tendsto_of_position_tendsto {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → ℕ → NormalMatrix) (hR : ∀ N i, (R N i)ᵀ = R N i)
    (J : NormalMatrix)
    (hunit : ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete (R N) (t / (N + 1)) i).det)
    (hX : Tendsto (fun N : ℕ => discretePosition (R N) (t / (N + 1)) (N + 1))
      atTop (nhds J)) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 *
      (curvatureDirichlet t (fun i : Fin N => R N (i.val + 1) - 1)).det)
      atTop (nhds J.det) := by
  have hc : Continuous (fun A : NormalMatrix => A.det) := continuous_id.matrix_det
  apply ((hc.tendsto J).comp hX).congr'
  filter_upwards [hunit] with N hu
  dsimp only [Function.comp_apply]
  rw [curvatureDirichlet_determinant ht (R N) (hR N) hu]
  have hh : t / (N + 1 : ℝ) ≠ 0 := div_ne_zero ht (by positivity)
  have hid : (t / (N + 1)) • normalizedDiscrete (R N) (t / (N + 1)) (N + 1) =
      discretePosition (R N) (t / (N + 1)) (N + 1) := by
    simp only [normalizedDiscrete, smul_smul, mul_inv_cancel₀ hh, one_smul]
  rw [← hid, Matrix.det_smul, Fintype.card_fin]


end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiODELimit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Determinant convergence from the same preconjugate Jacobi ODE data. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RegularJacobi

variable {t : ℝ} (d : RegularJacobi t)

theorem endpoint_position_tendsto (ht : 0 < t) :
    Tendsto (fun N : ℕ =>
      discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1))
      atTop (nhds (d.J t)) := by
  have hnorm : Tendsto (fun N : ℕ =>
      ‖relativeDiscretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1) -
        normalizedJacobi d.J t‖) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ d.positionError_tendsto
    filter_upwards [d.uniform_errors ht] with N hN
    have htmesh : ((N + 1 : ℕ) : ℝ) * meshStep t N = t := by
      simp only [meshStep, Nat.cast_add, Nat.cast_one]
      field_simp
    simpa only [htmesh] using hN.1 (N + 1) le_rfl
  have hb := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hc := hb.const_smul t
  have hid (N : ℕ) :
      t • relativeDiscretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1) =
        discretePosition (meshCurvature d.R t N) (meshStep t N) (N + 1) := by
    rw [relativeDiscretePosition_pos _ _ (Nat.succ_pos N)]
    have htmesh : ((N + 1 : ℕ) : ℝ) * meshStep t N = t := by
      simp only [meshStep, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [htmesh, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  simpa only [hid, normalizedJacobi_pos d.initial_position ht.ne', smul_smul,
    mul_inv_cancel₀ ht.ne', one_smul] using hc

theorem normalizedDiscrete_eventually_isUnit (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete (meshCurvature d.R t N) (meshStep t N) i).det := by
  have hcJ : ContinuousOn d.J (Set.Icc 0 t) := fun s hs =>
    (d.position_derivative s hs).continuousAt.continuousWithinAt
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  obtain ⟨K, _, hK⟩ := eventually_mesh_inverse_bounds ht.le
    (normalizedJacobi_continuousOn hcJ hd0)
    (normalizedJacobi_isUnit d.initial_position hd0 hpre) d.positionError_tendsto
    ((d.uniform_errors ht).mono fun _ h => h.1)
  filter_upwards [hK] with N hN i hi0 hiN
  have hh : meshStep t N ≠ 0 := ne_of_gt (div_pos ht (by positivity))
  have hbi := (hN i hiN).1
  rw [relativeDiscretePosition_pos _ _ (by omega)] at hbi
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have hx := isUnit_of_divided_time (mul_ne_zero hi' hh) hbi
  have hs : IsUnit (algebraMap ℝ NormalMatrix (meshStep t N)⁻¹) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hh)).map (algebraMap ℝ NormalMatrix)
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  simpa only [normalizedDiscrete, Algebra.smul_def] using hs.mul hx

theorem curvatureDirichlet_det_tendsto (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    Tendsto (fun N : ℕ => (meshStep t N) ^ 3 *
      (curvatureDirichlet t (fun i : Fin N =>
        d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1)).det)
      atTop (nhds (d.J t).det) := by
  exact curvatureDirichlet_det_tendsto_of_position_tendsto ht.ne'
    (meshCurvature d.R t) (fun N i => d.symmetric _) (d.J t)
    (d.normalizedDiscrete_eventually_isUnit ht hpre) (d.endpoint_position_tendsto ht)

end RegularJacobi

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSineReference
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference determinant limit is instantiated by the sine Jacobi curve. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem reference_determinant_tendsto {t : ℝ} (ht : 0 < t) (htπ : t < Real.pi) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 3 * (referenceMatrix t N).det ^ 3)
      atTop (nhds (Real.sin t ^ 3)) := by
  have h := (sineJacobi t).curvatureDirichlet_det_tendsto ht
    (sineJacobi_preconjugate htπ)
  have hz (N : ℕ) : Matrix.blockDiagonal (fun _ : Fin N => (0 : NormalMatrix)) = 0 :=
    Matrix.blockDiagonal_zero
  simpa only [sineJacobi, meshStep, curvatureDirichlet, sub_self,
    hz, smul_zero, sub_zero, det_scalarLift,
    Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] using h

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiRadialODE
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Jacobi.entryCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial determinant comparison from the Jacobi ODE. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

namespace RegularJacobi

variable {t : ℝ} (d : RegularJacobi t)

open scoped Matrix.Norms.Frobenius

/-- The Jacobi radial inequality follows from the ODE, trace normalization,
and preconjugacy. -/
theorem radial_determinant_comparison (ht : 0 < t) (htπ : t < Real.pi)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s))
    (htrace : ∀ s, (d.R s).trace = 3)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    (d.J t).det ≤ Real.sin t ^ 3 * ((1 : NormalMatrix) -
      (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
        (∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s)).det := by
  apply continuous_radial_comparison ht htπ (radialCurvature d.R t)
    (fun s => by simp [radialCurvature, Matrix.trace_sub, htrace]) hL hc hLip
  · simpa only [sampled_radialCurvature] using d.curvatureDirichlet_eventually_posDef ht hpre
  · simpa only [sampled_radialCurvature, meshStep] using d.curvatureDirichlet_det_tendsto ht hpre
  · exact reference_determinant_tendsto ht htπ

/-- The limiting compression is positive semidefinite, including a singular
limit; this is the spectral input for the subsequent determinant deficit. -/
theorem radial_compression_posSemidef (ht : 0 < t) (htπ : t < Real.pi)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s))
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    ((1 : NormalMatrix) - (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) •
      (∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s)).PosSemidef := by
  apply continuous_radial_compression_posSemidef ht.le htπ _ hL hc hLip
  simpa only [sampled_radialCurvature] using d.curvatureDirichlet_eventually_posDef ht hpre

end RegularJacobi

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiRadialDeficit
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative radial deficit before the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi.RegularJacobi

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

variable {t : ℝ} (d : RegularJacobi t)

/-- The actual Jacobi determinant loses a definite fraction of the squared
sine-weighted averaged curvature. -/
theorem radial_determinant_deficit (ht : 0 < t) (htπ : t < Real.pi)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s))
    (hR : Continuous d.R) (hRpos : ∀ s, (d.R s).PosSemidef)
    (htrace : ∀ s, (d.R s).trace = 3)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    (d.J t).det ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        ‖∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s‖ ^ 2) := by
  let A := radialCurvature d.R t
  let B : NormalMatrix := ∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s
  have hA : Continuous A := (hR.comp (continuous_id.mul_const t)).sub continuous_const
  have hAt : ∀ s, (A s).trace = 0 := fun s => by
    simp [A, radialCurvature, Matrix.trace_sub, htrace]
  have hAp : ∀ s, (A s + 1).PosSemidef := fun s => by
    simpa only [A, radialCurvature, sub_add_cancel] using hRpos (s * t)
  have hBt : B.trace = 0 := sine_average_trace hA hAt
  have hBp : (B + 1).PosSemidef := sine_average_add_one_posSemidef hA hAp
  have hBh : B.IsHermitian := by
    simpa only [add_sub_cancel_right] using hBp.isHermitian.sub (isHermitian_one :
      (1 : NormalMatrix).IsHermitian)
  have hβ : 0 ≤ t ^ 2 / (Real.pi ^ 2 - t ^ 2) := by
    apply div_nonneg (sq_nonneg t)
    nlinarith [Real.pi_pos]
  have hdef := matrix_preconjugate_loss hBh hβ hBt hBp
    (d.radial_compression_posSemidef ht htπ hpre hL hc hLip)
  exact (d.radial_determinant_comparison ht htπ hpre htrace hL hc hLip).trans
    (mul_le_mul_of_nonneg_left hdef (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht htπ).le 3))

end

end PositiveEinsteinFour.Jacobi.RegularJacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AveragedRadial
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the proved Jacobi determinant deficit over initial geodesics.
The density is explicitly truncated at the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Jacobi.instNormedAddCommGroupNormalMatrix_2
attribute [local instance] OAI.PositiveEinsteinFour.Jacobi.instNormedSpaceRealNormalMatrix_1
theorem RegularJacobi.truncatedDensity_le {t : ℝ} (d : RegularJacobi t)
    (ht : 0 < t) (htπ : t < Real.pi)
    (hR : Continuous d.R) (hpos : ∀ s, (d.R s).PosSemidef)
    (htrace : ∀ s, (d.R s).trace = 3)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    d.truncatedDensity ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        ‖∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s‖ ^ 2) := by
  classical
  unfold truncatedDensity
  split_ifs with hpre
  · exact d.radial_determinant_deficit ht htπ hpre hR hpos htrace hL hc hLip
  · exact d.radial_deficit_nonneg ht.le htπ hR hpos htrace

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

attribute [local instance] OAI.PositiveEinsteinFour.Jacobi.instNormedAddCommGroupContinuousMapNormalMatrix_1
attribute [local instance] OAI.PositiveEinsteinFour.Jacobi.instNormedSpaceRealContinuousMapNormalMatrix_1
/-- The actual averaged radial determinant estimate. Its mean-square and
energy hypotheses apply to the field, rather than to individual geodesics.
All matrix comparison, finite approximation and averaging steps are proved. -/
theorem averaged_truncatedDensity_le {t q : ℝ}
    (d : Ω → RegularJacobi t) {F G : ℝ → C(Ω, NormalMatrix)}
    (ht : 0 < t) (htπ : t < Real.pi) (hq : 0 ≤ q)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = q)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * q)
    (hcurvature : ∀ x r, (d x).R r = 1 + F r x)
    (hpos : ∀ x r, ((d x).R r).PosSemidef)
    (htrace : ∀ x r, ((d x).R r).trace = 3)
    (hLip : ∀ x, ∃ L : ℝ, 0 ≤ L ∧ ∀ s r,
      ‖Averages.sineWeight s • radialCurvature (d x).R t s -
        Averages.sineWeight r • radialCurvature (d x).R t r‖ ≤ L * |s - r|)
    (hD : Integrable (fun x => (d x).truncatedDensity) μ) :
    (∫ x, (d x).truncatedDensity ∂μ) ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        q * (1 - (t / Real.pi) ^ 2 / 2)) := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun r => (hderiv r).continuousAt
  have hFt : Continuous (fun u => F (t * u)) := hF.comp (continuous_const.mul continuous_id)
  let B : C(Ω, NormalMatrix) := ∫ u, F (t * u) ∂Averages.sineMeasure
  have hB (x : Ω) : B x = ∫ u, F (t * u) x ∂Averages.sineMeasure :=
    ContinuousMap.integral_apply (Averages.integrable_sineMeasure hFt) x
  have hR (x : Ω) : Continuous (d x).R := by
    have hc := (ContinuousMap.evalCLM ℝ x).continuous.comp hF
    have heq : (d x).R = fun r => 1 + F r x := funext (hcurvature x)
    rw [heq]
    exact continuous_const.add hc
  have hA (x : Ω) : Continuous (fun s =>
      Averages.sineWeight s • radialCurvature (d x).R t s) := by
    unfold Averages.sineWeight radialCurvature
    fun_prop
  have hmean (x : Ω) :
      (∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature (d x).R t s) = B x := by
    rw [← Averages.integral_sineMeasure, hB]
    congr 1
    funext s
    simp [radialCurvature, hcurvature, mul_comm]
  have hQ : Integrable (fun x => ‖B x‖ ^ 2) μ := by
    rw [← integrableOn_univ]
    exact (B.continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_univ
  let c := lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6
  have hc : 0 ≤ c := by dsimp [c, lossFactor]; positivity
  have hi : Integrable (fun x => Real.sin t ^ 3 * (1 - c * ‖B x‖ ^ 2)) μ :=
    ((integrable_const 1).sub (hQ.const_mul c)).const_mul _
  have hpoint (x : Ω) : (d x).truncatedDensity ≤
      Real.sin t ^ 3 * (1 - c * ‖B x‖ ^ 2) := by
    obtain ⟨L, hL, hbound⟩ := hLip x
    simpa only [hmean, c] using (d x).truncatedDensity_le ht htπ (hR x)
      (hpos x) (htrace x) hL (hA x) hbound
  have hint := integral_mono hD hi hpoint
  have heq : (∫ x, Real.sin t ^ 3 * (1 - c * ‖B x‖ ^ 2) ∂μ) =
      Real.sin t ^ 3 * (1 - c * (∫ x, ‖B x‖ ^ 2 ∂μ)) := by
    rw [integral_const_mul, integral_sub (integrable_const 1) (hQ.const_mul c),
      integral_const_mul]
    simp
  rw [heq] at hint
  have hmeanbound := matrix_geodesic_mean_square_lower hq hderiv hstationary henergy (t := t)
  simp_rw [← hB] at hmeanbound
  have hmul := mul_le_mul_of_nonneg_left hmeanbound hc
  have hsin : 0 ≤ Real.sin t ^ 3 := pow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht htπ).le 3
  have hmul' := mul_le_mul_of_nonneg_left hmul hsin
  dsimp only [c] at hint hmul'
  nlinarith only [hint, hmul']

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undetermined Hessian in concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The highest Hessian tensor is symmetric in its derivatives, has zero
trace, and satisfies the differentiated Bianchi equation. -/
def condition (X : Hessian) : Prop :=
  (∀ i j, X i j = X j i) ∧
  (∀ i j, symmetric (X i j) ∧ traceFree (X i j)) ∧
  hessianTrace X = 0 ∧ ∀ i r, divergence X i r = 0


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestVectorSpace
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the concrete highest-Hessian coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem symmetricArray_add (a b : Fin 10 → Mat) :
    symmetricArray (a + b) = symmetricArray a + symmetricArray b := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem symmetricArray_smul (r : ℝ) (a : Fin 10 → Mat) :
    symmetricArray (r • a) = r • symmetricArray a := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem highest_add (c d : Fin 21 → ℝ) : highest (c + d) = highest c + highest d := by
  unfold highest
  rw [entries_add, symmetricArray_add]

theorem highest_smul (r : ℝ) (c : Fin 21 → ℝ) : highest (r • c) = r • highest c := by
  unfold highest
  rw [entries_smul, symmetricArray_smul]


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestActionCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total plus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Simultaneous plus rotation of both derivative slots and the matrix slots. -/
def totalPlus (s : Fin 3) (X : Hessian) : Hessian := fun i j a b =>
  matrixAction s (X i j) a b +
    (∑ k, quaternionMatrix s i k * X k j a b) +
    ∑ k, quaternionMatrix s j k * X i k a b


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

theorem tensorCoordinates_pairing (X Y : Hessian) :
    (∑ p : TensorIndex, tensorCoordinates X p * tensorCoordinates Y p) =
      hessianPairing X Y := by
  simp only [Fintype.sum_prod_type, tensorCoordinates, hessianPairing]
  calc
    _ = ∑ i : Fin 4, ∑ a : Fin 3, ∑ j : Fin 4, ∑ b : Fin 3,
        X i j a b * Y i j a b := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a : Fin 3, ∑ i : Fin 4, ∑ j : Fin 4, ∑ b : Fin 3,
        X i j a b * Y i j a b := Finset.sum_comm
    _ = ∑ a : Fin 3, ∑ i : Fin 4, ∑ b : Fin 3, ∑ j : Fin 4,
        X i j a b * Y i j a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def totalMinus (s : Fin 3) (X : Hessian) : Hessian := fun i j a b =>
  (∑ k, rightQuaternion s i k * X k j a b) +
    ∑ k, rightQuaternion s j k * X i k a b

@[simp] theorem minusCoordinates_2_4 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 4 = -c 1 - c 20 := rfl

@[simp] theorem minusCoordinates_2_5 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 5 = c 0 + c 7 + 2 * c 15 := rfl

@[simp] theorem minusCoordinates_2_6 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 6 = 2 * c 8 + 2 * c 14 := rfl


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestProjection
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orthogonal projection is constructed from the actual tensor subspace. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

@[simp] theorem hessianVector_vectorHessian (v : HessianSpace) :
    hessianVector (vectorHessian v) = v := by
  ext p
  rcases p with ⟨i, j, a, b⟩
  rfl

theorem hessianVector_inner (X Y : Hessian) :
    inner ℝ (hessianVector X) (hessianVector Y) = hessianPairing X Y := by
  simpa [hessianVector, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
    tensorCoordinates_pairing X Y

/-- The explicit twenty-one-coordinate map, regarded as a linear map into
the Euclidean space of all four-slot tensors. -/
def highestLinearMap : (Fin 21 → ℝ) →ₗ[ℝ] HessianSpace where
  toFun c := hessianVector (highest c)
  map_add' c d := by
    ext p
    rcases p with ⟨i, j, a, b⟩
    change highest (c + d) i j a b = highest c i j a b + highest d i j a b
    rw [highest_add]
    rfl
  map_smul' r c := by
    ext p
    rcases p with ⟨i, j, a, b⟩
    change highest (r • c) i j a b = r * highest c i j a b
    rw [highest_smul]
    rfl

def highestSubspace : Submodule ℝ HessianSpace := highestLinearMap.range

/-- The actual orthogonal projection onto the symmetry/trace/Bianchi subspace. -/
def highestProjection (X : Hessian) : Hessian :=
  vectorHessian (highestSubspace.starProjection (hessianVector X))

/-- The unsymmetrized weight derivative tensor `dm ⊗ ∇T`. -/
def weightTensor (a : Vec) (Z : Tensor) : Hessian :=
  fun i j b c => a i * Z.matrix b c j

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledOperator
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real coupled operator used for the plus projection. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- A real outer vector tensored with an arbitrary matrix-valued four-vector. -/
def rawWeight (a : Vec) (Z : RawGradient) : Hessian := fun i j b c => a i * Z b c j

/-- The actual polynomial used for the total-plus spectral projection. -/
def plusPolynomial (X : Hessian) : Hessian :=
  (1 / 12 : ℝ) • ((7 : ℝ) • X - coupledOperator X)

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoupledCasimir
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plus spectral polynomial on the actual highest-Hessian space. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

def rawSlice (X : Hessian) (i : Fin 4) : RawGradient := fun b c =>
  WithLp.toLp 2 (fun j => X i j b c)

def outerAction (s : Fin 3) (X : Hessian) : Hessian := fun i j b c =>
  quaternion s (WithLp.toLp 2 (fun k => X k j b c)) i

def innerAction (s : Fin 3) (X : Hessian) : Hessian := fun i j b c =>
  matrixAction s (X i j) b c + ∑ k, quaternionMatrix s j k * X i k b c

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalizedBlockNorm_nonneg (T : Mat3) : 0 ≤ normalizedBlockNorm T :=
  Real.sqrt_nonneg _

/-- Vanishing of the normalized norm is exactly vanishing of the concrete
curvature block. -/
theorem normalizedBlockNorm_eq_zero_iff (T : Mat3) :
    normalizedBlockNorm T = 0 ↔ T = 0 := by
  constructor
  · intro hz
    have hsum : (∑ i, ∑ j, T i j ^ 2) = 0 := by
      have hs := normalizedBlockNorm_sq T
      rw [hz] at hs
      linarith
    ext i j
    have hj : T i j ^ 2 ≤ ∑ k, T i k ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have hi : (∑ k, T i k ^ 2) ≤ ∑ a, ∑ k, T a k ^ 2 :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hsq : T i j ^ 2 = 0 := le_antisymm (hsum ▸ hj.trans hi) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsq
  · rintro rfl
    simp [normalizedBlockNorm]

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrthonormalFrame
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of the concrete orthonormal frames used for the curvature
blocks. This is obtained from the actual positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff MatrixOrder

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

instance instNonemptyOrthonormalFrame (g : SmoothMetric M) (c : M) : Nonempty (OrthonormalFrame g c) :=
  ⟨canonicalFrame g c⟩

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete each unit direction to its quaternionic orthonormal frame.
This relates spherical fiber averages to actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

theorem directionFrameMatrix_succ (q : Directions) (i : Fin 4) (s : Fin 3) :
    directionFrameMatrix q i s.succ = normalVector q s i := by
  fin_cases i <;> fin_cases s <;>
    simp [directionFrameMatrix, normalVector, TraceHessian.quaternionMatrix,
      Fin.sum_univ_succ]

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Link the normal-tensor calculation to the concrete metric. The classical
curvature decomposition is displayed as an explicit local hypothesis here;
the angular mean identities themselves are proved, not postulated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3
theorem squareNorm_eq_frobenius_norm_sq (T : Mat3) : squareNorm T = ‖T‖ ^ 2 := by
  symm
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [squareNorm, Real.norm_eq_abs, sq_abs]

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureForm
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coordinate curvature is a four-linear form. This supplies
the multilinearity used to change normal frames without an independent
curvature-transformation assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameCurvature_eq_form (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l =
      curvatureForm g c ![e.vector i, e.vector j, e.vector k, e.vector l] := rfl

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure in the geometric application is fixed by the metric. In four
Euclidean dimensions the diameter-normalized Hausdorff measure is multiplied
by the unit-ball factor `(pi^2 / 2) / 2^4`. Positivity and finiteness are kept
separate from the elementary probability normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem totalVolume_pos {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    0 < totalVolume g := by
  exact ENNReal.toReal_pos (ne_of_gt h.positive) (ne_of_lt h.finite)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.QuaternionFrame.rawField_fieldRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Weyl gradient, with its derivative index treated as a tangent
vector. These changes of coordinate retain every component: neither the
Bianchi equation nor a differential estimate is built into the definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bianchi TraceHessian
open scoped Manifold ContDiff

noncomputable section

theorem gradientTensor_traceFree (Z : Gradient) (ht : ∀ i, traceFree (Z i)) :
    (gradientTensor Z).traceFree := by
  ext i
  simpa [Tensor.traceFree, gradientTensor, traceFree, Fin.sum_univ_three] using ht i

theorem gradientTensor_divergence (Z : Gradient) (hs : ∀ i, symmetric (Z i))
    (r : Fin 3) (i : Fin 4) :
    (gradientTensor Z).divergence r i = gradientDivergence Z r i := by
  rw [Tensor.divergence_eq_sum]
  simp_rw [gradientTensor_matrix Z hs]
  change (∑ s, quaternion s (WithLp.toLp 2 (fun j => Z j s r))) i = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  unfold gradientDivergence
  apply Finset.sum_congr rfl
  intro s _
  exact (quaternionMatrix_apply s (WithLp.toLp 2 (fun j => Z j s r)) i).symm

theorem gradientTensor_bianchi (Z : Gradient) (hs : ∀ i, symmetric (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) : (gradientTensor Z).bianchi := by
  intro r
  ext i
  exact gradientTensor_divergence Z hs r i |>.trans (hb r i)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotCubic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot correction is the actual cubic trace in the
weighted Hessian identity. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Angular Matrix

noncomputable section

theorem matrixPairing_eq_trace (A B : Mat) :
    matrixPairing A B = Matrix.trace (A * Bᵀ) := by
  simp only [matrixPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]

theorem matrixSlotAction_eq (A M : Mat) :
    matrixSlotAction A M = (1 / 2 : ℝ) • (A * M + M * A) -
      (Matrix.trace (A * M) / 3) • (1 : Mat) := by
  ext a b
  simp only [matrixSlotAction, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionReflections
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pure quaternion lifts of the reflections needed to choose a local
spectral frame. Only their concrete action on the two quaternion triples
is used; no global eigenframe or representation theorem is assumed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- A left pure-quaternion frame change fixes the opposite triple. -/
theorem imaginaryLeft_commutes_opposite (u : Fin 3 → ℝ) (s : Fin 3) :
    imaginaryCombination quaternionMatrix u * Angular.oppositeMatrix s =
      Angular.oppositeMatrix s * imaginaryCombination quaternionMatrix u := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Angular.oppositeMatrix_commute]

/-- A right pure-quaternion frame change fixes the positive triple. -/
theorem imaginaryRight_commutes_positive (u : Fin 3 → ℝ) (s : Fin 3) :
    imaginaryCombination Angular.oppositeMatrix u * quaternionMatrix s =
      quaternionMatrix s * imaginaryCombination Angular.oppositeMatrix u := by
  simp only [imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Angular.oppositeMatrix_commute]

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionLifts
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition of the concrete quaternion frame changes.  These identities
keep the action on both Weyl blocks, so they can be used at a single point
without selecting a moving eigenframe. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- Every unit axis reflection has an explicit left-quaternion lift. -/
def QuaternionLift.leftAxis (u : Fin 3 → ℝ) (hu : ∑ r, u r ^ 2 = 1) :
    QuaternionLift quaternionMatrix Angular.oppositeMatrix (axisReflection u) where
  matrix := imaginaryCombination quaternionMatrix u
  orthogonal := imaginaryCombination_orthogonal quaternionMatrix
    Angular.quaternionMatrix_anticommutator Angular.quaternionMatrix_transpose u hu
  orientation := imaginaryLeft_det_one u hu
  intertwines := imaginaryCombination_intertwines quaternionMatrix
    Angular.quaternionMatrix_anticommutator u hu
  opposite := imaginaryLeft_commutes_opposite u

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionGenerators
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rotation of the matrix indices is recovered from the actual
quaternion commutator.  Thus a four-dimensional quaternion lift also
intertwines the three-dimensional infinitesimal rotation generators. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem QuaternionLift.mul_transpose {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R) :
    P.matrix * P.matrixᵀ = 1 :=
  mul_eq_one_comm.mp P.orthogonal

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceDecomposition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local tensor identities imply the highest-Hessian constraints. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem divergence_add (X Y : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (X + Y) i r = divergence X i r + divergence Y i r := by
  have h (s : Fin 3) :
      WithLp.toLp 2 (fun j => (X + Y) i j s r) =
        WithLp.toLp 2 (fun j => X i j s r) + WithLp.toLp 2 (fun j => Y i j s r) := rfl
  simp only [divergence, h, quaternion_add, Finset.sum_add_distrib]

theorem divergence_smul (a : ℝ) (X : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (a • X) i r = a • divergence X i r := by
  have h (s : Fin 3) :
      WithLp.toLp 2 (fun j => (a • X) i j s r) =
        a • WithLp.toLp 2 (fun j => X i j s r) := rfl
  simp only [divergence, h, quaternion_smul, Finset.smul_sum]

theorem divergence_sub (X Y : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (X - Y) i r = divergence X i r - divergence Y i r := by
  rw [sub_eq_add_neg, divergence_add]
  have h : divergence (-Y) i r = -divergence Y i r := by
    simpa only [neg_one_smul] using divergence_smul (-1) Y i r
  rw [h, sub_eq_add_neg]

theorem traceComponent_divergence (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i : Fin 4) (r : Fin 3) : divergence (traceComponent M) i r = 0 := by
  change divergence ((5 / 12 : ℝ) • traceLift M) i r = 0
  rw [divergence_smul]
  change (5 / 12 : ℝ) • liftDivergence M i r = 0
  rw [traceLift_bianchi M hs ht, smul_zero]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianAssembly
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the actual weighted Hessian square and its Green contributions. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Polarization is applied before any symmetry is imposed on the weight tensor. -/
def weightedQuadratic (q : Hessian → ℝ) (m : ℝ) (X L : Hessian) : ℝ :=
  (m * q X + (q (X + L) - q X - q L) / 2) / 6

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestGram
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Casimir lower bound with arbitrary symmetric matrix coefficients.
Positive semidefiniteness is applied to each actual tensor coordinate. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian

noncomputable section

/-- The matrix-weighted Gram form of three actual Hessian arrays. -/
def hessianGram (A : Mat) (F : Fin 3 → Hessian) : ℝ :=
  ∑ r, ∑ s, A r s * hessianPairing (F r) (F s)

/-- The same local Casimir expression accepts complete Weyl matrices. -/
def generalCasimirCurvatureForm (A U : Mat) (X : Hessian) : ℝ :=
  4 * hessianNormSq X + hessianGram A (fun r => totalPlus r X) / 24 +
    hessianGram U (fun r => totalMinus r X) / 4

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotCompression
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded matrix-slot operator and the concrete Bianchi compression
use the same Euclidean pairing and normalization. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

def rawGradientVector (Z : RawGradient) : GradientVector :=
  WithLp.toLp 2 (rawCoordinates Z)

def tensorGradientVector (Z : Tensor) : GradientVector := rawGradientVector Z.matrix

theorem inner_rawGradientVector (Z W : RawGradient) :
    inner ℝ (rawGradientVector Z) (rawGradientVector W) = rawPairing Z W := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    rawGradientVector, rawPairing]
  apply Finset.sum_congr rfl
  intro p _
  ring

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricCurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivative-slot integration for the actual metric Weyl Hessian. The
coefficient and its derivative are both the concrete quaternion curvature
block. The only differential premises are parallel differentiation and
the classical divergence and skew identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

theorem inner_matrixVector (A B : Mat) :
    inner ℝ (matrixVector A) (matrixVector B) = matrixPairing A B := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixVector, Fintype.sum_prod_type, matrixPairing]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def framePlusCoefficient (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (plusWeyl g e.base e.frame) quaternionMatrix p.1.1 p.1.2 p.2.2 p.2.1

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricMatrixGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying-coefficient Green identity for the actual Weyl matrix slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance instNormedAddCommGroupMat_1_re98581_1 : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat_1_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
def frameWeylMatrix (g : SmoothMetric M) (e : FrameBundle g) : Mat :=
  plusWeyl g e.base e.frame

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricMinusGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite curvature block acting on the plus Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameMinusCoefficient (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (minusWeyl g e.base e.frame) oppositeMatrix p.1.1 p.1.2 p.2.2 p.2.1


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylMatrixEquation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Weyl matrix equation in an arbitrary orthonormal frame. This
derivation uses the actual Bianchi Hessian and curvature commutator, so
no eigenframe is differentiated. -/

namespace PositiveEinsteinFour.TraceHessian

open scoped BigOperators
open Matrix
open HighestHessian

noncomputable section

set_option maxHeartbeats 1000000 in
theorem matrixAction_square_coordinates (a b c d e : ℝ) (r : Fin 3) :
    matrixAction r (traceFreeSquare (ofCoordinates a b c d e)) =
      -(∑ s, ofCoordinates a b c d e r s • matrixAction s (ofCoordinates a b c d e)) := by
  ext i j
  simp only [traceFreeSquare, matrixAction, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul]
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [rotation, ofCoordinates, Matrix.one_apply, Fin.sum_univ_three] <;> ring

/-- The infinitesimal rotation of the trace-free square is computed
without a diagonalization hypothesis. -/
theorem matrixAction_traceFreeSquare (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (r : Fin 3) :
    matrixAction r (traceFreeSquare M) = -(∑ s, M r s • matrixAction s M) := by
  simpa only [coordinates_eq M hs ht] using
    matrixAction_square_coordinates (M 0 0) (M 1 1) (M 0 1) (M 0 2) (M 1 2) r

theorem matrixAction_weylLaplacian (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (r : Fin 3) :
    matrixAction r (weylLaplacian M) =
      (6 : ℝ) • (matrixAction r M + ∑ s, M r s • matrixAction s M) := by
  have hlin : matrixAction r (weylLaplacian M) =
      (6 : ℝ) • (matrixAction r M - matrixAction r (traceFreeSquare M)) := by
    ext a b
    simp only [weylLaplacian, matrixAction, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  rw [hlin, matrixAction_traceFreeSquare M hs ht, sub_neg_eq_add]

theorem traceComponent_weylLaplacian_skew (M : Mat)
    (hs : symmetric M) (ht : traceFree M) (i j : Fin 4) (a b : Fin 3) :
    traceComponent (weylLaplacian M) i j a b -
      traceComponent (weylLaplacian M) j i a b = bundleCurvatureAction M i j M a b := by
  rw [traceComponent_skew]
  have h (r : Fin 3) := congrArg (fun N : Mat => N a b)
    (matrixAction_weylLaplacian M hs ht r)
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  simp_rw [h]
  simp only [bundleCurvatureAction, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Polarization of the actual derivative-slot Green integrands. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry
open CurvatureContraction

noncomputable section

def derivativePairing (A : DerivativeCoefficient) (X Y : Hessian) : ℝ :=
  ∑ p : Averages.CurvatureIndex,
    A p.1.1 p.1.2 p.2.1 p.2.2 * matrixPairing (X p.1.1 p.2.1) (Y p.1.2 p.2.2)

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The matrix-slot Hessian quadratic form is exactly the left side of
the varying-operator Green identity, including the unsymmetrized weight. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def matrixHessianPairing (A : Mat) (X Y : Hessian) : ℝ :=
  ∑ i, inner ℝ (gradientVector (X i))
    (matrixSlotOperator A (gradientVector (Y i)))

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The prescribed-trace coefficient and its ordinary derivative in an
arbitrary frame. No derivative of a matrix eigenframe is used. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian HighestHessian Bianchi
open scoped BigOperators

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.traceCoefficientNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.traceCoefficientNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.traceCoefficientNormedAlgebra
def traceCoefficient (A : Mat) : Mat :=
  (4 + Matrix.trace (A * A) / 6) • A - (5 : ℝ) • traceFreeSquare A

def traceCoefficientDerivative (A Z : Mat) : Mat :=
  (4 + Matrix.trace (A * A) / 6) • Z +
    (Matrix.trace (A * Z) / 3) • A - (10 : ℝ) • matrixSlotAction A Z

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci-commuted gradient equation for the actual metric. The two
classical slot identities remain explicit, while the differentiated trace
and curvature-divergence equations are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem tensorGradientVector_gradientTensor (Z : Angular.Gradient)
    (hs : ∀ i, symmetric (Z i)) :
    tensorGradientVector (gradientTensor Z) = gradientVector Z := by
  ext p
  rcases p with ⟨i, a, b⟩
  change (gradientTensor Z).matrix a b i = Z i a b
  rw [gradientTensor_matrix Z hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full prescribed-trace Green identity for the actual metric,
derived by differentiating its invariant polynomial coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.metricTraceNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.metricTraceNormedSpace
local instance metricTraceNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuous_traceCoefficient : Continuous traceCoefficient := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [traceCoefficient, traceFreeSquare, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  fun_prop

theorem continuous_traceCoefficientDerivative :
    Continuous (fun p : Mat × Mat => traceCoefficientDerivative p.1 p.2) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [traceCoefficientDerivative, matrixSlotAction, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul]
  by_cases hab : a = b
  · simp only [hab, ite_true, if_true]
    fun_prop
  · simp only [hab, ite_false, if_false]
    fun_prop

def traceCoefficientVectorMap : C(Mat, MatrixVector) :=
  ⟨fun A => matrixVector (traceCoefficient A),
    matrixVectorMap.continuous.comp continuous_traceCoefficient⟩

def traceCoefficientDerivativeVectorMap : C(Mat × Mat, MatrixVector) :=
  ⟨fun p => matrixVector (traceCoefficientDerivative p.1 p.2),
    matrixVectorMap.continuous.comp continuous_traceCoefficientDerivative⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiate the actual normalized Weyl norm on its positive set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian
open scoped BigOperators

noncomputable section

local instance weylNormNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance weylNormNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance weylNormNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem trace_square_eq_six_norm_sq (A : Mat) (hA : symmetric A) :
    Matrix.trace (A * A) = 6 * normalizedBlockNorm A ^ 2 := by
  rw [normalizedBlockNorm_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hsum : (∑ i, ∑ j, A i j * A j i) = ∑ i, ∑ j, A i j ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA j i, pow_two]
  rw [hsum]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ricci commutation before any pointwise spectral decomposition. All
matrix and derivative slots stay in the same arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

/-- The uncompressed Ricci right side in an arbitrary frame. The first
coefficient is `6 + 3`; the remaining two terms are the differentiated
matrix equation and the full bundle curvature contribution. -/
def invariantRicciGradient (A : Mat) (Z : Angular.Gradient) : Angular.Gradient :=
  fun j => (9 : ℝ) • Z j - (12 : ℝ) • matrixSlotAction A (Z j) +
    (2 : ℝ) • ∑ i, bundleCurvatureAction A i j (Z i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedRing
local instance smoothWeylNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedAlgebra
def regularizedBlockNorm (ε : ℝ) (A : Mat) : ℝ :=
  Real.sqrt (normalizedBlockNorm A ^ 2 + ε ^ 2)

def regularizedRadialDerivative (ε : ℝ) (A Z : Mat) : ℝ :=
  Matrix.trace (A * Z) / (6 * regularizedBlockNorm ε A)

def regularizedWeylWeight (ε : ℝ) (A B : Mat) : ℝ :=
  (1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B)) ^ 2

def regularizedWeylWeightDerivative (ε : ℝ) (A B Z V : Mat) : ℝ :=
  -(3 / 4 : ℝ) *
    (1 - (3 / 8 : ℝ) * (regularizedBlockNorm ε A - regularizedBlockNorm ε B)) *
    (regularizedRadialDerivative ε A Z - regularizedRadialDerivative ε B V)

theorem regularizedBlockNorm_zero (A : Mat) :
    regularizedBlockNorm 0 A = normalizedBlockNorm A := by
  simp [regularizedBlockNorm, Real.sqrt_sq (normalizedBlockNorm_nonneg A)]

theorem regularizedBlockNorm_pos (ε : ℝ) (hε : 0 < ε) (A : Mat) :
    0 < regularizedBlockNorm ε A := by
  unfold regularizedBlockNorm
  positivity

theorem norm_le_regularizedBlockNorm (ε : ℝ) (A : Mat) :
    normalizedBlockNorm A ≤ regularizedBlockNorm ε A := by
  unfold regularizedBlockNorm
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ε]

theorem continuous_regularizedBlockNorm (ε : ℝ) :
    Continuous (regularizedBlockNorm ε) := by
  unfold regularizedBlockNorm normalizedBlockNorm
  fun_prop

theorem continuous_normalizedBlockNorm : Continuous normalizedBlockNorm := by
  have heq : regularizedBlockNorm 0 = normalizedBlockNorm :=
    funext regularizedBlockNorm_zero
  rw [← heq]
  exact continuous_regularizedBlockNorm 0

theorem continuous_regularizedRadialDerivative {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z : Ω → Mat) (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => regularizedRadialDerivative ε (A x) (Z x)) := by
  have ht : Continuous (fun x => Matrix.trace (A x * Z x)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  exact ht.div (continuous_const.mul ((continuous_regularizedBlockNorm ε).comp hA))
    (fun x => ne_of_gt (mul_pos (by norm_num) (regularizedBlockNorm_pos ε hε (A x))))

theorem continuous_regularizedWeylWeight {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (A B : Ω → Mat) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => regularizedWeylWeight ε (A x) (B x)) := by
  exact (continuous_const.sub (continuous_const.mul
    (((continuous_regularizedBlockNorm ε).comp hA).sub
      ((continuous_regularizedBlockNorm ε).comp hB)))).pow 2

theorem continuous_regularizedWeylWeightDerivative {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A B Z V : Ω → Mat)
    (hA : Continuous A) (hB : Continuous B) (hZ : Continuous Z) (hV : Continuous V) :
    Continuous (fun x => regularizedWeylWeightDerivative ε (A x) (B x) (Z x) (V x)) := by
  exact (continuous_const.mul (continuous_const.sub (continuous_const.mul
    (((continuous_regularizedBlockNorm ε).comp hA).sub
      ((continuous_regularizedBlockNorm ε).comp hB))))).mul
        ((continuous_regularizedRadialDerivative ε hε A Z hA hZ).sub
          (continuous_regularizedRadialDerivative ε hε B V hB hV))

theorem hasDerivAt_regularizedBlockNorm {A : ℝ → Mat} {Z : Mat} {r ε : ℝ}
    (hA : HasDerivAt A Z r) (hs : ∀ t, symmetric (A t)) (hε : 0 < ε) :
    HasDerivAt (fun t => regularizedBlockNorm ε (A t))
      (regularizedRadialDerivative ε (A r) Z) r := by
  have hd := ((hasDerivAt_matrixTrace (hA.mul hA)).div_const 6).add_const (ε ^ 2)
  have hn : Matrix.trace (A r * A r) / 6 + ε ^ 2 ≠ 0 := by
    rw [trace_square_eq_six_norm_sq _ (hs r)]
    positivity
  have hroot := hd.sqrt hn
  change HasDerivAt (fun t => Real.sqrt (Matrix.trace (A t * A t) / 6 + ε ^ 2))
    (Matrix.trace (Z * A r + A r * Z) / 6 /
      (2 * Real.sqrt (Matrix.trace (A r * A r) / 6 + ε ^ 2))) r at hroot
  have heq : (fun t => Real.sqrt (Matrix.trace (A t * A t) / 6 + ε ^ 2)) =
      fun t => regularizedBlockNorm ε (A t) := by
    funext t
    unfold regularizedBlockNorm
    rw [trace_square_eq_six_norm_sq _ (hs t)]
    congr 2
    ring
  rw [heq] at hroot
  convert! hroot using 1
  all_goals try with_reducible_and_instances rfl
  unfold regularizedRadialDerivative regularizedBlockNorm
  rw [Matrix.trace_add, Matrix.trace_mul_comm Z (A r),
    trace_square_eq_six_norm_sq _ (hs r)]
  ring_nf

theorem matrixPairing_self_norm (A : Mat) :
    matrixPairing A A = 6 * normalizedBlockNorm A ^ 2 := by
  rw [normalizedBlockNorm_sq]
  simp only [matrixPairing, pow_two]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pointwise spectral basis in the positive Weyl block lifts to an
orientation-preserving orthogonal change in four dimensions. The harmless
common sign in the three-dimensional basis cancels from matrix conjugation. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem frameMatrix_orthogonal (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    (frameMatrix φ)ᵀ * frameMatrix φ = 1 := by
  ext i j
  have h := φ.inner_map_map ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
    ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
  rw [EuclideanSpace.basisFun_inner] at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, frameMatrix_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, Matrix.one_apply, eq_comm] using h

/-- Each reflection used by Cartan--Dieudonné has a concrete quaternion
lift after multiplying its three-dimensional matrix by a common sign. -/
theorem reflection_has_signed_lift (v : ThreeSpace) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ Nonempty
      (QuaternionLift quaternionMatrix Angular.oppositeMatrix
        (c • frameMatrix (Submodule.reflection (ℝ ∙ v)ᗮ))) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨1, by norm_num, ?_⟩
    have htop : Submodule.reflection (⊤ : Submodule ℝ ThreeSpace) = 1 := by
      ext x : 1
      exact Submodule.reflection_mem_subspace_eq_self
        (K := (⊤ : Submodule ℝ ThreeSpace)) (show x ∈ (⊤ : Submodule ℝ ThreeSpace) by trivial)
    simpa only [Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top,
      htop, frameMatrix_one, one_smul] using
        (show Nonempty (QuaternionLift quaternionMatrix Angular.oppositeMatrix (1 : Mat)) from
          ⟨QuaternionLift.one _ _⟩)
  · let u : ThreeSpace := (‖v‖⁻¹ : ℝ) • v
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
    have hus : (ℝ ∙ u) = ℝ ∙ v := normalized_span v hv
    have huq : ∑ r, u r ^ 2 = 1 := by
      simpa only [hu, one_pow] using (EuclideanSpace.real_norm_sq_eq u).symm
    refine ⟨-1, by norm_num, ?_⟩
    have hf : frameMatrix (Submodule.reflection (ℝ ∙ v)ᗮ) = -axisReflection u := by
      simpa only [hus] using frameMatrix_orthogonalReflection u hu
    have hm : (-1 : ℝ) • frameMatrix (Submodule.reflection (ℝ ∙ v)ᗮ) =
        axisReflection u := by
      rw [hf, neg_one_smul, neg_neg]
    rw [hm]
    exact ⟨QuaternionLift.leftAxis u huq⟩

theorem reflection_list_has_signed_lift (l : List ThreeSpace) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ Nonempty
      (QuaternionLift quaternionMatrix Angular.oppositeMatrix
        (c • frameMatrix (l.map fun v => Submodule.reflection (ℝ ∙ v)ᗮ).prod)) := by
  induction l with
  | nil =>
      refine ⟨1, by norm_num, ?_⟩
      simpa only [List.map_nil, List.prod_nil, frameMatrix_one, one_smul] using
        (show Nonempty (QuaternionLift quaternionMatrix Angular.oppositeMatrix (1 : Mat)) from
          ⟨QuaternionLift.one _ _⟩)
  | cons v l ih =>
      obtain ⟨c, hc, ⟨P⟩⟩ := reflection_has_signed_lift v
      obtain ⟨d, hd, ⟨R⟩⟩ := ih
      refine ⟨c * d, by rw [mul_pow, hc, hd, one_mul], ?_⟩
      have h := P.mul R
      rw [signed_matrix_mul, ← frameMatrix_mul] at h
      simpa only [List.map_cons, List.prod_cons] using
        (show Nonempty _ from ⟨h⟩)

/-- Every orthogonal spectral basis admits the required oriented four-frame
lift. The common sign disappears from conjugation of the Weyl matrix. -/
theorem exists_signed_left_lift (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    ∃ c : ℝ, c ^ 2 = 1 ∧ Nonempty
      (QuaternionLift quaternionMatrix Angular.oppositeMatrix (c • frameMatrix φ)) := by
  obtain ⟨l, _, hφ⟩ := φ.reflections_generate_dim
  rw [hφ]
  exact reflection_list_has_signed_lift l

/-- A nonzero symmetric trace-free Weyl block has the paper's normalized
shape in an actual orthogonal eigenbasis. -/
theorem exists_spectral_shape (A : Mat) (hA : symmetric A) (ht : traceFree A)
    (hv : 0 < normalizedBlockNorm A) :
    ∃ φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace, ∃ S : Shape,
      (frameMatrix φ)ᵀ * A * frameMatrix φ =
        Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i) := by
  have hherm : A.IsHermitian := by
    ext i j
    exact hA j i
  let φ := (EuclideanSpace.basisFun (Fin 3) ℝ).equiv
    hherm.eigenvectorBasis (Equiv.refl (Fin 3))
  have hφ : frameMatrix φ = (hherm.eigenvectorUnitary : Mat) := by
    ext i j
    rw [frameMatrix_apply]
    simp only [φ, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
  have htrace : ∑ i, hherm.eigenvalues i = 0 := by
    have h := hherm.trace_eq_sum_eigenvalues
    calc
      _ = Matrix.trace A := by simpa using h.symm
      _ = 0 := ht
  have hsquare : ∑ i, hherm.eigenvalues i ^ 2 =
      6 * normalizedBlockNorm A ^ 2 := by
    rw [matrix_spectral_square A hherm, trace_square_eq_six_norm_sq A hA]
  let S : Shape := {
    s := fun i => hherm.eigenvalues i / normalizedBlockNorm A
    trace := by simp only [← Finset.sum_div, htrace, zero_div]
    square := by
      simp only [div_pow, ← Finset.sum_div, hsquare]
      field_simp [ne_of_gt hv]
  }
  refine ⟨φ, S, ?_⟩
  rw [hφ]
  have hd : (hherm.eigenvectorUnitary : Mat)ᵀ * A * hherm.eigenvectorUnitary =
      Matrix.diagonal hherm.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hherm.conjStarAlgAut_star_eigenvectorUnitary
  rw [hd]
  apply congrArg Matrix.diagonal
  funext i
  change hherm.eigenvalues i = normalizedBlockNorm A *
    (hherm.eigenvalues i / normalizedBlockNorm A)
  field_simp [ne_of_gt hv]

/-- The local spectral shape is realized by a genuine oriented
four-dimensional quaternion lift. The possible global sign on the
three-dimensional eigenbasis cancels from both matrix slots. -/
theorem exists_lifted_spectral_shape (A : Mat) (hA : symmetric A) (ht : traceFree A)
    (hv : 0 < normalizedBlockNorm A) :
    ∃ R : Mat, Rᵀ * R = 1 ∧
      Nonempty (QuaternionLift quaternionMatrix Angular.oppositeMatrix R) ∧
      ∃ S : Shape, Rᵀ * A * R =
        Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i) := by
  obtain ⟨φ, S, hS⟩ := exists_spectral_shape A hA ht hv
  obtain ⟨c, hc, hP⟩ := exists_signed_left_lift φ
  refine ⟨c • frameMatrix φ, ?_, hP, S, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← pow_two, hc, one_smul, frameMatrix_orthogonal]
  · rw [signed_conjugation c hc, hS]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The full trace Green term as invariant polynomial contractions.
This expression has no division by a Weyl norm and is valid at its zeros. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance traceScalarNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance traceScalarNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance traceScalarNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def weylGradientEnergy (Z : Fin 4 → Mat) : ℝ :=
  (∑ i, matrixPairing (Z i) (Z i)) / 6

def weylMatrixEnergy (A : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (∑ i, matrixPairing (matrixSlotAction A (Z i)) (Z i)) / 6

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary differentiation and compact bounds for the specific polynomial
multiplier of equation (15), with both Weyl norms varying. -/

namespace PositiveEinsteinFour.Geometry

open Potential Quadratic TraceHessian Filter
open scoped _root_.Topology

noncomputable section

local instance kappaNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance kappaNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance kappaNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def regularizedKappa (ε : ℝ) (A B : Mat) : ℝ :=
  kappa (regularizedBlockNorm ε A) (regularizedBlockNorm ε B)

def regularizedKappaDerivative (ε : ℝ) (A B Z V : Mat) : ℝ :=
  kappaV (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
    regularizedRadialDerivative ε A Z +
  kappaB (regularizedBlockNorm ε A) (regularizedBlockNorm ε B) *
    regularizedRadialDerivative ε B V

end
end PositiveEinsteinFour.Geometry
end


section

/-! Supply the smooth weights used by the metric Green identities from
the actual two Weyl blocks and their actual first covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameRegularizedWeight (g : SmoothMetric M) (ε : ℝ)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame)) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylWeight ε (plusWeyl g e.base e.frame)
    (minusWeyl g e.base e.frame), continuous_regularizedWeylWeight ε _ _ hT hU⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci equation and its identity and varying-matrix Green
contractions in the actual arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem gradientVector_pairing (Z W : Angular.Gradient) :
    inner ℝ (gradientVector Z) (gradientVector W) = ∑ i, matrixPairing (Z i) (W i) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    gradientVector, Fintype.sum_prod_type, matrixPairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem gradientTensor_pairing (Z W : Angular.Gradient)
    (hZ : ∀ i, symmetric (Z i)) (hW : ∀ i, symmetric (W i)) :
    rawPairing (gradientTensor Z).matrix (gradientTensor W).matrix =
      ∑ i, matrixPairing (Z i) (W i) := by
  rw [← inner_rawGradientVector]
  change inner ℝ (tensorGradientVector (gradientTensor Z))
    (tensorGradientVector (gradientTensor W)) = _
  rw [tensorGradientVector_gradientTensor Z hZ, tensorGradientVector_gradientTensor W hW,
    gradientVector_pairing]

local instance metricContractionNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricContractionNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricContractionNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The true Bianchi compression energy, before any spectral coordinates. -/
def weylCompressionEnergy (A : Mat) (Z : Angular.Gradient) : ℝ :=
  rawPairing (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix))
    (rawBianchiProjection (generalMatrixAction A (gradientTensor Z).matrix)) / 6

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth approximation of the scalar deficit δ=2-v-b used in the
energy Bochner identity. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian Filter
open scoped _root_.Topology

noncomputable section

local instance deficitNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance deficitNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance deficitNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def regularizedDeficit (ε : ℝ) (A B : Mat) : ℝ :=
  2 - regularizedBlockNorm ε A - regularizedBlockNorm ε B

def regularizedDeficitDerivative (ε : ℝ) (A B Z V : Mat) : ℝ :=
  -regularizedRadialDerivative ε A Z - regularizedRadialDerivative ε B V

end
end PositiveEinsteinFour.Geometry
end


section

/-! The original weighted-Hessian curvature form with complete Weyl matrices.
The contractions retain the full symmetric Weyl matrices. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

/-- The actual original curvature form, with the same contractions as the
four geometric Green identities. -/
def generalOriginalCurvatureForm (A U : Mat) (X : Hessian) : ℝ :=
  4 * hessianNormSq X -
    (5 / 6 : ℝ) * derivativePairing (generalCoefficient quaternionMatrix A) X X -
    (5 / 3 : ℝ) * matrixHessianPairing A X X -
    derivativePairing (generalCoefficient Angular.oppositeMatrix U) X X


end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Evaluate the derivative-slot Green integral on actual metric tensors,
using the published raw curvature decomposition and Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedSpace
local instance curvatureIntegralNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- The coefficient is a fixed bounded linear function of the Weyl block. -/
def generalCoefficientMap (Q : Fin 3 → Mat4) (i k j l : Fin 4) : Mat →L[ℝ] ℝ :=
  ({ toFun := fun A => generalCoefficient Q A i k j l
     map_add' A B := by
       simp only [generalCoefficient, Matrix.add_apply, add_mul,
         Finset.sum_add_distrib, mul_add]
     map_smul' c A := by
       simp only [generalCoefficient, Matrix.smul_apply, smul_eq_mul,
         mul_assoc, ← Finset.mul_sum, RingHom.id_apply]
       ring } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap

end
end PositiveEinsteinFour.Geometry
end


section

/-! Matrix conjugation and the derivative-index change used at a single
spectral frame. All maps act on the actual matrix arrays; no smooth choice
of eigenvectors is involved. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem conjugateMatrix_pairing (R : Mat) (hR : R * Rᵀ = 1) (A B : Mat) :
    matrixPairing (conjugateMatrix R A) (conjugateMatrix R B) = matrixPairing A B := by
  rw [matrixPairing_eq_trace, conjugateMatrix_transpose,
    conjugateMatrix_mul R hR, conjugateMatrix_trace R hR, matrixPairing_eq_trace]

theorem conjugateMatrix_norm (R : Mat) (hR : R * Rᵀ = 1) (A : Mat) :
    normalizedBlockNorm (conjugateMatrix R A) = normalizedBlockNorm A := by
  have hp := conjugateMatrix_pairing R hR A A
  have hs : normalizedBlockNorm (conjugateMatrix R A) ^ 2 =
      normalizedBlockNorm A ^ 2 := by
    rw [normalizedBlockNorm_sq, normalizedBlockNorm_sq]
    simpa only [matrixPairing, pow_two] using
      congrArg (fun x : ℝ => x / 6) hp
  nlinarith [normalizedBlockNorm_nonneg (conjugateMatrix R A),
    normalizedBlockNorm_nonneg A]

theorem matrixPairing_comm (A B : Mat) : matrixPairing A B = matrixPairing B A := by
  simp only [matrixPairing, mul_comm]

theorem matrixPairing_sum_smul_right {ι : Type*} [Fintype ι]
    (A : Mat) (c : ι → ℝ) (B : ι → Mat) :
    matrixPairing A (∑ i, c i • B i) = ∑ i, c i * matrixPairing A (B i) := by
  rw [matrixPairing_comm, CurvatureContraction.matrixPairing_sum_smul_left]
  simp only [matrixPairing_comm]

/-- Every quadratic contraction is preserved by simultaneous changes of
the matrix basis and the covector basis. -/
theorem turnGradient_pairing (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z W : Angular.Gradient) :
    (∑ i, matrixPairing (turnGradient R P Z i) (turnGradient R P W i)) =
      ∑ i, matrixPairing (Z i) (W i) := by
  simp only [turnGradient, CurvatureContraction.matrixPairing_sum_smul_left,
    matrixPairing_sum_smul_right, conjugateMatrix_pairing R hR, Finset.mul_sum]
  simp_rw [← mul_assoc]
  exact orthogonal_sum_contraction P hP _

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The finite four-by-four projection-cost kernel passes through the
smooth norm regularization, without any nonvanishing Weyl hypothesis. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

local instance matrixWeightNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance matrixWeightNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance matrixWeightNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def regularizedMatrixWeight (ε : ℝ) (A B : Mat) (Z V : Fin 4 → Mat)
    (K : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, (regularizedWeylWeightDerivative ε A B (Z i) (V i) *
    regularizedWeylWeightDerivative ε A B (Z j) (V j) / regularizedWeylWeight ε A B) * K i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Full-matrix generator compression on the actual Bianchi gradient space.
This is the ingredient for retaining unsymmetrized inner-Bianchi Hessians. -/


namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian CurvatureContraction PositiveEinsteinFour.Geometry

noncomputable section

/-- The two actual derivative slots, before taking a trace-free coefficient. -/
def generalDerivativeSlot (Q : Fin 3 → Mat4) (r s : Fin 3) (X : Hessian) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, Q r i k * Q s j l * matrixPairing (X k l) (X i j)

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Simultaneous dominated convergence for the scalar, cubic, and projection
terms of the weighted Hessian estimate. All derivative indices are the
four actual frame directions. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

local instance hessianWeightNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianWeightNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianWeightNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def regularizedHessianWeight (ε : ℝ) (A B : Mat) (Z V : Fin 4 → Mat)
    (F : ℝ) (G : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ) : ℝ :=
  regularizedWeylWeight ε A B * F +
    (∑ i, regularizedWeylWeightDerivative ε A B (Z i) (V i) * G i) +
    regularizedMatrixWeight ε A B Z V K

end
end PositiveEinsteinFour.Geometry
end


section

/-! The minimum of the constructed normalized spectrum gives exactly
the scalar parameter r in the closed spectral domain. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem shape_exists_minimum_parameter (S : Shape) :
    ∃ r : ℝ, 1 ≤ r ∧ r ≤ 2 ∧ S.sigma = (3 * r - r ^ 3) / 2 ∧
      (∀ i, -r ≤ S.s i) ∧ ∃ i, S.s i = -r := by
  obtain ⟨a, ha⟩ := Finite.exists_min S.s
  have ht := S.trace
  have hn := S.square
  simp only [Fin.sum_univ_three] at ht hn
  fin_cases a
  · obtain ⟨hr, hr2, _, hc⟩ := normalized_eigenvalue_parameter
      (-S.s 0) (S.s 1) (S.s 2) (by linarith only [ht])
      (by nlinarith only [hn]) (by simpa using ha 1) (by simpa using ha 2)
    refine ⟨-S.s 0, hr, hr2, ?_, ?_, 0, by ring⟩
    · unfold Shape.sigma
      simp only [Fin.sum_univ_three, neg_neg] at hc ⊢
      exact hc
    · intro i
      simpa using ha i
  · obtain ⟨hr, hr2, _, hc⟩ := normalized_eigenvalue_parameter
      (-S.s 1) (S.s 0) (S.s 2) (by linarith only [ht])
      (by nlinarith only [hn]) (by simpa using ha 0) (by simpa using ha 2)
    refine ⟨-S.s 1, hr, hr2, ?_, ?_, 1, by ring⟩
    · unfold Shape.sigma
      simp only [Fin.sum_univ_three, neg_neg] at hc ⊢
      linarith only [hc]
    · intro i
      simpa using ha i
  · obtain ⟨hr, hr2, _, hc⟩ := normalized_eigenvalue_parameter
      (-S.s 2) (S.s 0) (S.s 1) (by linarith only [ht])
      (by nlinarith only [hn]) (by simpa using ha 0) (by simpa using ha 1)
    refine ⟨-S.s 2, hr, hr2, ?_, ?_, 2, by ring⟩
    · unfold Shape.sigma
      simp only [Fin.sum_univ_three, neg_neg] at hc ⊢
      linarith only [hc]
    · intro i
      simpa using ha i

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem gradientTensor_energy (Z : Angular.Gradient) (hZ : ∀ i, symmetric (Z i)) :
    (gradientTensor Z).squaredNorm / 6 = weylGradientEnergy Z := by
  have h := gradientTensor_pairing Z Z hZ hZ
  rw [rawPairing_vectors] at h
  simp only [real_inner_self_eq_norm_sq] at h
  exact congrArg (fun x : ℝ => x / 6) h

theorem weylGradientEnergy_turn (R : Mat) (hR : R * Rᵀ = 1)
    (P : Mat4) (hP : P * Pᵀ = 1) (Z : Angular.Gradient) :
    weylGradientEnergy (turnGradient R P Z) = weylGradientEnergy Z := by
  unfold weylGradientEnergy
  rw [turnGradient_pairing R hR P hP]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The small classical smooth-bundle input needed to use scalar Poisson
solutions on one oriented frame component. Smoothness of the squared norm
and invariance under oriented orthonormal frames are the ordinary metric
bundle calculus of Petersen §2.2 and §3.1.1. The scalar gradient identities
below are derived from parallel differentiation; no variance estimate is
included in the input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def orientedNormRegularization (b : M → ℝ) (ε : ℝ) (c : M) : ℝ :=
  Real.sqrt (b c ^ 2 + ε ^ 2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariance of the quaternionic Bianchi constraint under a genuine
oriented four-frame lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- The passive vector change intertwines each imaginary quaternion
with its rotated linear combination. -/
theorem QuaternionLift.quaternion_turnVector {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (s : Fin 3) (v : Vec) :
    quaternion s (turnVector P.matrix v) =
      turnVector P.matrix (∑ r, R r s • quaternion r v) := by
  have hp : quaternionMatrix s * P.matrixᵀ =
      P.matrixᵀ * (∑ r, R r s • quaternionMatrix r) := by
    calc
      _ = (P.matrixᵀ * P.matrix) * (quaternionMatrix s * P.matrixᵀ) := by
        rw [P.orthogonal, Matrix.one_mul]
      _ = P.matrixᵀ * (P.matrix * quaternionMatrix s) * P.matrixᵀ := by
        simp only [Matrix.mul_assoc]
      _ = P.matrixᵀ * ((∑ r, R r s • quaternionMatrix r) * P.matrix) * P.matrixᵀ := by
        rw [P.intertwines]
      _ = P.matrixᵀ * (∑ r, R r s • quaternionMatrix r) *
          (P.matrix * P.matrixᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [P.mul_transpose, Matrix.mul_one]
  have hsum : (∑ r, R r s • quaternionMatrix r) *ᵥ (v : Fin 4 → ℝ) =
      ((∑ r, R r s • quaternion r v : Vec) : Fin 4 → ℝ) := by
    ext j
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
      Pi.smul_apply, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [← quaternionMatrix_apply]
    rfl
  ext i
  calc
    _ = (quaternionMatrix s *ᵥ (P.matrixᵀ *ᵥ (v : Fin 4 → ℝ))) i := by
      rw [← quaternionMatrix_apply]
      rfl
    _ = ((quaternionMatrix s * P.matrixᵀ) *ᵥ (v : Fin 4 → ℝ)) i := by
      rw [Matrix.mulVec_mulVec]
    _ = ((P.matrixᵀ * (∑ r, R r s • quaternionMatrix r)) *ᵥ (v : Fin 4 → ℝ)) i := by rw [hp]
    _ = _ := by rw [← Matrix.mulVec_mulVec, hsum]; rfl

/-- Orthogonality contracts the changed quaternion row against the
changed matrix row. -/
theorem QuaternionLift.quaternion_row_contraction {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (hR : R * Rᵀ = 1) (r : Fin 3) (v : Vec) :
    (∑ a, R r a • quaternion a (turnVector P.matrix v)) =
      turnVector P.matrix (quaternion r v) := by
  have hr (t : Fin 3) : (∑ a, R r a * R t a) = if r = t then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun N : Mat => N r t) hR
  simp_rw [P.quaternion_turnVector, ← turnVector_smul]
  rw [← turnVector_sum]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hr, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

/-- The Bianchi constraint itself is preserved by a lifted change of
frame. This is a finite contraction of the quaternion intertwining law. -/
theorem turnRawGradient_bianchi (R : Mat) (hR : R * Rᵀ = 1)
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (Z : RawGradient) (hZ : ∀ s, ∑ r, quaternion r (Z r s) = 0) (b : Fin 3) :
    (∑ a, quaternion a (turnRawGradient R P.matrix Z a b)) = 0 := by
  have hq (a : Fin 3) : quaternion a (turnRawGradient R P.matrix Z a b) =
      ∑ r, ∑ s, (R r a * R s b) • quaternion a (turnVector P.matrix (Z r s)) := by
    simp only [turnRawGradient, turnVector_sum, turnVector_smul]
    simp only [quaternion_smul, Fin.sum_univ_three, quaternion_add]
  rw [show (∑ a, quaternion a (turnRawGradient R P.matrix Z a b)) =
      ∑ a, ∑ r, ∑ s, R s b • (R r a • quaternion a (turnVector P.matrix (Z r s))) by
    simp only [hq, smul_smul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_comm]]
  calc
    _ = ∑ r, ∑ s, R s b •
        (∑ a, R r a • quaternion a (turnVector P.matrix (Z r s))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.smul_sum]
    _ = ∑ r, ∑ s, R s b • turnVector P.matrix (quaternion r (Z r s)) := by
      simp_rw [P.quaternion_row_contraction hR]
    _ = ∑ s, R s b • turnVector P.matrix (∑ r, quaternion r (Z r s)) := by
      rw [Finset.sum_comm]
      simp only [turnVector_sum, Finset.smul_sum]
    _ = 0 := by simp only [hZ, turnVector_zero, smul_zero, Finset.sum_const_zero]

theorem turnGradient_bianchi (R : Mat) (hR : R * Rᵀ = 1)
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R)
    (Z : Angular.Gradient) (hZ : ∀ r i, gradientDivergence Z r i = 0) :
    ∀ r i, gradientDivergence (turnGradient R P.matrix Z) r i = 0 := by
  have hz (s : Fin 3) :
      (∑ r, quaternion r (WithLp.toLp 2 (fun i => Z i r s))) = 0 := by
    ext i
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply]
    simpa only [← quaternionMatrix_apply, gradientDivergence] using hZ s i
  intro r i
  have h := congrArg (fun v : Vec => v i)
    (turnRawGradient_bianchi R hR P
      (fun a b => WithLp.toLp 2 (fun j => Z j a b)) hz r)
  simp only [turnRawGradient_field, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.zero_apply] at h
  simpa only [← quaternionMatrix_apply, gradientDivergence] using h

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section


/-- The polarized arbitrary-matrix curvature operator. -/
def generalCurvaturePairing (A U : Mat) (X Y : Hessian) : ℝ :=
  4 * hessianPairing X Y +
    (∑ r, ∑ s, A r s * hessianPairing (totalPlus r X) (totalPlus s Y)) / 24 +
    (∑ r, ∑ s, U r s * hessianPairing (totalMinus r X) (totalMinus s Y)) / 4

def generalTraceCurvatureBlock (A M : Mat) : Mat :=
  (4 : ℝ) • M - matrixSlotAction A M

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The elementary Grassmannian calculation needed for the sectional
criterion. Two arbitrary unit coefficient vectors in the positive and
negative quaternion triples are realized by a genuine two-plane. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

theorem quaternion_gram (v : Vec4) (i j : Fin 3) :
    inner ℝ (act (quaternionMatrix i) v) (act (quaternionMatrix j) v) =
      if i = j then ‖v‖ ^ 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [act, quaternionMatrix, PiLp.inner_apply, RCLike.inner_apply,
      EuclideanSpace.real_norm_sq_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem opposite_gram (v : Vec4) (i j : Fin 3) :
    inner ℝ (act (oppositeMatrix i) v) (act (oppositeMatrix j) v) =
      if i = j then ‖v‖ ^ 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [act, oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.real_norm_sq_eq,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

end
end PositiveEinsteinFour.SectionalPlane
end


section

/-! The arbitrary-frame weighted Hessian square in the original Green form. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

def generalTraceCorrection (A U M : Mat) (m : ℝ) (L : Hessian) : ℝ :=
  -(m * generalCurvaturePairing A U (traceComponent M) (traceComponent M) +
    generalCurvaturePairing A U (traceComponent M) L) / 6

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! The sharp opposite-block cost for an arbitrary symmetric coefficient
matrix.  A concrete orthogonal quaternion expansion of the two derivative
slots replaces a second choice of eigenframe. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- Only the three imaginary right-quaternion coefficients enter the
opposite-block action. -/
def rightVectorEnergy (X : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ t : Fin 4, ∑ r : Fin 3,
    rightQuaternionCoefficients (fun i j => X i j a b) t r.succ ^ 2

end
end PositiveEinsteinFour.HighestHessian
end


section

/-! Apply the arbitrary-matrix highest-square inequality to the actual
metric Hessian and its exact trace. No eigenframe is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Pointwise shifted-matrix positivity is the elementary sectional
condition consumed by the local tensor estimate. Its geometric derivation
from the curvature decomposition is separate from the weighted estimate. -/
def ShiftedCurvaturePositive (g : SmoothMetric M) : Prop :=
  ∀ e : FrameBundle g, ∃ x y : ℝ,
    (plusWeyl g e.base e.frame + x • (1 : Mat)).PosSemidef ∧
    (minusWeyl g e.base e.frame + y • (1 : Mat)).PosSemidef ∧ x + y ≤ 2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the actual weighted-Hessian integrands. The orthogonal
projection is the already constructed projection, not a chosen eigenframe. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance hessianContinuityNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianContinuityNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianContinuityNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def hessianVectorMap : Hessian →L[ℝ] HessianSpace :=
  ({ toFun := hessianVector
     map_add' := fun X Y => by ext p; rfl
     map_smul' := fun r X => by ext p; rfl } : Hessian →ₗ[ℝ] HessianSpace).toContinuousLinearMap

def vectorHessianMap : HessianSpace →L[ℝ] Hessian :=
  ({ toFun := vectorHessian
     map_add' := fun X Y => by ext i j a b; rfl
     map_smul' := fun r X => by ext i j a b; rfl } : HessianSpace →ₗ[ℝ] Hessian).toContinuousLinearMap

theorem continuous_highestProjection : Continuous highestProjection :=
  vectorHessianMap.continuous.comp
    (highestSubspace.starProjection.continuous.comp hessianVectorMap.continuous)

section Continuous

variable {Ω : Type*} [TopologicalSpace Ω]

local instance hessianContinuityNormedRing_re98581_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianContinuityNormedSpace_re98581_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianContinuityNormedAlgebra_re98581_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuous_hessianPairing {X Y : Ω → Hessian}
    (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => hessianPairing (X x) (Y x)) := by
  simp only [← hessianVector_inner]
  exact (hessianVectorMap.continuous.comp hX).inner
    (hessianVectorMap.continuous.comp hY)

theorem continuous_derivativePairing {A : Ω → DerivativeCoefficient} {X Y : Ω → Hessian}
    (hA : Continuous A) (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => HighestHessian.derivativePairing (A x) (X x) (Y x)) := by
  simp only [HighestHessian.derivativePairing, matrixPairing]
  fun_prop

theorem continuous_matrixHessianPairing {A : Ω → Mat} {X Y : Ω → Hessian}
    (hA : Continuous A) (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => matrixHessianPairing (A x) (X x) (Y x)) := by
  unfold matrixHessianPairing
  apply continuous_finsetSum
  intro i _
  exact (gradientVectorMap.continuous.comp ((continuous_apply i).comp hX)).inner
    ((matrixSlot.continuous.comp hA).clm_apply
      (gradientVectorMap.continuous.comp ((continuous_apply i).comp hY)))

theorem continuous_weightedQuadratic {q : Ω → Hessian → ℝ}
    (hq : ∀ W : Ω → Hessian, Continuous W → Continuous (fun x => q x (W x)))
    {m : Ω → ℝ} {X L : Ω → Hessian}
    (hm : Continuous m) (hX : Continuous X) (hL : Continuous L) :
    Continuous (fun x => weightedQuadratic (q x) (m x) (X x) (L x)) := by
  exact ((hm.mul (hq X hX)).add
    ((((hq (X + L) (hX.add hL)).sub (hq X hX)).sub (hq L hL)).div_const 2)).div_const 6

theorem continuous_weylGradientEnergy {Z : Ω → Fin 4 → Mat} (hZ : Continuous Z) :
    Continuous (fun x => weylGradientEnergy (Z x)) := by
  simp only [weylGradientEnergy, matrixPairing]
  fun_prop

theorem continuous_matrixSlotAction {A Z : Ω → Mat}
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => matrixSlotAction (A x) (Z x)) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a = b
  · simp only [matrixSlotAction, hab, ite_true, if_true]
    fun_prop
  · simp only [matrixSlotAction, hab, ite_false, if_false]
    fun_prop

theorem continuous_weylMatrixEnergy {A : Ω → Mat} {Z : Ω → Fin 4 → Mat}
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => weylMatrixEnergy (A x) (Z x)) := by
  have h (i : Fin 4) := continuous_matrixSlotAction hA ((continuous_apply i).comp hZ)
  simp only [weylMatrixEnergy, matrixPairing]
  fun_prop

theorem rawBianchiProjection_coordinates (Z : RawGradient) (p : GradientIndex) :
    rawCoordinates (rawBianchiProjection Z) p = (1 / 10 : ℝ) *
      (6 * rawCoordinates Z p - ∑ q, gradientCouplingKernel p q * rawCoordinates Z q) := by
  change (1 / 10 : ℝ) * (6 * rawCoordinates Z p - rawCoordinates (rawCoupling Z) p) = _
  rw [rawCoupling_coordinates]

theorem continuous_weylCompressionEnergy {A : Ω → Mat} {Z : Ω → Fin 4 → Mat}
    (hA : Continuous A) (hZ : Continuous Z) (hs : ∀ x i, symmetric (Z x i)) :
    Continuous (fun x => weylCompressionEnergy (A x) (Z x)) := by
  have hg (p : GradientIndex) : Continuous (fun x =>
      rawCoordinates (generalMatrixAction (A x) (gradientTensor (Z x)).matrix) p) := by
    change Continuous (fun x => matrixSlotAction (A x)
      (fun a b => (gradientTensor (Z x)).matrix a b p.1) p.2.1 p.2.2)
    simp_rw [gradientTensor_matrix _ (hs _)]
    exact (continuous_apply p.2.2).comp ((continuous_apply p.2.1).comp
      (continuous_matrixSlotAction hA ((continuous_apply p.1).comp hZ)))
  unfold weylCompressionEnergy rawPairing
  simp_rw [rawBianchiProjection_coordinates]
  fun_prop

theorem continuous_generalCurvaturePairing {A U : Ω → Mat} {X Y : Ω → Hessian}
    (hA : Continuous A) (hU : Continuous U) (hX : Continuous X) (hY : Continuous Y) :
    Continuous (fun x => generalCurvaturePairing (A x) (U x) (X x) (Y x)) := by
  have hplus (s : Fin 3) {F : Ω → Hessian} (hF : Continuous F) :
      Continuous (fun x => totalPlus s (F x)) := by
    change Continuous (fun x i j a b =>
      (∑ c, (rotation s a c * F x i j c b - F x i j a c * rotation s c b)) +
        (∑ k, quaternionMatrix s i k * F x k j a b) +
        ∑ k, quaternionMatrix s j k * F x i k a b)
    fun_prop
  have hminus (s : Fin 3) {F : Ω → Hessian} (hF : Continuous F) :
      Continuous (fun x => totalMinus s (F x)) := by
    change Continuous (fun x i j a b =>
      (∑ k, rightQuaternion s i k * F x k j a b) +
        ∑ k, rightQuaternion s j k * F x i k a b)
    fun_prop
  unfold generalCurvaturePairing
  exact ((continuous_const.mul (continuous_hessianPairing hX hY)).add
    ((continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp ((continuous_apply r).comp hA)).mul
        (continuous_hessianPairing (hplus r hX) (hplus s hY))).div_const 24)).add
    ((continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp ((continuous_apply r).comp hU)).mul
        (continuous_hessianPairing (hminus r hX) (hminus s hY))).div_const 4)

end Continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The nine commuting-quaternion products are an actual orthogonal
basis for symmetric trace-free scalar Hessians in four dimensions. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

def scalarPairing (S T : Matrix4) : ℝ := ∑ a, ∑ b, S a b * T a b

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar norm bounds forced by shifted positive semidefiniteness. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- A trace-free block bounded below by `-x` has normalized norm at most
`x`; the zero block is included. -/
theorem normalizedBlockNorm_le_shift (A : Mat) (hs : symmetric A) (ht : traceFree A)
    (x : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef) :
    normalizedBlockNorm A ≤ x := by
  by_cases hv : normalizedBlockNorm A = 0
  · rw [hv]
    exact shift_nonneg_of_traceFree A ht x hAx
  have hvp : 0 < normalizedBlockNorm A :=
    lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)
  obtain ⟨R, hR, _, S, hS⟩ := exists_lifted_spectral_shape A hs ht hvp
  obtain ⟨r, hr, _, _, _, hmin⟩ := shape_exists_minimum_parameter S
  have hbound := shape_minimum_parameter_bound A R hR S (normalizedBlockNorm A) x r hS hAx hmin
  have hprod : 0 ≤ normalizedBlockNorm A * (r - 1) :=
    mul_nonneg hvp.le (sub_nonneg.mpr hr)
  nlinarith only [hbound, hprod]

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! All five Green integrals for the actual Weyl Hessian. The result has
only first derivatives and the constructed orthogonal-projection cost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance hessianAssemblyNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def invariantHessianForm (A U : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (-42 - 3 * normalizedBlockNorm U ^ 2 - (10 / 3 : ℝ) * normalizedBlockNorm A ^ 2) *
      weylGradientEnergy Z +
    75 * weylMatrixEnergy A Z + (25 / 3 : ℝ) * weylMatrixEnergy (traceFreeSquare A) Z -
    (100 / 3 : ℝ) * weylCompressionEnergy A Z + 5 * weylRadialSquare A Z

section Continuous

variable {Ω : Type*} [TopologicalSpace Ω]

local instance hessianAssemblyNormedRing_re98581_2 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace_re98581_2 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra_re98581_2 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuous_generalCoefficient (Q : Fin 3 → Mat4) {A : Ω → Mat}
    (hA : Continuous A) : Continuous (fun x => generalCoefficient Q (A x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  apply continuous_pi
  intro l
  exact (generalCoefficientMap Q i k j l).continuous.comp hA

theorem continuous_traceComponent : Continuous traceComponent := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hij : i = j
  · simp only [traceComponent, traceLift, matrixAction, Matrix.smul_apply, smul_eq_mul,
      hij, ite_true, if_true]
    fun_prop
  · simp only [traceComponent, traceLift, matrixAction, Matrix.smul_apply, smul_eq_mul,
      hij, ite_false, if_false]
    fun_prop

end Continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projection cost is a four-by-four quadratic form in the
weight derivative. This finite expansion is used for its integral limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def highestProjectionMap : Hessian →L[ℝ] Hessian :=
  vectorHessianMap.comp (highestSubspace.starProjection.comp hessianVectorMap)

def projectedWeightKernel (A U : Mat) (Z : Tensor) (i j : Fin 4) : ℝ :=
  generalCurvaturePairing A U
    (highestProjection (weightTensor (derivativeBasis i) Z))
    (highestProjection (weightTensor (derivativeBasis j) Z)) / 24

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial first derivative and its exact contribution to the
invariant Hessian expression. Division by a zero Weyl norm is harmless. -/

namespace PositiveEinsteinFour.Geometry

open TraceHessian HighestHessian
open scoped BigOperators

noncomputable section

def blockRadialGradient (A : Mat) (Z : Fin 4 → Mat) : Bianchi.Vec :=
  WithLp.toLp 2 (fun i => regularizedRadialDerivative 0 A (Z i))

theorem trace_eq_norm_mul_radial (A Z : Mat) :
    Matrix.trace (A * Z) = 6 * normalizedBlockNorm A * regularizedRadialDerivative 0 A Z := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hA := (normalizedBlockNorm_eq_zero_iff A).mp hv
    simp [hA, regularizedRadialDerivative]
  · unfold regularizedRadialDerivative
    rw [regularizedBlockNorm_zero]
    field_simp [hv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sectional criterion from actual two-planes. The quaternionic
Grassmann calculation and the minimum-eigenvalue argument connect sectional
positivity with the Riemann curvature decomposition and symmetry identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem sectionalValue_frame (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (u v : FourSpace) :
    sectionalValue (frameCurvature g c e) u v =
      sectionalNumerator g c (chartAt FourSpace c c) (e.map u) (e.map v) := by
  let C : Mat4 := fun i j => if j = 0 then u i else v i
  have heq : (fun s : Fin 4 => ∑ a, C a (![0, 1, 1, 0] s) • e.vector a) =
      ![e.map u, e.map v, e.map v, e.map u] := by
    funext s
    fin_cases s
    · change (∑ a, u a • e.vector a) = e.map u
      exact (e.map_eq_combination u).symm
    · change (∑ a, v a • e.vector a) = e.map v
      exact (e.map_eq_combination v).symm
    · change (∑ a, v a • e.vector a) = e.map v
      exact (e.map_eq_combination v).symm
    · change (∑ a, u a • e.vector a) = e.map u
      exact (e.map_eq_combination u).symm
  have hh := multilinear_combinations (curvatureForm g c) C e.vector ![0, 1, 1, 0]
  rw [heq] at hh
  change sectionalNumerator g c (chartAt FourSpace c c) (e.map u) (e.map v) = _ at hh
  rw [hh]
  change (∑ a, ∑ b, ∑ p, ∑ r,
      frameCurvature g c e a b p r * u a * v b * v p * u r) =
    ∑ a, ∑ b, ∑ p, ∑ r,
      (u a * v b * v p * u r) * frameCurvature g c e a b p r
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The refined Kato bound in an arbitrary orthonormal frame, including
the zero Weyl block. The pointwise spectral frame is constructed, and the
Bianchi condition is transported by its actual quaternion lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem blockRadialGradient_turn (R : Mat) (hR : R * Rᵀ = 1) (P : Mat4)
    (A : Mat) (Z : Angular.Gradient) :
    blockRadialGradient (conjugateMatrix R A) (turnGradient R P Z) =
      turnVector P (blockRadialGradient A Z) := by
  ext i
  simp only [blockRadialGradient, regularizedRadialDerivative, regularizedBlockNorm_zero,
    conjugateMatrix_norm R hR, trace_turnGradient R hR, turnVector,
    Matrix.mulVec, Matrix.transpose_apply, dotProduct, Finset.sum_div, mul_div_assoc]

theorem blockRadialGradient_diagonal (S : Shape) (v : ℝ)
    (Z : Angular.Gradient) :
    blockRadialGradient (Matrix.diagonal (fun a => v * S.s a)) Z =
      (v / normalizedBlockNorm (Matrix.diagonal (fun a => v * S.s a))) •
        radialCoordinate S (gradientTensor Z) := by
  ext i
  simp only [blockRadialGradient, regularizedRadialDerivative, regularizedBlockNorm_zero,
    Matrix.trace, Matrix.diagonal_mul, Matrix.diag_apply, radialCoordinate,
    gradientTensor, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Identify the scalar-Hessian matrix operator with the actual
four-index curvature coefficient used in integration by parts. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular CurvatureContraction

noncomputable section

/-- The row of the four-index operator is `(i,j)` and the column `(k,l)`. -/
def blockQuadratic (Q : Fin 3 → Matrix4) (A : Mat) (S : Matrix4) : ℝ :=
  ∑ i, ∑ k, ∑ j, ∑ l, generalCoefficient Q A i k j l * S i j * S k l

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The regularized scalar Weyl equation follows from ordinary derivatives
of the actual block and its proved matrix Laplacian. Test functions are
arbitrary smooth flow weights, ready for the polynomial coupling test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedRing
local instance normEquationNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedAlgebra
def regularizedRadialSecond (ε : ℝ) (A Z X : Mat) : ℝ :=
  (Matrix.trace (Z * Z + A * X) / 6 - regularizedRadialDerivative ε A Z ^ 2) /
    regularizedBlockNorm ε A

theorem hasDerivAt_regularizedRadialDerivative
    {A Z : ℝ → Mat} {X : Mat} {t ε : ℝ}
    (hA : HasDerivAt A (Z t) t) (hZ : HasDerivAt Z X t)
    (hs : ∀ s, TraceHessian.symmetric (A s)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedRadialDerivative ε (A s) (Z s))
      (regularizedRadialSecond ε (A t) (Z t) X) t := by
  have hn := regularizedBlockNorm_pos ε hε (A t)
  have hd := ((hasDerivAt_matrixTrace (hA.mul hZ)).div_const 6).div
    (hasDerivAt_regularizedBlockNorm hA hs hε) (ne_of_gt hn)
  convert! hd using 1
  · funext s
    change regularizedRadialDerivative ε (A s) (Z s) =
      Matrix.trace (A s * Z s) / 6 / regularizedBlockNorm ε (A s)
    unfold regularizedRadialDerivative
    ring
  · unfold regularizedRadialSecond regularizedRadialDerivative
    change _ = (Matrix.trace (Z t * Z t + A t * X) / 6 * regularizedBlockNorm ε (A t) -
      Matrix.trace (A t * Z t) / 6 *
        (Matrix.trace (A t * Z t) / (6 * regularizedBlockNorm ε (A t)))) /
      regularizedBlockNorm ε (A t) ^ 2
    field_simp [ne_of_gt hn]

theorem continuous_regularizedRadialSecond {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z X : Ω → Mat)
    (hA : Continuous A) (hZ : Continuous Z) (hX : Continuous X) :
    Continuous (fun x => regularizedRadialSecond ε (A x) (Z x) (X x)) := by
  exact (((matrixTraceMap.continuous.comp ((hZ.mul hZ).add (hA.mul hX))).div_const 6).sub
    ((continuous_regularizedRadialDerivative ε hε A Z hA hZ).pow 2)).div
      ((continuous_regularizedBlockNorm ε).comp hA)
      (fun x => ne_of_gt (regularizedBlockNorm_pos ε hε (A x)))

theorem regularizedRadialSecond_sum (ε : ℝ) (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hZ : ∀ i, TraceHessian.symmetric (Z i)) (hX : hessianTrace X = weylLaplacian A) :
    (∑ i, regularizedRadialSecond ε A (Z i) (X i i)) =
      (weylGradientEnergy Z + Matrix.trace (A * weylLaplacian A) / 6 -
        (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2)) / regularizedBlockNorm ε A := by
  have hs (i : Fin 4) : Matrix.trace (Z i * Z i) = matrixPairing (Z i) (Z i) := by
    rw [matrixPairing_eq_trace]
    congr 2
    ext a b
    exact hZ i a b
  have hx : (∑ i, Matrix.trace (A * X i i)) = Matrix.trace (A * weylLaplacian A) := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum]
    exact congrArg (fun Q => Matrix.trace (A * Q)) hX
  unfold regularizedRadialSecond
  rw [← Finset.sum_div]
  congr 1
  simp only [Matrix.trace_add, add_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div, hs, hx, weylGradientEnergy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reflection of one axis in the actual orthonormal frame. It exchanges
the two Weyl blocks, with one sign for each covariant derivative slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Matrix Bundle
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameReflection_involutive (g : SmoothMetric M) :
    Function.Involutive (frameReflection : FrameBundle g → FrameBundle g) := by
  rintro ⟨c, e⟩
  change (⟨c, e.reflect.reflect⟩ : FrameBundle g) = ⟨c, e⟩
  rw [e.reflect_reflect]

theorem minusWeyl_reflect (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) :
    minusWeyl g c e.reflect = plusWeyl g c e := by
  rw [← plusWeyl_reflect, e.reflect_reflect]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability at a zero Weyl norm is obtained from uniformly bounded
regularized energies and Fatou's lemma. No integrability of the singular
quotient is assumed in the limiting argument. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

theorem regularizedRadialDerivative_factor (ε : ℝ) (A Z : Mat) :
    regularizedRadialDerivative ε A Z =
      (normalizedBlockNorm A / regularizedBlockNorm ε A) * regularizedRadialDerivative 0 A Z := by
  change Matrix.trace (A * Z) / (6 * regularizedBlockNorm ε A) = _
  rw [trace_eq_norm_mul_radial A Z]
  ring

theorem regularized_radial_energy_le (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) :
    (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) ≤ ‖blockRadialGradient A Z‖ ^ 2 := by
  let r := normalizedBlockNorm A / regularizedBlockNorm ε A
  have hr0 : 0 ≤ r := div_nonneg (normalizedBlockNorm_nonneg A)
    (regularizedBlockNorm_pos ε hε A).le
  have hr1 : r ≤ 1 := (div_le_one (regularizedBlockNorm_pos ε hε A)).mpr
    (norm_le_regularizedBlockNorm ε A)
  have hrsq : r ^ 2 ≤ 1 := by nlinarith
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) ≤
    ∑ i, regularizedRadialDerivative 0 A (Z i) ^ 2
  apply Finset.sum_le_sum
  intro i _
  rw [regularizedRadialDerivative_factor ε A (Z i), mul_pow]
  exact (mul_le_mul_of_nonneg_right hrsq (sq_nonneg _)).trans_eq (one_mul _)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The scalar Weyl equation at zero regularization. Its singular energy
term is controlled by the proved integrable energy quotient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

def scalarNormExpression (ε : ℝ) (A : Mat) (Z : Fin 4 → Mat) : ℝ :=
  (weylGradientEnergy Z - ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) /
    regularizedBlockNorm ε A + regularizedRadialDerivative ε A (weylLaplacian A)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the proved scalar variance theorem to smooth regularizations of
actual oriented Weyl norms. All equalities with frame derivatives are
proved from the raw parallel calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
  {g : SmoothMetric M}
  {μ : Measure (FrameBundle g)}

def scalarVarianceWeight (g : SmoothMetric M) (e : FrameBundle g) : ℝ :=
  4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
    normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar shape in the integrated Weyl equation is determined by
the actual determinant and norm, including at a zero Weyl block. Its
upper bound follows from the three-dimensional spectral identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

def normalizedDeterminantShape (A : Mat3) : ℝ :=
  A.det / (2 * normalizedBlockNorm A ^ 3)

theorem shape_product (S : Shape) : (∏ i, S.s i) = 2 * S.sigma := by
  simp only [Fin.prod_univ_three, Shape.sigma, Fin.sum_univ_three]
  rw [S.trace_coordinates]
  ring

theorem determinant_shape (A R : Mat3) (hR : Rᵀ * R = 1)
    (S : Shape)
    (hd : Rᵀ * A * R = Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) :
    A.det = 2 * normalizedBlockNorm A ^ 3 * S.sigma := by
  rw [← orthogonal_conjugate_det A R hR, hd, Matrix.det_diagonal]
  calc
    _ = normalizedBlockNorm A ^ 3 * ∏ i, S.s i := by
      simp only [Fin.prod_univ_three]
      ring
    _ = _ := by rw [shape_product]; ring

theorem normalizedDeterminantShape_mul (A : Mat3) :
    A.det = 2 * normalizedDeterminantShape A * normalizedBlockNorm A ^ 3 := by
  by_cases h : normalizedBlockNorm A = 0
  · have hA := (normalizedBlockNorm_eq_zero_iff A).mp h
    simp [hA, normalizedDeterminantShape]
  · unfold normalizedDeterminantShape
    field_simp [h]

theorem normalizedDeterminantShape_le_one (A : Mat3)
    (hs : symmetric A) (ht : traceFree A) : normalizedDeterminantShape A ≤ 1 := by
  by_cases h : normalizedBlockNorm A = 0
  · simp [normalizedDeterminantShape, h]
  · have hp : 0 < normalizedBlockNorm A :=
      lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm h)
    obtain ⟨R, hR, _, S, hS⟩ := exists_lifted_spectral_shape A hs ht hp
    have hd := determinant_shape A R hR S hS
    have he : normalizedDeterminantShape A = S.sigma := by
      unfold normalizedDeterminantShape
      rw [hd]
      field_simp [h]
    rw [he]
    nlinarith only [S.sigma_rho_circle, sq_nonneg S.rho]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contract the actual Weyl equation with the Weyl tensor. The cubic
trace is its determinant, so the result uses the canonical shape even
where the Weyl block is zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem weylLaplacian_pairing (A : Mat3) (hs : symmetric A) (ht : traceFree A) :
    matrixPairing A (weylLaplacian A) =
      36 * (normalizedBlockNorm A ^ 2 -
        normalizedDeterminantShape A * normalizedBlockNorm A ^ 3) := by
  have hsym : (weylLaplacian A)ᵀ = weylLaplacian A := by
    ext i j
    exact weylLaplacian_symmetric A hs j i
  have htr : Matrix.trace A = 0 := ht
  rw [matrixPairing_eq_trace, hsym]
  simp only [weylLaplacian, traceFreeSquare, mul_smul_comm, Matrix.mul_sub,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.mul_one, htr, smul_eq_mul,
    mul_zero, sub_zero, trace_square_eq_six_norm_sq A hs,
    traceCube_eq_three_det A hs ht, normalizedDeterminantShape_mul A]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cube root of the positive regularized Weyl norm satisfies the
scalar differential inequality forced by the Weyl equation and refined Kato. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance rootKatoNormedRing_re98581_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance rootKatoNormedSpace_re98581_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance rootKatoNormedAlgebra_re98581_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def regularizedWeylRoot (ε : ℝ) (A : Mat) : ℝ :=
  regularizedBlockNorm ε A ^ (1 / 3 : ℝ)

def regularizedWeylRootFirst (ε : ℝ) (A Z : Mat) : ℝ :=
  (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-2 / 3 : ℝ) *
    regularizedRadialDerivative ε A Z

def regularizedWeylRootSecond (ε : ℝ) (A Z X : Mat) : ℝ :=
  (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-2 / 3 : ℝ) *
      regularizedRadialSecond ε A Z X -
    (2 / 9 : ℝ) * regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) *
      regularizedRadialDerivative ε A Z ^ 2

theorem regularizedWeylRoot_eq (ε : ℝ) (A : Mat) :
    regularizedWeylRoot ε A =
      (normalizedBlockNorm A ^ 2 + ε ^ 2) ^ (1 / 6 : ℝ) := by
  unfold regularizedWeylRoot regularizedBlockNorm
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

theorem hasDerivAt_regularizedWeylRoot
    {A : ℝ → Mat} {Z : Mat} {t ε : ℝ}
    (hA : HasDerivAt A Z t) (hs : ∀ s, symmetric (A s)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedWeylRoot ε (A s))
      (regularizedWeylRootFirst ε (A t) Z) t := by
  have h := (hasDerivAt_regularizedBlockNorm hA hs hε).rpow_const
    (p := (1 / 3 : ℝ)) (Or.inl (regularizedBlockNorm_pos ε hε (A t)).ne')
  change HasDerivAt (fun s => regularizedWeylRoot ε (A s)) _ t at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold regularizedWeylRootFirst
  norm_num
  ring

theorem hasDerivAt_regularizedWeylRootFirst
    {A Z : ℝ → Mat} {X : Mat} {t ε : ℝ}
    (hA : HasDerivAt A (Z t) t) (hZ : HasDerivAt Z X t)
    (hs : ∀ s, symmetric (A s)) (hε : 0 < ε) :
    HasDerivAt (fun s => regularizedWeylRootFirst ε (A s) (Z s))
      (regularizedWeylRootSecond ε (A t) (Z t) X) t := by
  have hu := hasDerivAt_regularizedBlockNorm hA hs hε
  have hp := hu.rpow_const (p := (-2 / 3 : ℝ))
    (Or.inl (regularizedBlockNorm_pos ε hε (A t)).ne')
  have hq := hasDerivAt_regularizedRadialDerivative hA hZ hs hε
  have h := (hp.const_mul (1 / 3 : ℝ)).mul hq
  change HasDerivAt (fun s => regularizedWeylRootFirst ε (A s) (Z s)) _ t at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [regularizedWeylRootSecond]
  norm_num
  ring

theorem regularizedWeylRootSecond_sum (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hZ : ∀ i, symmetric (Z i)) (hX : hessianTrace X = weylLaplacian A) :
    (∑ i, regularizedWeylRootSecond ε A (Z i) (X i i)) =
      (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) *
        (weylGradientEnergy Z + Matrix.trace (A * weylLaplacian A) / 6 -
          (5 / 3 : ℝ) * ∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) := by
  have hn := regularizedBlockNorm_pos ε hε A
  have hp : regularizedBlockNorm ε A ^ (-2 / 3 : ℝ) =
      regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) * regularizedBlockNorm ε A := by
    simpa only [show (-5 / 3 : ℝ) + 1 = -2 / 3 by norm_num] using
      Real.rpow_add_one hn.ne' (-5 / 3 : ℝ)
  simp only [regularizedWeylRootSecond, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [regularizedRadialSecond_sum ε A Z X hZ hX, hp]
  field_simp [hn.ne']
  ring

theorem weylLaplacian_trace_lower (A : Mat) (hA : symmetric A) (htA : traceFree A) :
    36 * normalizedBlockNorm A ^ 2 * (1 - normalizedBlockNorm A) ≤
      Matrix.trace (A * weylLaplacian A) := by
  have ht : matrixPairing A (weylLaplacian A) = Matrix.trace (A * weylLaplacian A) := by
    rw [matrixPairing_eq_trace]
    congr 2
    ext i j
    exact weylLaplacian_symmetric A hA j i
  rw [← ht, weylLaplacian_pairing A hA htA]
  have hshape := normalizedDeterminantShape_le_one A hA htA
  have hv := normalizedBlockNorm_nonneg A
  have hh := mul_nonneg (sub_nonneg.mpr hshape) (pow_nonneg hv 3)
  nlinarith only [hh]

theorem continuous_regularizedWeylRoot (ε : ℝ) :
    Continuous (regularizedWeylRoot ε) := by
  exact (continuous_regularizedBlockNorm ε).rpow_const
    (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))

theorem continuous_regularizedWeylRootFirst {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z : Ω → Mat)
    (hA : Continuous A) (hZ : Continuous Z) :
    Continuous (fun x => regularizedWeylRootFirst ε (A x) (Z x)) := by
  have hp := ((continuous_regularizedBlockNorm ε).comp hA).rpow_const
    (p := (-2 / 3 : ℝ)) (fun x => Or.inl (regularizedBlockNorm_pos ε hε (A x)).ne')
  exact (hp.const_mul (1 / 3 : ℝ)).mul
    (continuous_regularizedRadialDerivative ε hε A Z hA hZ)

theorem continuous_regularizedWeylRootSecond {Ω : Type*} [TopologicalSpace Ω]
    (ε : ℝ) (hε : 0 < ε) (A Z X : Ω → Mat)
    (hA : Continuous A) (hZ : Continuous Z) (hX : Continuous X) :
    Continuous (fun x => regularizedWeylRootSecond ε (A x) (Z x) (X x)) := by
  have hp := ((continuous_regularizedBlockNorm ε).comp hA).rpow_const
    (p := (-2 / 3 : ℝ)) (fun x => Or.inl (regularizedBlockNorm_pos ε hε (A x)).ne')
  have hq := ((continuous_regularizedBlockNorm ε).comp hA).rpow_const
    (p := (-5 / 3 : ℝ)) (fun x => Or.inl (regularizedBlockNorm_pos ε hε (A x)).ne')
  exact ((hp.const_mul (1 / 3 : ℝ)).mul
    (continuous_regularizedRadialSecond ε hε A Z X hA hZ hX)).sub
      ((hq.const_mul (2 / 9 : ℝ)).mul
        ((continuous_regularizedRadialDerivative ε hε A Z hA hZ).pow 2))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetrize an oriented frame measure only for the reflection-invariant
Green integral. Scalar variance and Weyl gaps still use the original
oriented measure. Reflection invariance of that original measure is not
assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def symmetricFrameMeasure (g : SmoothMetric M) (μ : Measure (FrameBundle g)) :
    Measure (FrameBundle g) := μ + μ.map frameReflection

instance symmetricFrameMeasure_finite [IsFiniteMeasure μ] :
    IsFiniteMeasure (symmetricFrameMeasure g μ) := by
  unfold symmetricFrameMeasure
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Continuous.aemeasurable; apply continuous_frameReflection <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite square-root energy inequality on the original measure.
Only parallel-flow compatibility with reflection is used: the plus equation
is applied to the reflected measure and then pulled back. The original
oriented measure is never required to be reflection invariant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem blockNorm_frameReflection (e : FrameBundle g) :
    normalizedBlockNorm (plusWeyl g (frameReflection e).base (frameReflection e).frame) =
      normalizedBlockNorm (minusWeyl g e.base e.frame) := by
  change normalizedBlockNorm (plusWeyl g e.base e.frame.reflect) = _
  rw [plusWeyl_reflect]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-frame changes and their exact Frobenius invariants. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped Manifold ContDiff BigOperators

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.frameNormalFrobenius
theorem conjugate_frobenius_norm_sq (V A : Mat3) (hV : Vᵀ * V = 1) :
    ‖Vᵀ * A * V‖ ^ 2 = ‖A‖ ^ 2 := by
  have h := QuaternionFrame.conjugateMatrix_pairing V (mul_eq_one_comm.mp hV) A A
  rw [← squareNorm_eq_frobenius_norm_sq, ← squareNorm_eq_frobenius_norm_sq]
  simpa only [QuaternionFrame.conjugateMatrix, matrixPairing, Angular.squareNorm, pow_two]
    using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem normalRestriction_same_direction (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) (K : Mat4) :
    normalRestriction f.matrix K =
      (normalChange (e.changeMatrix f))ᵀ * normalRestriction e.matrix K *
        normalChange (e.changeMatrix f) := by
  have hrow (j : Fin 4) : e.changeMatrix f 0 j = if (0 : Fin 4) = j then 1 else 0 := by
    have h := congrArg (fun A : Mat4 => A 0 j) (e.changeMatrix_orthogonal f)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply,
      e.changeMatrix_first f hfirst, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, Matrix.one_apply] using h
  calc
    _ = normalRestriction (e.matrix * e.changeMatrix f) K := by
      rw [e.mul_changeMatrix f]
    _ = _ := normalRestriction_conjugate _ _ _ hrow

theorem normalRestriction_norm_sq_same_direction (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) (K : Mat4) :
    ‖normalRestriction e.matrix K‖ ^ 2 = ‖normalRestriction f.matrix K‖ ^ 2 := by
  rw [normalRestriction_same_direction e f hfirst]
  exact (conjugate_frobenius_norm_sq _ _
    (normalChange_orthogonal _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_first f hfirst))).symm

theorem normalRestriction_sub_one_norm_sq_same_direction
    (e f : OrthonormalFrame g c) (hfirst : e.vector 0 = f.vector 0) (K : Mat4) :
    ‖normalRestriction e.matrix K - 1‖ ^ 2 =
      ‖normalRestriction f.matrix K - 1‖ ^ 2 := by
  let V := normalChange (e.changeMatrix f)
  have hV : Vᵀ * V = 1 := normalChange_orthogonal _
    (e.changeMatrix_orthogonal f) (e.changeMatrix_first f hfirst)
  have heq : normalRestriction f.matrix K - 1 =
      Vᵀ * (normalRestriction e.matrix K - 1) * V := by
    rw [normalRestriction_same_direction e f hfirst]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV]
    rfl
  rw [heq]
  exact (conjugate_frobenius_norm_sq _ _ hV).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exchanged polynomial test in (18), obtained from the proved
plus-block test by the actual frame reflection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def kappaNormIntegrand (A B : Mat) (Z V : Angular.Gradient) : ℝ :=
  regularizedKappa 0 A B * scalarNormExpression 0 A Z +
    ∑ i, regularizedKappaDerivative 0 A B (Z i) (V i) * regularizedRadialDerivative 0 A (Z i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature and its covariant derivative depend on the first
frame direction through their Frobenius norms, not on the normal basis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem frameTensor_normal_matrix (E : Mat4) (T : CovariantCoordinates 4)
    (i j : Fin 4) :
    frameTensor E T ![i, 0, 0, j] =
      (Eᵀ * directionalCurvatureMatrix T (fun a => E a 0) * E) i j := by
  rw [frameTensor_four, directionalCurvature_sumFour_moveLast]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, directionalCurvatureMatrix,
    Finset.sum_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem frameTensor_directionalDerivative (E : Mat4) (T : CovariantCoordinates 5)
    (a : Fin 4 → Fin 4) :
    frameTensor E T (Fin.cons 0 a) =
      frameTensor E (directionalDerivativeTensor T (fun d => E d 0)) a := by
  rw [frameTensor_cons]
  simp only [directionalDerivativeTensor, frameTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rotation of the actual first curvature derivative, including its
covector direction, before either Weyl block is contracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem frameTensor_directionFrame_normal (T : CovariantCoordinates 5)
    (q : Directions) (i j : Fin 3) :
    frameTensor (directionFrameMatrix q) T ![0, i.succ, 0, 0, j.succ] =
      ∑ d, q.val d * normalEvaluation q i j (curvatureDerivativeArray T d) := by
  change frameTensor (directionFrameMatrix q) T
    (Fin.cons (0 : Fin 4) (![i.succ, 0, 0, j.succ] : Fin 4 → Fin 4)) = _
  rw [frameTensor_cons]
  simp only [frameTensor_four, directionFrameMatrix_zero, directionFrameMatrix_succ,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  change (∑ a, ∑ b, ∑ c, ∑ f, q.val d *
    (normalVector q i a * q.val b * q.val c * normalVector q j f *
      T (Fin.cons d ![a, b, c, f]))) = q.val d *
    (∑ a, ∑ b, ∑ c, ∑ f, T (Fin.cons d ![a, b, c, f]) *
      normalVector q i a * q.val b * q.val c * normalVector q j f)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem normalDeviation_sum_smul (a : Fin 4 → ℝ) (Z W : Gradient) (q : Directions) :
    normalDeviation (∑ d, a d • Z d) (∑ d, a d • W d) q =
      ∑ d, a d • normalDeviation (Z d) (W d) q := by
  simp only [normalDeviation, rotated, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_add_distrib,
    Finset.smul_sum, smul_add, smul_smul]
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_comm (1 / 2 : ℝ) (a d)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify the actual metric integral with the finite-array integrand.
Only fixed frame reflection is used for the second Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def weylWeightGradient (A U : Mat) (Z V : Angular.Gradient) : Vec :=
  WithLp.toLp 2 (fun i => regularizedWeylWeightDerivative 0 A U (Z i) (V i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normalization of the two quaternionic blocks in the full tensor norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators

noncomputable section

theorem frameTensorPairing_twoFormProduct (R : CovariantCoordinates 4) (P Q : Mat4) :
    frameTensorPairing R (fun a => twoFormProduct P Q (a 0) (a 1) (a 2) (a 3)) =
      8 * twoFormPairing R P Q := by
  rw [frameTensorPairing, sum_four_coordinates]
  change (∑ i, ∑ j, ∑ k, ∑ l, R ![i, j, k, l] * (P i j * Q l k)) =
    8 * ((1 / 8 : ℝ) * ∑ i, ∑ j, ∑ l, ∑ k, R ![i, j, k, l] * P i j * Q l k)
  rw [show ∀ x : ℝ, 8 * ((1 / 8 : ℝ) * x) = x by intro x; ring]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Block assembly is four times the adjoint of the normalized block contraction. -/
theorem frameTensorPairing_blockTensor (R : CovariantCoordinates 4)
    (A : Mat3) (Q : Fin 3 → Mat4) :
    frameTensorPairing R (blockTensorCoordinates A Q) =
      4 * matrixPairing A (blockCoordinates R Q) := by
  have hb : blockTensorCoordinates A Q = fun a =>
      (1 / 2 : ℝ) * ∑ s, ∑ t, A s t *
        twoFormProduct (Q s) (Q t) (a 0) (a 1) (a 2) (a 3) := by
    funext a
    simp only [blockTensorCoordinates, blockTensor, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul]
  rw [hb, frameTensorPairing_const_mul_right]
  simp only [frameTensorPairing_sum_right, frameTensorPairing_const_mul_right,
    frameTensorPairing_twoFormProduct, ← blockCoordinates_pairing]
  simp only [matrixPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem frameTensorSquareNorm_of_blocks (R : CovariantCoordinates 4) (A B : Mat3)
    (hR : R = blockTensorCoordinates A quaternionMatrix + blockTensorCoordinates B oppositeMatrix)
    (hA : blockCoordinates R quaternionMatrix = A)
    (hB : blockCoordinates R oppositeMatrix = B) :
    frameTensorSquareNorm R = 4 * (squareNorm A + squareNorm B) := by
  change frameTensorPairing R R = _
  calc
    _ = frameTensorPairing R
        (blockTensorCoordinates A quaternionMatrix + blockTensorCoordinates B oppositeMatrix) :=
      congrArg (frameTensorPairing R) hR
    _ = _ := by
      rw [frameTensorPairing_add_right, frameTensorPairing_blockTensor,
        frameTensorPairing_blockTensor, hA, hB]
      simp only [matrixPairing, squareNorm, pow_two]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two total Weyl energies are base scalars, proved from the actual
orthonormal-frame tensor norm and the quaternionic normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem squareNorm_one_add (A : Mat3) (ht : A.trace = 0) :
    squareNorm (1 + A) = 3 + squareNorm A := by
  have h : squareNorm (1 + A) = 3 + 2 * A.trace + squareNorm A := by
    simp only [squareNorm, Matrix.add_apply, Matrix.one_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_three]
    norm_num
    ring
  rw [h, ht]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem curvature_blockCoordinates (e : OrthonormalFrame g c)
    (Q : Fin 3 → Mat4) :
    blockCoordinates (frameTensor e.matrix
      (curvatureCoordinates g c (chartAt FourSpace c c))) Q =
      curvatureBlock (curvaturePairing g c e) Q := by
  ext s t
  simp only [blockCoordinates, curvatureBlock]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [frameTensor_curvatureCoordinates]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full finite-array integrand is the actual metric integral from
both Green identities, trace subtraction, variance, and polynomial tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

def varianceDensity (A U : Mat) (p q : Vec) : ℝ :=
  ‖p - q‖ ^ 2 / (4 + normalizedBlockNorm A ^ 2 + normalizedBlockNorm U ^ 2) -
    (1 - (2 - normalizedBlockNorm A - normalizedBlockNorm U) ^ 2 / 4) *
      (normalizedBlockNorm A - normalizedBlockNorm U) ^ 2

def traceCouplingTerm (A U : Mat) (Z V : Angular.Gradient) : ℝ :=
  -(weylGradientEnergy Z + weylGradientEnergy V) *
      (scalarNormExpression 0 A Z + scalarNormExpression 0 U V) -
    26 * (2 - normalizedBlockNorm A - normalizedBlockNorm U) *
      (weylGradientEnergy Z + weylGradientEnergy V) +
    40 * (2 - normalizedBlockNorm A - normalizedBlockNorm U) *
      (weylMatrixEnergy A Z + weylMatrixEnergy U V) -
    (2 - normalizedBlockNorm A - normalizedBlockNorm U) * (traceEnergy A + traceEnergy U)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite curvature contractions occurring in the four-dimensional
Euler and first Pontryagin densities.  These are pointwise identities for
the actual metric curvature; no characteristic-number or Hodge theorem is
assumed or asserted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem squareNorm_one_add_trace (A : Mat3) (ht : A.trace = 0) :
    squareNorm (1 + A) = 3 + squareNorm A := by
  have h : squareNorm (1 + A) = 3 + 2 * A.trace + squareNorm A := by
    simp only [squareNorm, Matrix.add_apply, Matrix.one_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_three]
    norm_num
    ring
  rw [h, ht]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal coefficient matrices of orientation-preserving four-frame changes. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

theorem basis_pairing_combinations (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, fourMatrixPairing (Q r) (Q s) = if r = s then 4 else 0)
    (u v : Fin 3 → ℝ) :
    fourMatrixPairing (imaginaryCombination Q u) (imaginaryCombination Q v) =
      4 * ∑ r, u r * v r := by
  simp only [imaginaryCombination, Fin.sum_univ_three, fourMatrixPairing_add_left,
    fourMatrixPairing_add_right, fourMatrixPairing_smul_left,
    fourMatrixPairing_smul_right, hQ]
  norm_num
  ring

/-- An orthogonal action on an orthogonal three-dimensional two-form basis
has an orthogonal matrix of coefficients. -/
theorem coefficientMatrix_orthogonal (P : Mat4) (Q : Fin 3 → Mat4) (R : Mat3)
    (hP : Pᵀ * P = 1)
    (hQ : ∀ r s, fourMatrixPairing (Q r) (Q s) = if r = s then 4 else 0)
    (hR : ∀ s, P * Q s * Pᵀ = imaginaryCombination Q (fun r => R r s)) :
    Rᵀ * R = 1 := by
  ext s t
  have h := fourMatrixPairing_conjugate P (Q s) (Q t) hP
  rw [hR s, hR t, basis_pairing_combinations Q hQ, hQ] at h
  change (∑ r, R r s * R r t) = if s = t then 1 else 0
  by_cases hst : s = t
  · rw [ite_eq_left hst] at h ⊢
    linarith
  · rw [ite_eq_right hst] at h ⊢
    linarith

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The individual Weyl norms descend to each oriented frame component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

/-- The adjoint of tensor pullback by an orthogonal matrix is pullback
by its transpose, on all covariant slots. -/
theorem frameTensorPairing_adjoint {n : ℕ} (P : Mat4) (hP : Pᵀ * P = 1)
    (T S : CovariantCoordinates n) :
    frameTensorPairing (frameTensor P T) S =
      frameTensorPairing T (frameTensor Pᵀ S) := by
  have heq : frameTensor P (frameTensor Pᵀ S) = S := by
    rw [← frameTensor_mul, hP, frameTensor_one]
  calc
    _ = frameTensorPairing (frameTensor P T) (frameTensor P (frameTensor Pᵀ S)) :=
      congrArg (frameTensorPairing (frameTensor P T)) heq.symm
    _ = _ := frameTensor_pairing_orthogonal P (mul_eq_one_comm.mp hP) T (frameTensor Pᵀ S)

/-- Pullback of the tensor product of two two-forms. -/
theorem frameTensor_twoFormProduct (P A B : Mat4) :
    frameTensor P (fun a : Fin 4 → Fin 4 => twoFormProduct A B (a 0) (a 1) (a 2) (a 3)) =
      fun a => twoFormProduct (Pᵀ * A * P) (Pᵀ * B * P)
        (a 0) (a 1) (a 2) (a 3) := by
  funext a
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ s,
    P p (a 0) * P q (a 1) * P r (a 2) * P s (a 3) * (A p q * B s r)) =
      (Pᵀ * A * P) (a 0) (a 1) * (Pᵀ * B * P) (a 3) (a 2)
  rw [bilinearPullback_apply, bilinearPullback_apply, sumPair_product]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoFormPairing_frameTensor (P : Mat4) (hP : Pᵀ * P = 1)
    (T : CovariantCoordinates 4) (A B : Mat4) :
    twoFormPairing (frameTensor P T) A B =
      twoFormPairing T (P * A * Pᵀ) (P * B * Pᵀ) := by
  have h := frameTensorPairing_adjoint P hP T
    (fun a => twoFormProduct A B (a 0) (a 1) (a 2) (a 3))
  rw [frameTensorPairing_twoFormProduct, frameTensor_twoFormProduct,
    Matrix.transpose_transpose, frameTensorPairing_twoFormProduct] at h
  linarith

/-- The block contraction changes by the actual induced three-dimensional
orthogonal coefficient matrix. -/
theorem blockCoordinates_frameTensor (P : Mat4) (hP : Pᵀ * P = 1)
    (Q : Fin 3 → Mat4) (R : Mat3)
    (hR : ∀ s, P * Q s * Pᵀ = imaginaryCombination Q (fun r => R r s))
    (T : CovariantCoordinates 4) :
    blockCoordinates (frameTensor P T) Q =
      conjugateMatrix R (blockCoordinates T Q) := by
  ext s t
  rw [blockCoordinates_pairing, twoFormPairing_frameTensor P hP, hR s, hR t]
  simp only [imaginaryCombination, Fin.sum_univ_three, twoFormPairing_add_left,
    twoFormPairing_add_right, twoFormPairing_smul_left, twoFormPairing_smul_right]
  simp only [conjugateMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three, blockCoordinates_pairing]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameCurvatureBlock_eq (e : OrthonormalFrame g c)
    (Q : Fin 3 → Mat4) :
    curvatureBlock (curvaturePairing g c e) Q =
      blockCoordinates (frameTensor e.matrix
        (curvatureCoordinates g c (chartAt FourSpace c c))) Q := by
  ext a b
  simp only [blockCoordinates, curvatureBlock, frameTensor_curvatureCoordinates,
    curvaturePairing]

theorem blockNorm_same_oriented_frame (e f : OrthonormalFrame g c)
    (Q : Fin 3 → Mat4) (R : Mat3) (hR : Rᵀ * R = 1)
    (hspan : ∀ s, e.changeMatrix f * Q s * (e.changeMatrix f)ᵀ =
      imaginaryCombination Q (fun r => R r s)) :
    normalizedBlockNorm (curvatureBlock (curvaturePairing g c e) Q - 1) =
      normalizedBlockNorm (curvatureBlock (curvaturePairing g c f) Q - 1) := by
  let T : CovariantCoordinates 4 := curvatureCoordinates g c (chartAt FourSpace c c)
  have heq : blockCoordinates (frameTensor f.matrix T) Q =
      conjugateMatrix R (blockCoordinates (frameTensor e.matrix T) Q) := by
    rw [← e.mul_changeMatrix f, frameTensor_mul]
    exact blockCoordinates_frameTensor _ (e.changeMatrix_orthogonal f) Q R hspan _
  rw [frameCurvatureBlock_eq e Q, frameCurvatureBlock_eq f Q]
  change normalizedBlockNorm (blockCoordinates (frameTensor e.matrix T) Q - 1) =
    normalizedBlockNorm (blockCoordinates (frameTensor f.matrix T) Q - 1)
  rw [heq]
  have hsub (B : Mat3) : conjugateMatrix R (B - 1) = conjugateMatrix R B - 1 := by
    rw [conjugateMatrix_sub, conjugateMatrix_one R hR]
  rw [← hsub]
  exact (conjugateMatrix_norm R (mul_eq_one_comm.mp hR) _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weyl-norm difference variance follows by passing the smooth scalar
theorem to the limit using parallel-frame calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
  {g : SmoothMetric M}
  {μ : Measure (FrameBundle g)}

def normRegularizationParameter (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem blockCoordinates_contDiffAt {T : FourSpace → CovariantCoordinates 4}
    {z : FourSpace} (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z)
    (Q : Fin 3 → Mat4) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun w => blockCoordinates (T w) Q i j) z := by
  change ContDiffAt ℝ ∞ (fun w => (1 / 8 : ℝ) * ∑ a : Fin 4 × Fin 4,
    ∑ b : Fin 4 × Fin 4, T w ![a.1, a.2, b.2, b.1] * Q i a.1 a.2 * Q j b.1 b.2) z
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact ((hT _).mul contDiffAt_const).mul contDiffAt_const

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual changes of orthonormal frame on the six two-form coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix

noncomputable section

theorem twoFormFrameAction_comp (P Q : Mat4) (a : TwoFormFour) :
    twoFormFrameAction Q (twoFormFrameAction P a) = twoFormFrameAction (P * Q) a := by
  apply twoFormMatrix_injective
  simp only [twoFormMatrix_frameAction, Matrix.transpose_mul, Matrix.mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial absorption and actual Gaussian moment bounds for the local
heat remainder. These bounds use Euclidean volume and the proved unit mass. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_integral_moment_bound (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, ‖x‖ ^ (2 * m) * fourHeatGaussian t x) ≤
      4 * (m.factorial : ℝ) * (8 * t) ^ m := by
  calc
    _ ≤ ∫ x : FourSpace,
        (4 * (m.factorial : ℝ) * (8 * t) ^ m) * fourHeatGaussian (2 * t) x :=
      integral_mono (fourHeatGaussian_moment_integrable m t ht)
        ((fourHeatGaussian_integrable (2 * t) (by positivity)).const_mul _)
        (fourHeatGaussian_moment_bound m t ht)
    _ = _ := by
      rw [integral_const_mul, fourHeatGaussian_mass (2 * t) (by positivity), mul_one]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatAwayBound
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.vector_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Gaussian derivative scale is uniformly O(t) away from the center.
This is the bound used for the normal-chart cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour

noncomputable section

theorem fourHeatGaussian_away_inverse_time (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (x : FourSpace) (hx : r ≤ ‖x‖) :
    fourHeatGaussian t x / t ≤ (384 / (Real.pi ^ 2 * r ^ 8)) * t := by
  have hpow : r ^ 8 ≤ ‖x‖ ^ 8 := pow_le_pow_left₀ hr.le hx 8
  have hG : 0 ≤ fourHeatGaussian t x / t := div_nonneg (fourHeatGaussian_pos t ht x).le ht.le
  have hb : r ^ 8 * (fourHeatGaussian t x / t) ≤ (384 / Real.pi ^ 2) * t :=
    (mul_le_mul_of_nonneg_right hpow hG).trans (fourHeatGaussian_weighted_inverse_time t ht x)
  calc
    _ ≤ ((384 / Real.pi ^ 2) * t) / r ^ 8 :=
      (le_div_iff₀ (pow_pos hr 8)).mpr (by simpa only [mul_comm] using hb)
    _ = _ := by field_simp

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricDistance
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tangent norm and path distance of a smooth metric. These
basic definitions are independent of the classification and scaling steps. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricEDistance_eq_iInf (g : SmoothMetric M) (x y : M) :
    metricEDistance g x y =
      ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I4 1 γ),
        ∫⁻ t, metricTangentENorm g (γ t) (mfderiv (𝓡∂ 1) I4 γ t 1) := by
  simp only [metricEDistance, Manifold.riemannianEDist, metricTangentENorm]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper volume estimate from the Jacobi ODE, curvature-field identities,
energy bounds, and the polar volume formula. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

local instance instNormedAddCommGroupNormalMatrix_3_re98581_1 : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealNormalMatrix_2_re98581_1 : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace
local instance instNormedAddCommGroupContinuousMapNormalMatrix_2_re98581_1 : NormedAddCommGroup C(Ω, NormalMatrix) :=
  ContinuousMap.instNormedAddCommGroup
local instance instNormedSpaceRealContinuousMapNormalMatrix_2_re98581_1 : NormedSpace ℝ C(Ω, NormalMatrix) := ContinuousMap.normedSpace
/-- Equation (7) from the actual Jacobi ODE and the two geodesic field
identities. -/
theorem volume_ratio_upper_of_jacobi
    (d : (u : ℝ) → Ω → RegularJacobi (Real.pi * u))
    {F G : ℝ → C(Ω, NormalMatrix)} {V s : ℝ}
    (hs : 0 ≤ s)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = (3 / 2) * s)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * ((3 / 2) * s))
    (hcurvature : ∀ u x r, (d u x).R r = 1 + F r x)
    (hpos : ∀ u x r, ((d u x).R r).PosSemidef)
    (htrace : ∀ u x r, ((d u x).R r).trace = 3)
    (hLip : ∀ u, 0 < u → u < 1 → ∀ x, ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
      ‖Averages.sineWeight a • radialCurvature (d u x).R (Real.pi * u) a -
        Averages.sineWeight b • radialCurvature (d u x).R (Real.pi * u) b‖ ≤ L * |a - b|)
    (hD : ∀ u, 0 < u → u < 1 → Integrable (fun x => (d u x).truncatedDensity) μ)
    (hD0 : IntervalIntegrable (fun u => ∫ x, (d u x).truncatedDensity ∂μ)
      volume 0 (5 / 8))
    (hD1 : IntervalIntegrable (fun u => ∫ x, (d u x).truncatedDensity ∂μ)
      volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ x, (d u x).truncatedDensity ∂μ) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ x, (d u x).truncatedDensity ∂μ)) :
    V ≤ 1 - (3 / 40) * s := by
  apply volume_ratio_upper_of_averaged_radial hs hD0 hD1 hpolar
  intro u hu hu1
  exact averaged_truncatedDensity_le (d u) (mul_pos Real.pi_pos hu)
    (by nlinarith [Real.pi_pos]) (by positivity) hderiv hstationary henergy
    (hcurvature u) (hpos u) (htrace u) (hLip u hu hu1) (hD u hu hu1)

end

end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverTopology
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual orientation cover has a continuous free deck involution and
exactly two points over each base point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCoverDeck_free (x : OrientationCover M) : orientationCoverDeck x ≠ x := by
  intro h
  have hb : (!x.snd) = x.snd := congrArg TotalSpace.snd h
  exact Bool.not_ne_self x.snd hb

theorem orientationCover_fibers (x y : OrientationCover M) :
    orientationCoverProjection x = orientationCoverProjection y ↔
      x = y ∨ x = orientationCoverDeck y := by
  constructor
  · intro h
    cases x with
    | mk a s =>
      cases y with
      | mk b t =>
        change a = b at h
        subst b
        cases s <;> cases t <;> simp [orientationCoverDeck]
  · rintro (rfl | rfl) <;> rfl

theorem orientationCoverProjection_surjective :
    Function.Surjective (orientationCoverProjection (M := M)) := fun x => ⟨⟨x, false⟩, rfl⟩

instance orientationCover_t2Space [T2Space M] : T2Space (OrientationCover M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hne
  by_cases hbase : x.proj = y.proj
  · let Z := orientationCoverCore (M := M)
    let e := Z.localTrivAt x.proj
    have hx : x ∈ e.source := Z.mk_mem_localTrivAt_source x.proj x.snd
    have hy : y ∈ e.source := e.mem_source.mpr (hbase ▸ Z.mem_localTrivAt_baseSet x.proj)
    have hxy : e x ≠ e y := fun heq => hne (e.toOpenPartialHomeomorph.injOn hx hy heq)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hxy) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (orientationCover_isCoveringMap.continuous).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase) (orientationCover_isCoveringMap.continuous).continuousAt

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverCompactness
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness of the actual two-sheeted orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_compact_orientationCover_neighborhood (x : M) :
    ∃ U ∈ 𝓝 x, ∃ K : Set (OrientationCover M), IsCompact K ∧
      ∀ y : OrientationCover M, y.proj ∈ U → y ∈ K := by
  let Z := orientationCoverCore (M := M)
  let e := Z.localTrivAt x
  obtain ⟨C, hCc, hCx, hCe⟩ := exists_compact_subset e.open_baseSet (Z.mem_localTrivAt_baseSet x)
  let K := e.toOpenPartialHomeomorph.symm '' (C ×ˢ (univ : Set Bool))
  have hK : IsCompact K := (hCc.prod isCompact_univ).image_of_continuousOn
    (e.toOpenPartialHomeomorph.continuousOn_symm.mono (by
      intro p hp
      exact e.mem_target.mpr (hCe hp.1)))
  refine ⟨C, mem_interior_iff_mem_nhds.mp hCx, K, hK, ?_⟩
  intro y hy
  have hs : y ∈ e.source := e.mem_source.mpr (hCe hy)
  refine ⟨e y, ?_, e.toOpenPartialHomeomorph.left_inv hs⟩
  have hp : (e y).1 = y.proj := e.proj_toFun y hs
  exact ⟨hp.symm ▸ hy, mem_univ _⟩

instance orientationCover_compactSpace : CompactSpace (OrientationCover M) := by
  choose U hU K hK hcover using exists_compact_orientationCover_neighborhood (M := M)
  obtain ⟨t, ht⟩ := finite_cover_nhds hU
  apply isCompact_univ_iff.mp
  have hc : IsCompact (⋃ x ∈ t, K x) :=
    t.finite_toSet.isCompact_biUnion (fun x _ => hK x)
  have heq : (⋃ x ∈ t, K x) = (univ : Set (OrientationCover M)) := by
    apply univ_subset_iff.mp
    intro y _
    have hy : y.proj ∈ ⋃ x ∈ t, U x := by rw [ht]; trivial
    obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x, hxt, hcover x y hx⟩
  rwa [heq] at hc

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverClosed
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation and countability of the compact smooth orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

instance orientationCover_t3Space : T3Space (OrientationCover M) := inferInstance

instance orientationCover_secondCountable : SecondCountableTopology (OrientationCover M) :=
  ChartedSpace.secondCountable_of_sigmaCompact FourSpace (OrientationCover M)

instance orientationCover_nonempty [Nonempty M] : Nonempty (OrientationCover M) := by
  obtain ⟨x⟩ := ‹Nonempty M›
  exact ⟨⟨x, false⟩⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverClopenSheet
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A disconnected two-sheeted orientation cover has a continuous global sheet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set Function _root_.Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
theorem orientationCover_image_clopen {U : Set (OrientationCover M)} (hU : IsClopen U) :
    IsClopen (orientationCoverProjection '' U) := by
  refine ⟨?_, ?_⟩
  · exact (hU.isClosed.isCompact.image orientationCover_isCoveringMap.continuous).isClosed
  · exact orientationCover_isCoveringMap.isLocalHomeomorph.isOpenMap U hU.isOpen

theorem orientationCover_clopen_surjective {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hne : U.Nonempty) :
    orientationCoverProjection '' U = univ :=
  (orientationCover_image_clopen hU).eq_univ (hne.image _)

theorem orientationCover_clopen_deck_notMem {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hproper : Uᶜ.Nonempty) {x : OrientationCover M} (hx : x ∈ U) :
    orientationCoverDeck x ∉ U := by
  have himage := orientationCover_clopen_surjective hU.compl hproper
  have hm : x.proj ∈ orientationCoverProjection '' Uᶜ := by rw [himage]; trivial
  obtain ⟨z, hz, hp⟩ := hm
  rcases (orientationCover_fibers z x).mp hp with h | h
  · exact False.elim (hz (h ▸ hx))
  · exact h ▸ hz

theorem orientationCover_clopen_projection_bijective {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hne : U.Nonempty) (hproper : Uᶜ.Nonempty) :
    Bijective (fun x : U => (x.val).proj) := by
  constructor
  · intro x y h
    apply Subtype.ext
    rcases (orientationCover_fibers x.val y.val).mp h with h | h
    · exact h
    · exact False.elim (orientationCover_clopen_deck_notMem hU hproper y.property
        (h ▸ x.property))
  · intro x
    have hm : x ∈ orientationCoverProjection '' U := by
      rw [orientationCover_clopen_surjective hU hne]
      trivial
    obtain ⟨y, hy, hp⟩ := hm
    exact ⟨⟨y, hy⟩, hp⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverDistanceDown
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection preserves the length of every differentiable path, hence cannot
increase the actual Riemannian distance. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_curve_derivative (γ : unitInterval → OrientationCover M)
    (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) (t : unitInterval) :
    mfderiv (𝓡∂ 1) I4 (orientationCoverProjection ∘ γ) t =
      mfderiv (𝓡∂ 1) I4 γ t := by
  have h := mfderiv_comp t
    (orientationCover_projection_hasMFDerivAt (γ t)).mdifferentiableAt
    (hγ t |>.mdifferentiableAt one_ne_zero)
  rw [orientationCover_projection_mfderiv] at h
  exact h

theorem orientationCover_curve_length (g : SmoothMetric M)
    (γ : unitInterval → OrientationCover M) (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) :
    (∫⁻ t, metricTangentENorm g ((γ t).proj)
      (mfderiv (𝓡∂ 1) I4 (orientationCoverProjection ∘ γ) t 1)) =
    ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (γ t)
      (mfderiv (𝓡∂ 1) I4 γ t 1) := by
  apply lintegral_congr
  intro t
  rw [orientationCover_curve_derivative γ hγ t, metricTangentENorm_eq_ofReal,
    metricTangentENorm_eq_ofReal, metricTangentNorm_eq_sqrt, metricTangentNorm_eq_sqrt]
  rfl

theorem orientationCover_distance_down (g : SmoothMetric M) (x y : OrientationCover M) :
    metricEDistance g x.proj y.proj ≤ metricEDistance (orientationCoverMetric g) x y := by
  rw [metricEDistance_eq_iInf (orientationCoverMetric g) x y]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let δ : Path x.proj y.proj := γ.map orientationCover_isCoveringMap.continuous
  have hδ : ContMDiff (𝓡∂ 1) I4 1 δ :=
    (orientationCover_projection_smooth.of_le (by first | simp | exact_mod_cast le_top)).comp hγ
  calc
    metricEDistance g x.proj y.proj ≤
        ∫⁻ t, metricTangentENorm g (δ t) (mfderiv (𝓡∂ 1) I4 δ t 1) := by
      rw [metricEDistance_eq_iInf]
      exact iInf_le_of_le δ (iInf_le _ hδ)
    _ = ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (γ t)
        (mfderiv (𝓡∂ 1) I4 γ t 1) := orientationCover_curve_length g γ hγ

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverDeckMetric
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sheet exchange is an actual smooth isometry for the pullback metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_deck_curve_length (g : SmoothMetric M)
    (γ : unitInterval → OrientationCover M) (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) :
    (∫⁻ t, metricTangentENorm (orientationCoverMetric g) (orientationCoverDeck (γ t))
      (mfderiv (𝓡∂ 1) I4 (orientationCoverDeck ∘ γ) t 1)) =
    ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (γ t)
      (mfderiv (𝓡∂ 1) I4 γ t 1) := by
  apply lintegral_congr
  intro t
  have h := mfderiv_comp t (orientationCover_deck_smooth.mdifferentiable (by simp) (γ t))
    (hγ.mdifferentiable one_ne_zero t)
  rw [orientationCover_deck_mfderiv] at h
  have hd : mfderiv (𝓡∂ 1) I4 (orientationCoverDeck ∘ γ) t =
      mfderiv (𝓡∂ 1) I4 γ t := h
  rw [hd, metricTangentENorm_eq_ofReal, metricTangentENorm_eq_ofReal,
    metricTangentNorm_eq_sqrt, metricTangentNorm_eq_sqrt]
  rfl

theorem orientationCover_deck_distance_le (g : SmoothMetric M)
    (x y : OrientationCover M) :
    metricEDistance (orientationCoverMetric g) (orientationCoverDeck x) (orientationCoverDeck y) ≤
      metricEDistance (orientationCoverMetric g) x y := by
  rw [metricEDistance_eq_iInf (orientationCoverMetric g) x y]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let δ : Path (orientationCoverDeck x) (orientationCoverDeck y) :=
    γ.map continuous_orientationCoverDeck
  have hδ : ContMDiff (𝓡∂ 1) I4 1 δ :=
    (orientationCover_deck_smooth.of_le (by first | simp | exact_mod_cast le_top)).comp hγ
  calc
    metricEDistance (orientationCoverMetric g) (orientationCoverDeck x) (orientationCoverDeck y) ≤
        ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (δ t)
          (mfderiv (𝓡∂ 1) I4 δ t 1) := by
      rw [metricEDistance_eq_iInf]
      exact iInf_le_of_le δ (iInf_le _ hδ)
    _ = _ := orientationCover_deck_curve_length g γ hγ

theorem orientationCover_deck_distance (g : SmoothMetric M) (x y : OrientationCover M) :
    metricEDistance (orientationCoverMetric g) (orientationCoverDeck x) (orientationCoverDeck y) =
      metricEDistance (orientationCoverMetric g) x y := by
  apply le_antisymm (orientationCover_deck_distance_le g x y)
  simpa only [orientationCoverDeck_deck] using
    orientationCover_deck_distance_le g (orientationCoverDeck x) (orientationCoverDeck y)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverPathLift
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth paths lift through the actual cover without changing length. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_orientationCover_path_lift (x : OrientationCover M) {b : M}
    (γ : Path x.proj b) (hγ : ContMDiff (𝓡∂ 1) I4 1 γ) :
    ∃ z : OrientationCover M, z.proj = b ∧ ∃ δ : Path x z,
      ContMDiff (𝓡∂ 1) I4 1 δ ∧ orientationCoverProjection ∘ δ = γ := by
  let C := orientationCover_isCoveringMap (M := M)
  let Γ := C.liftPath γ.toContinuousMap x γ.source
  have he : orientationCoverProjection ∘ Γ = γ := C.liftPath_lifts γ.toContinuousMap x γ.source
  let δ : Path x (Γ 1) := ⟨Γ, C.liftPath_zero γ.toContinuousMap x γ.source, rfl⟩
  refine ⟨Γ 1, ?_, δ, ?_, he⟩
  · exact (congrFun he 1).trans γ.target
  · apply contMDiff_orientationCover_lift Γ.continuous
    change ContMDiff (𝓡∂ 1) I4 1 (orientationCoverProjection ∘ Γ)
    rwa [he]

theorem orientationCover_min_distance_le (g : SmoothMetric M) (x y : OrientationCover M) :
    min (metricEDistance (orientationCoverMetric g) x y)
      (metricEDistance (orientationCoverMetric g) x (orientationCoverDeck y)) ≤
      metricEDistance g x.proj y.proj := by
  rw [metricEDistance_eq_iInf g x.proj y.proj]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  obtain ⟨z, hz, δ, hδ, he⟩ := exists_orientationCover_path_lift x γ hγ
  have hdist : metricEDistance (orientationCoverMetric g) x z ≤
      ∫⁻ t, metricTangentENorm (orientationCoverMetric g) (δ t)
        (mfderiv (𝓡∂ 1) I4 δ t 1) := by
    rw [metricEDistance_eq_iInf]
    exact iInf_le_of_le δ (iInf_le _ hδ)
  have hlen := orientationCover_curve_length g δ hδ
  change (∫⁻ t, metricTangentENorm g ((orientationCoverProjection ∘ δ) t)
    (mfderiv (𝓡∂ 1) I4 (orientationCoverProjection ∘ δ) t 1)) = _ at hlen
  rw [he] at hlen
  have hbound := hdist.trans_eq hlen.symm
  rcases (orientationCover_fibers z y).mp hz with rfl | rfl
  · exact (min_le_left _ _).trans hbound
  · exact (min_le_right _ _).trans hbound

theorem orientationCover_distance_lift (g : SmoothMetric M) (x y : OrientationCover M) :
    ∃ z : OrientationCover M, z.proj = y.proj ∧
      metricEDistance (orientationCoverMetric g) x z ≤ metricEDistance g x.proj y.proj := by
  have h := orientationCover_min_distance_le g x y
  by_cases hd : metricEDistance (orientationCoverMetric g) x y ≤
      metricEDistance (orientationCoverMetric g) x (orientationCoverDeck y)
  · exact ⟨y, rfl, (min_eq_left hd) ▸ h⟩
  · exact ⟨orientationCoverDeck y, rfl, (min_eq_right (le_of_not_ge hd)) ▸ h⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrientationCoverMetricDoubleCover
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The determinant-sign cover and its pullback metric form a metric double cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scaledEDistance_one_eq (g : SmoothMetric M) (x y : M) :
    scaledEDistance g 1 x y = metricEDistance g x y := by
  change ENNReal.ofReal (Real.sqrt 1) * metricEDistance g x y = _
  simp

def actualOrientationDoubleCover (g : SmoothMetric M) :
    MetricDoubleCover g (orientationCoverMetric g) where
  projection := orientationCoverProjection
  covering := orientationCover_isCoveringMap
  surjective := orientationCoverProjection_surjective
  deck := orientationCoverDeck
  involutive := orientationCoverDeck_deck
  free := orientationCoverDeck_free
  fibers := orientationCover_fibers
  deck_distance x y := by
    simp only [scaledEDistance_one_eq]
    exact orientationCover_deck_distance g x y
  distance_down x y := by
    simp only [scaledEDistance_one_eq]
    exact orientationCover_distance_down g x y
  distance_lift x y := by
    simp only [scaledEDistance_one_eq]
    exact orientationCover_distance_lift g x y

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual Euler and signature curvature integrals in the normalization
used by the classification. These are metric integrals; their global index
interpretation is a separate step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M}

def orientedEulerDensity (g : SmoothMetric M) (o : FrameOrientation g) (c : M) : ℝ :=
  curvatureEulerDensity
    (frameTensor (o.frame c).matrix (curvatureCoordinates g c (chartAt FourSpace c c)))

theorem volumeMeasure_integral_eq_total_mul (hvol : FinitePositiveVolume g) (f : M → ℝ) :
    (∫ c, f c ∂volumeMeasure g) = totalVolume g * ∫ c, f c ∂normalizedVolume g := by
  rw [normalizedVolume, integral_smul_measure, ENNReal.toReal_inv]
  change (∫ c, f c ∂volumeMeasure g) =
    totalVolume g * ((totalVolume g)⁻¹ * ∫ c, f c ∂volumeMeasure g)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (totalVolume_pos hvol)), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The determinant of a moving frame in a fixed sheet chart follows the
same sign cocycle that defines the actual orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientationLinearMatrix (L : FourSpace →L[ℝ] FourSpace) : Mat4 :=
  fun i j => L (coordinateVector j) i

theorem orientationLinearMatrix_det (L : FourSpace →L[ℝ] FourSpace) :
    (orientationLinearMatrix L).det = L.det := by
  have h : orientationLinearMatrix L = LinearMap.toMatrix
      (PiLp.basisFun 2 ℝ (Fin 4)) (PiLp.basisFun 2 ℝ (Fin 4)) L.toLinearMap := by
    ext i j
    simp [orientationLinearMatrix, LinearMap.toMatrix_apply, coordinateVector]
  rw [h]
  exact LinearMap.det_toMatrix _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The tautological orientation on the actual determinant-sign cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set Filter _root_.Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientationCoverPositiveFrames (g : SmoothMetric M) :
    Set (FrameBundle (orientationCoverMetric g)) :=
  {e | e.base.snd = decide (0 < e.frame.matrix.det)}

theorem reflected_frame_det {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] [IsManifold I4 ∞ N] {g : SmoothMetric N} {x : N}
    (e : OrthonormalFrame g x) : e.reflect.matrix.det = -e.matrix.det := by
  change (e.matrix * frameReflectionMatrix).det = _
  rw [Matrix.det_mul]
  have hr : frameReflectionMatrix.det = -1 := by
    norm_num [frameReflectionMatrix, Matrix.det_diagonal, orientationSign, Fin.prod_univ_succ]
  rw [hr]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated Weyl identity follows from the actual pointwise Weyl
equation and measure-preserving parallel-frame differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem matrixVector_norm_sq (A : Mat3) :
    ‖matrixVector A‖ ^ 2 = matrixPairing A A := by
  rw [← real_inner_self_eq_norm_sq, inner_matrixVector]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem h2SchwartzInverse_first (f : 𝓢(V, ℂ)) (i : Fin 4) :
    (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (h2SchwartzInverse f)).toLp 2 volume =
      scalarBesselFirstL2 i (f.toLp 2 volume) := by
  apply h2_L2_injective
  dsimp only
  rw [scalarBesselFirstL2_distribution, ← h2SchwartzInverse_L2,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact (lineDerivOp_toTemperedDistributionCLM_eq _ _).symm

theorem h2SchwartzInverse_second (f : 𝓢(V, ℂ)) (i j : Fin 4) :
    (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
      (∂_{EuclideanSpace.basisFun (Fin 4) ℝ j} (h2SchwartzInverse f))).toLp 2 volume =
      scalarBesselSecondL2 i j (f.toLp 2 volume) := by
  apply h2_L2_injective
  dsimp only
  rw [scalarBesselSecondL2_distribution, ← h2SchwartzInverse_L2,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  simp only [scalarCoordinateDerivative]
  rw [lineDerivOp_toTemperedDistributionCLM_eq, lineDerivOp_toTemperedDistributionCLM_eq]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarH1EllipticGain
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local H3 elliptic gain for an actual first-order Sobolev source. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_ball_H1_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u f : T) (hf : MemSobolev 1 2 f) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = f ψ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    MemSobolev 3 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hc hs
  have hsource (k : ℕ) : MemSobolev 1 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u)) := by
    rw [scalar_localize_eq_of_tests (ball 0 1) _ f htest (ψ k) (hsupp k).1 (hsupp k).2]
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ k) f
      (by simpa only [Nat.cast_one] using hf)
  have houter : MemSobolev 1 2 (M (ψ 2) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ 2) u
      (by simpa only [Nat.cast_one] using hu)
  have hmid : MemSobolev 2 2 (M (ψ 1) u) := by
    have hg := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
      c (ψ 1) (ψ 2) (hnest 1) 0 u (by simpa using houter)
      ((hsource 1).mono (by norm_num))
    simpa using hg
  have hfinal := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c (ψ 0) (ψ 1) (hnest 0) 1 u (by simpa using hmid) (by simpa using hsource 0)
  simpa [hψ] using hfinal

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarH2Closure
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.scalarCoordinateJet_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the first and second weak derivatives through strong L2 limits.
This closes the nonlinear H2 calculation after its explicit product limits. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

/-- Strong convergence of the two jets supplies H2 for their value limit. -/
theorem scalar_H2_of_strong_jets (f : ℕ → L2) (G : Fin 4 → ℕ → L2)
    (H : Fin 4 → Fin 4 → ℕ → L2) (u : L2) (g : Fin 4 → L2) (h : Fin 4 → Fin 4 → L2)
    (hf : Tendsto f atTop (𝓝 u))
    (hg : ∀ i, Tendsto (G i) atTop (𝓝 (g i)))
    (hh : ∀ i j, Tendsto (H i j) atTop (𝓝 (h i j)))
    (hD : ∀ n i, scalarCoordinateDerivative i (f n : T) = (G i n : T))
    (hDD : ∀ n i j, scalarCoordinateDerivative i (G j n : T) = (H i j n : T)) :
    MemSobolev 2 2 (u : T) := by
  have hDu (i : Fin 4) : scalarCoordinateDerivative i (u : T) = (g i : T) :=
    scalar_L2_weak_derivative_limit f (G i) u (g i) hf (hg i) i (fun n => hD n i)
  have hDg (i j : Fin 4) : scalarCoordinateDerivative i (g j : T) = (h i j : T) :=
    scalar_L2_weak_derivative_limit (G j) (H i j) (g j) (h i j) (hg j) (hh i j) i
      (fun n => hDD n i j)
  have hgH1 (j : Fin 4) : MemSobolev 1 2 (g j : T) := by
    have hs := scalar_memSobolev_succ_iff 0 (g j : T)
    norm_num at hs
    rw [hs]
    refine ⟨memSobolev_zero_iff.mpr ⟨g j, rfl⟩, fun i => ?_⟩
    rw [hDg i j]
    exact memSobolev_zero_iff.mpr ⟨h i j, rfl⟩
  have huH1 : MemSobolev 1 2 (u : T) := by
    have hs := scalar_memSobolev_succ_iff 0 (u : T)
    norm_num at hs
    rw [hs]
    refine ⟨memSobolev_zero_iff.mpr ⟨u, rfl⟩, fun i => ?_⟩
    rw [hDu i]
    exact memSobolev_zero_iff.mpr ⟨g i, rfl⟩
  have hc := (scalar_memSobolev_succ_iff 1 (u : T)).mpr
    ⟨huH1, fun i => by rw [hDu i]; exact hgH1 i⟩
  norm_num at hc
  exact hc

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarOpenIntegerEllipticGain
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The localized integer-order elliptic bootstrap on one fixed half ball. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_half_open_integer_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (n : ℕ) (c : S) (u : T) (hu : MemSobolev 1 2 u)
    (hsource : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u - u - M c u)))
    (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2)) :
    MemSobolev ((n : ℝ) + 2) 2 (M φ u) := by
  obtain ⟨t, ht, hbound⟩ := hc.exists_forall_le'
    continuous_norm.neg.continuousOn (a := -(1 / 2 : ℝ)) (by
      intro x hx
      have h : ‖x‖ < (1 / 2 : ℝ) := by
        simpa only [mem_ball, dist_zero_right] using hs hx
      change -(1 / 2 : ℝ) < -‖x‖
      linarith)
  let r : ℝ := max (-t) (1 / 4)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hrh : r < 1 / 2 := max_lt (by linarith) (by norm_num)
  have hrs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r := by
    intro x hx
    have hb := hbound x hx
    change t ≤ -‖x‖ at hb
    have hn : ‖x‖ ≤ -t := by linarith
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using hn.trans (le_max_left (-t) (1 / 4)))
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_half_nested_cutoffs r hr hrh φ hc hrs
  have hF (k : ℕ) := hsource (ψ k) (hsupp k).1 (hsupp k).2
  have hreg : ∀ k : ℕ, k ≤ n + 1 → ∀ j : ℕ,
      MemSobolev ((k : ℝ) + 1) 2 (M (ψ j) u) := by
    intro k
    induction k with
    | zero =>
      intro _ j
      simpa only [Nat.cast_zero, zero_add, Nat.cast_one] using
        scalar_memSobolev_schwartz_multiplier 1 (ψ j) u (by simpa using hu)
    | succ k ih =>
      intro hk j
      have houter := ih (by omega) (j + 1)
      have hforcing : MemSobolev (k : ℝ) 2
          (M (ψ j) (scalarPerturbedOperator a b u - u - M c u)) :=
        (hF j).mono (by exact_mod_cast (show k ≤ n by omega))
      have hg := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
        c (ψ j) (ψ (j + 1)) (hnest j) k u
        (by simpa only [Nat.cast_add, Nat.cast_one] using houter) hforcing
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hg
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, hψ] using
    hreg (n + 1) (le_refl _) 0

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarIterationRegularity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed local elliptic operator gains two derivatives at every step of
its inhomogeneous resolvent chain. The estimates stay on one open ball. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_iterate_open_integer_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (κ : ℂ) (u : ℕ → T)
    (hu : ∀ k, MemSobolev 1 2 (u k))
    (heq : ∀ k (ψ : S), HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2) →
      (scalarPerturbedOperator a b (u (k + 1)) - u (k + 1) - M c (u (k + 1))) ψ =
        κ * u k ψ)
    (n : ℕ) (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2)) :
    MemSobolev ((2 * n + 1 : ℕ) : ℝ) 2 (M φ (u n)) := by
  induction n generalizing φ with
  | zero =>
      simpa only [Nat.mul_zero, zero_add, Nat.cast_one] using
        scalar_memSobolev_schwartz_multiplier 1 φ (u 0) (by simpa only [Nat.cast_one] using hu 0)
  | succ n ih =>
      have hf (ψ : S) (hψc : HasCompactSupport (ψ : V → ℂ))
          (hψs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) :
          MemSobolev ((2 * n + 1 : ℕ) : ℝ) 2
            (M ψ (scalarPerturbedOperator a b (u (n + 1)) - u (n + 1) - M c (u (n + 1)))) := by
        have he : M ψ (scalarPerturbedOperator a b (u (n + 1)) - u (n + 1) - M c (u (n + 1))) =
            M ψ (κ • u n) :=
          scalar_localize_eq_of_tests (ball 0 (1 / 2)) _ (κ • u n)
            (fun η hηc hηs => heq n η hηc hηs) ψ hψc hψs
        rw [he, map_smul]
        exact (ih ψ hψc hψs).smul κ
      have hg := scalar_half_open_integer_forcing_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
        (2 * n + 1) c (u (n + 1)) (hu (n + 1)) hf φ hc hs
      convert hg using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarL2EllipticGain
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual local elliptic gain with merely L2 forcing. The smooth
zeroth-order coefficient is handled as a multiplier of the unknown. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_ball_L2_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u : T) (f : V → ℂ)
    (hf : MemLp f 2 (volume : Measure V))
    (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = ∫ x, ψ x * f x)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    MemSobolev 2 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hc hs
  have houter : MemSobolev 1 2 (M (ψ 1) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ 1) u
      (by simpa only [Nat.cast_one] using hu)
  have hsource : MemSobolev 0 2
      (M (ψ 0) (scalarPerturbedOperator a b u - u - M c u)) :=
    scalar_localize_memSobolev_zero_of_L2_source (ball 0 1) _ f htest
      (ψ 0) (hsupp 0).1 (hsupp 0).2
      (MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [mul_comm])
        ((ψ 0).memLp ∞ (volume : Measure V) |>.mul hf))
  have hgain := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c (ψ 0) (ψ 1) (hnest 0) 0 u (by simpa using houter) (by simpa using hsource)
  simpa only [hψ, zero_add, Nat.cast_ofNat] using hgain

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Smooth H2 approximation with strong L4 convergence of first derivatives.
This is the convergence required by the quadratic terms in the nonlinear
Hessian chain rule in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_2
theorem scalarSchwartzBesselInverse_first (f : S) (i : Fin 4) :
    (D i (scalarSchwartzBesselInverse f)).toLp 2 volume =
      scalarBesselFirstL2 i (f.toLp 2 volume) := by
  apply scalarL2_distribution_injective
  dsimp only
  rw [scalarBesselFirstL2_distribution, ← scalarSchwartzBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact (lineDerivOp_toTemperedDistributionCLM_eq _ _).symm

theorem scalarSchwartzBesselInverse_second (f : S) (i j : Fin 4) :
    (D i (D j (scalarSchwartzBesselInverse f))).toLp 2 volume =
      scalarBesselSecondL2 i j (f.toLp 2 volume) := by
  apply scalarL2_distribution_injective
  dsimp only
  rw [scalarBesselSecondL2_distribution, ← scalarSchwartzBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  simp only [scalarCoordinateDerivative]
  rw [lineDerivOp_toTemperedDistributionCLM_eq, lineDerivOp_toTemperedDistributionCLM_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite distributional jets characterize integer Sobolev regularity.
This closes the higher nonlinear chain rules after their L2 product limits. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

/-- Only the finitely many coordinate derivatives through order n are needed. -/
theorem scalar_memSobolev_of_coordinate_jets (n : ℕ) (u : T)
    (hj : ∀ is : List (Fin 4), is.length ≤ n → ∃ v : L2, scalarCoordinateJet is u = (v : T)) :
    MemSobolev (n : ℝ) 2 u := by
  induction n generalizing u with
  | zero =>
    obtain ⟨v, hv⟩ := hj [] (by simp)
    simpa only [Nat.cast_zero, scalarCoordinateJet_nil] using memSobolev_zero_iff.mpr ⟨v, hv⟩
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, scalar_memSobolev_succ_iff]
    refine ⟨ih u (fun is hs => hj is (by omega)), fun i => ?_⟩
    apply ih
    intro is hs
    obtain ⟨v, hv⟩ := hj (is ++ [i]) (by simp; omega)
    refine ⟨v, ?_⟩
    simpa only [scalarCoordinateJet_append, scalarCoordinateJet_cons, scalarCoordinateJet_nil] using hv

/-- Strong L2 limits of every finite jet remain the actual derivatives of the
value limit and yield integer Sobolev regularity. -/
theorem scalar_integer_jets_closed (n : ℕ) (u : L2) (fs : ℕ → L2)
    (G : List (Fin 4) → L2) (Gs : List (Fin 4) → ℕ → L2)
    (hvalue : Tendsto fs atTop (𝓝 u))
    (hG : ∀ is, is.length ≤ n → Tendsto (Gs is) atTop (𝓝 (G is)))
    (hjets : ∀ is, is.length ≤ n → ∀ k,
      scalarCoordinateJet is (fs k : T) = (Gs is k : T)) :
    MemSobolev (n : ℝ) 2 (u : T) := by
  apply scalar_memSobolev_of_coordinate_jets
  intro is hs
  refine ⟨G is, ?_⟩
  have hleft := (scalarCoordinateJet is).continuous.continuousAt.tendsto.comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp hvalue)
  have hright := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp (hG is hs)
  have hl : Tendsto (fun k => (Gs is k : T)) atTop (𝓝 (scalarCoordinateJet is (u : T))) := by
    simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply, hjets is hs] using hleft
  have hr : Tendsto (fun k => (Gs is k : T)) atTop (𝓝 (G is : T)) := by
    simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply] using hright
  exact tendsto_nhds_unique hl hr

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite signed Gram expansion of the four transport amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_smul_right (a : ℝ) (A B : HeatMat6) :
    heatSignedGram A (a • B) = a * heatSignedGram A B := by
  simp [heatSignedGram, Matrix.trace_smul]

theorem heatSignedGram_comm (A B : HeatMat6) : heatSignedGram A B = heatSignedGram B A := by
  unfold heatSignedGram
  calc
    _ = ((twoFormHodgeMatrix * (Aᵀ * B))ᵀ).trace := (Matrix.trace_transpose _).symm
    _ = ((Bᵀ * A) * twoFormHodgeMatrix).trace := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        heat_hodgeMatrix_symmetric]
    _ = _ := Matrix.trace_mul_comm _ _

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Exact normal-coordinate pairing of the actual normalized heat columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_columns (A : HeatMat6) :
    heatSignedGram A A = ∑ l, ∑ m, twoFormHodgeMatrix l m *
      inner ℝ (WithLp.toLp 2 (fun k => A k l) : TwoFormFour) (WithLp.toLp 2 (fun k => A k m)) := by
  simp only [heatSignedGram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The proved signature integral in the original metric-volume convention.
The numerical Hausdorff normalization is displayed, not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem riemannianChartFactor_toReal_pos : 0 < riemannianChartFactor.toReal := by
  rw [riemannianChartFactor, ENNReal.toReal_mul]
  apply mul_pos
  · rw [ENNReal.toReal_ofReal (by positivity)]
    positivity
  · exact_mod_cast euclideanHausdorffFactor_pos

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiKernelPowers
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive scalar path weights bound the noncommuting curvature kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

def curvatureKernel {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  scalarLift G * Matrix.blockDiagonal R

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_JacobiSymmetricKernel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric realization of the positive Green-kernel perturbation. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

def symmetricCurvatureKernel {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (R : Fin N → NormalMatrix) : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  scalarLift S * Matrix.blockDiagonal R * scalarLift S

end
end PositiveEinsteinFour.Jacobi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A unit Weyl norm forces parallel Weyl curvature and maximal normalized
determinant. The proof differentiates its actual constant norm twice. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section

theorem matrixPairing_swap (A B : Mat) : matrixPairing A B = matrixPairing B A := by
  simp only [matrixPairing, mul_comm]

theorem hasDerivAt_pairing {A B : ℝ → Mat} {A' B' : Mat} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => matrixPairing (A s) (B s))
      (matrixPairing A' (B t) + matrixPairing (A t) B') t := by
  simpa only [inner_matrixVector, add_comm] using
    (hasDerivAt_matrixVector hA).inner ℝ (hasDerivAt_matrixVector hB)

theorem constant_matrix_norm_pairing {A : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hA : HasDerivAt A Z t) (hnorm : ∀ s, normalizedBlockNorm (A s) = 1) :
    matrixPairing (A t) Z = 0 := by
  have hd := hasDerivAt_pairing hA hA
  have he : (fun s => matrixPairing (A s) (A s)) = fun _ => (6 : ℝ) := by
    funext s
    rw [matrixPairing_self_norm, hnorm s]
    norm_num
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (6 : ℝ))
  rw [matrixPairing_swap Z (A t)] at hz
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! A symmetric projection of trace one is determined by a unit vector
in its image. This will identify the actual parallel Weyl block. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix
open scoped BigOperators
noncomputable section

theorem symmetric_projection_trace_one (P : Mat) (hs : symmetric P)
    (hp : P * P = P) (ht : Matrix.trace P = 1)
    (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) (hPv : P *ᵥ v = v) :
    P = Matrix.vecMulVec v v := by
  let Q := Matrix.vecMulVec v v
  have hPt : Pᵀ = P := by ext i j; exact hs j i
  have hQt : Qᵀ = Q := by
    ext i j
    exact mul_comm _ _
  have hPQ : P * Q = Q := by
    dsimp only [Q]
    rw [Matrix.mul_vecMulVec, hPv]
  have hQP : Q * P = Q := by
    have h := congrArg Matrix.transpose hPQ
    simpa only [Matrix.transpose_mul, hPt, hQt] using h
  have hQQ : Q * Q = Q := by
    dsimp only [Q]
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  have hD : (P - Q) * (P - Q) = P - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hp, hPQ, hQP, hQQ, sub_self,
      sub_zero]
  have hsD : symmetric (P - Q) := by
    intro i j
    change P i j - v i * v j = P j i - v j * v i
    rw [hs i j, mul_comm (v i)]
  have htD : Matrix.trace (P - Q) = 0 := by
    rw [Matrix.trace_sub, ht]
    dsimp only [Q]
    rw [Matrix.trace_vecMulVec, hv, sub_self]
  have hnorm := trace_square_eq_six_norm_sq (P - Q) hsD
  rw [hD, htD] at hnorm
  have hzero : P - Q = 0 := (normalizedBlockNorm_eq_zero_iff _).mp (by nlinarith)
  exact sub_eq_zero.mp hzero

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Two bounded complex coordinate charts cover the projective cut hyperplane. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexCutLift_sub_norm (i : Fin 2) (z w : ℂ) :
    ‖complexCutLift i z-complexCutLift i w‖ = ‖z-w‖ := by
  have heq : complexCutLift i z-complexCutLift i w =
      EuclideanSpace.single (if i = 0 then 2 else 1) (z-w) := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [complexCutLift]
  rw [heq]
  simp

theorem complexCutPoint_distance_le (i : Fin 2) (z w : ℂ) :
    fubiniStudyDistance (complexCutPoint i z) (complexCutPoint i w) ≤ Real.pi * ‖z-w‖ := by
  let p := complexNormalize (complexCutLift i z) (complexCutLift_ne_zero i z)
  let q := complexNormalize (complexCutLift i w) (complexCutLift_ne_zero i w)
  have hp : complexSphereProjection p = complexCutPoint i z := complexNormalize_projection _ _
  have hq : complexSphereProjection q = complexCutPoint i w := complexNormalize_projection _ _
  rw [← hp,← hq]
  have hb := fubiniStudyDistance_unit_le_chord p q
  have hn : ‖p.val-q.val‖ ≤ 2*‖z-w‖ := by
    exact (complex_normalization_distance_le _ _ (complexCutLift_norm_ge_one i z)
      (complexCutLift_norm_ge_one i w)).trans_eq (by rw [complexCutLift_sub_norm])
  exact hb.trans ((mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ Real.pi/2)).trans_eq (by ring))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


