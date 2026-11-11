-- Prove2me | Definitions.Def_OAIQ237Ny004
-- name    : OAIQ237Ny004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:59.326018+00:00
-- url     : https://prove2.me/theorems/1e1a8063-9bcb-443e-a99b-62bc95ef4198
-- title:
--   Definitions bundle OAIQ237Ny004 of the split of OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 148 declarations of OpenAI's Lean: 111 definitions, 1 inductive type or structure and 36 theorems. The definitions and types are `OAI.Yau.Target.SphereNodalStage`, `OAI.Yau.Target.SphereStageExtension`, `OAI.Yau.Target.SphereWeightedL2`, `OAI.Yau.Target.ambientWeightedChartOperator`, `OAI.Yau.Target.ambientWeightedMetric`, `OAI.Yau.Target.baseChartFlux`, `OAI.Yau.Target.coefficientPrincipalEntry`, `OAI.Yau.Target.exteriorCorrectedEquationLocalInst7`, `OAI.Yau.Target.exteriorCorrectedEquationLocalInst8`, `OAI.Yau.Target.exteriorCorrectedEquationLocalInst9`, `OAI.Yau.Target.independentAmbientMetric`, `OAI.Yau.Target.intrinsicCorrectedChartLocalInst8`, `OAI.Yau.Target.intrinsicCorrectedChartLocalInst9`, `OAI.Yau.Target.intrinsicCorrectionResidual`, `OAI.Yau.Target.intrinsicDivergencePotential`, `OAI.Yau.Target.intrinsicDivergencePrincipal`, `OAI.Yau.Target.intrinsicRealCorrectionResidual`, `OAI.Yau.Target.intrinsicRealPotential`, `OAI.Yau.Target.intrinsicSeedCoordMetric`, `OAI.Yau.Target.intrinsicWeightedChartOperator`, `OAI.Yau.Target.intrinsicWeightedMetric`, `OAI.Yau.Target.perturbedNodalTransferLocalInst7`, `OAI.Yau.Target.perturbedNodalTransferLocalInst8`, `OAI.Yau.Target.perturbedNodalTransferLocalInst9`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst1`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst10`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst13`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst15`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst16`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst2`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst3`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst4`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst7`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst8`, `OAI.Yau.Target.positiveSphereCorrectionLocalInst9`, `OAI.Yau.Target.roundCoordFactor`, `OAI.Yau.Target.roundCoordGradient`, `OAI.Yau.Target.roundCorrectionDenominator`, `OAI.Yau.Target.roundCotangentTensor`, `OAI.Yau.Target.roundMetricJet` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `NodalSets_Charts_BaseChartFlux`, `NodalSets_Charts_IndependentAmbientMetric`, `NodalSets_Charts_IntrinsicCorrectedChart`, `NodalSets_Charts_RoundChartConnection`, `NodalSets_Charts_RoundCotangentSmooth`, `NodalSets_Charts_RoundCotangentTensor`, `NodalSets_Charts_RoundSphereEnergyData`, `NodalSets_Charts_SeedChartPrincipal`, `NodalSets_Charts_SeedMetricNeighborhood`, `NodalSets_Charts_SimplicityEnergyDensity`, `NodalSets_Charts_SphereChartCutoffApproximation`, `NodalSets_Charts_SphereChartDerivativeMap`, `NodalSets_Charts_SphereChartDivergenceData`, `NodalSets_Charts_SphereChartFluxL2`, `NodalSets_Charts_SphereChartScalarExtension`, `NodalSets_Charts_SphereChartTangentTrace`, `NodalSets_Charts_SphereChartTestFlux`, `NodalSets_Charts_SphereChartValueMap`, `NodalSets_Charts_SphereDifferenceTestMaps`, `NodalSets_Charts_SphereEnergyCompletion`, `NodalSets_Charts_SphereEnergyForm`, `NodalSets_Charts_SphereEnergyL2Map`, `NodalSets_Charts_SphereL2LocalPullback`, `NodalSets_Charts_SphereReferenceMeasureInvariance`, `NodalSets_Charts_SphereSimplicitySquare`, `NodalSets_Charts_SphereSmoothGreenLocal`, `NodalSets_Charts_SphereSmoothL2Density`, `NodalSets_Charts_SphereTransitionFlux`, `NodalSets_Charts_SphereTransitionScalar`, `NodalSets_Charts_SphereWeightedChartL2`, `NodalSets_Charts_SphereWeightedL2`, `NodalSets_Charts_SupportedFiniteAtlasBounds`, `NodalSets_Charts_TargetWarpedMetric`, `NodalSets_Coefficients_CoordinateCorrection`, `NodalSets_Coefficients_GlobalCorrection`, `NodalSets_Coefficients_IntrinsicCorrectionResidual`, `NodalSets_Coefficients_IntrinsicDivergenceCoefficients`, `NodalSets_Coefficients_IntrinsicRealCorrection`, `NodalSets_Coefficients_PositiveSphereCorrection`, `NodalSets_Coefficients_RoundCoefficientJets`, `NodalSets_Coefficients_RoundCorrectionDenominator`, `NodalSets_Coefficients_SphereCoefficientScalarBounds`, `NodalSets_Elliptic_ExteriorCorrectedEquation`, `NodalSets_Elliptic_IntrinsicRealCoordinates`, `NodalSets_Elliptic_IntrinsicRoundPerturbation`, `NodalSets_Elliptic_IntrinsicSeedPatch`, `NodalSets_Elliptic_IntrinsicWeightedLift`, `NodalSets_Elliptic_RealCoordinateEllipticLemmas`, `NodalSets_Elliptic_RealInteriorWeakAddLemmas`, `NodalSets_Elliptic_RealSquareCutoffWeakGradient`, `NodalSets_Elliptic_RealTransportDerivatives`, `NodalSets_Elliptic_RealWeakSecondCommutator`, `NodalSets_Elliptic_RealWeakSecondForcing`, `NodalSets_Elliptic_RealWeightedTransport`, `NodalSets_Elliptic_RoundCoordinateGradient`, `NodalSets_Elliptic_SeedCoordAdmissibility`, `NodalSets_Elliptic_SeedCoordinateField`, `NodalSets_Elliptic_SeedDeviationCoordinates`, `NodalSets_Elliptic_SeedLogExtension`, `NodalSets_Elliptic_SeedRoundPatch`, `NodalSets_Elliptic_SimplicityCoordinateEnergy`, `NodalSets_Elliptic_TargetWarpedComparison`, `NodalSets_Elliptic_WeightedLift`, `NodalSets_Hausdorff_PerturbedNodalTransfer`, `NodalSets_SmoothLimit_SphereIterationInterface`, `NodalSets_SmoothLimit_SphereSummableSmoothPair`, `NodalSets_Spectral_SphereEigenResolventForcing`, `NodalSets_Spectral_SphereIndexedRayleigh`, `NodalSets_Spectral_SphereRayleighQuotient`, `NodalSets_Spectral_SphereWeakResolvent`.
--
--   **Imports.** It imports the published bundle `Def_YauCounterexample`; the bundles `OAIQ237Ny002` and `OAIQ237Ny003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Yau.Target.PlacedEnvelopeData.seeded_residual_of_seed_support`, `OAI.Yau.Target.corrected_exterior_equation`, `OAI.Yau.Target.exists_sphere_simplicity_kernel_form`, `OAI.Yau.Target.independentAmbientMetric_circle_laplacian`, `OAI.Yau.Target.intrinsic_noncritical_placed_data`, `OAI.Yau.Target.intrinsic_one_step`, `OAI.Yau.Target.intrinsic_packed_global_sphere_stage`, `OAI.Yau.Target.intrinsic_packed_positive_sphere_stage`, `OAI.Yau.Target.intrinsic_packed_selected_stage`, `OAI.Yau.Target.intrinsic_packed_small_corrected_stage`, `OAI.Yau.Target.intrinsic_placed_total_residual`, `OAI.Yau.Target.sphereChartTransition_divergence`, `OAI.Yau.Target.sphereL2Resolvent_compact`, `OAI.Yau.Target.sphere_affine_kernel_implies_simplicity`, `OAI.Yau.Target.sphere_eigen_all_finite_weak_jets`, `OAI.Yau.Target.sphere_eigen_differentiated_equation`, `OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness`, `OAI.Yau.Target.sphere_eigen_global_representative`, `OAI.Yau.Target.sphere_eigen_hessian_localized_energy`, `OAI.Yau.Target.sphere_eigen_interior_fourth_weak_derivatives`, `OAI.Yau.Target.sphere_finite_norm_C1_intrinsic_limit`, `OAI.Yau.Target.sphere_finite_norm_indexed_compactness`, `OAI.Yau.Target.sphere_finite_norm_indexed_eigenvalue_continuity`, `OAI.Yau.Target.sphere_finite_norm_simple_oriented_persistence`, `OAI.Yau.Target.sphere_finite_norm_simple_uniform_persistence`, `OAI.Yau.Target.sphere_finite_weak_jet_iteration`, `OAI.Yau.Target.sphere_interior_localized_energy`, `OAI.Yau.Target.sphere_normalized_global_limit`, `OAI.Yau.Target.sphere_reference_literal_nodal_persistence`, `OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal`, `OAI.Yau.Target.sphere_resolvent_finite_smooth_frame`, `OAI.Yau.Target.sphere_resolvent_finite_variational_frame`, `OAI.Yau.Target.sphere_resolvent_interior_gradient_difference_bound`, `OAI.Yau.Target.sphere_same_second_differentiated_equation`, `OAI.Yau.Target.sphere_same_third_difference_bound`, `OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood`, `OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer` and `OAI.Yau.Target.uniform_small_correction_nodal_transfer`; the proofs of `OAI.Yau.Geometry.real_compact_interior_pointwise`, `OAI.Yau.Geometry.real_global_unique_continuation`, `OAI.Yau.Target.PlacedEnvelopeData.seeded_residual_of_seed_support`, `OAI.Yau.Target.corrected_exterior_equation`, `OAI.Yau.Target.exists_sphere_simplicity_kernel_form`, `OAI.Yau.Target.independentAmbientMetric_circle_laplacian`, `OAI.Yau.Target.intrinsic_noncritical_placed_data`, `OAI.Yau.Target.intrinsic_one_step`, `OAI.Yau.Target.intrinsic_packed_global_sphere_stage`, `OAI.Yau.Target.intrinsic_packed_positive_sphere_stage`, `OAI.Yau.Target.intrinsic_packed_selected_stage`, `OAI.Yau.Target.intrinsic_packed_small_corrected_stage`, `OAI.Yau.Target.intrinsic_placed_total_residual`, `OAI.Yau.Target.seed_envelope_coordinate_patch`, `OAI.Yau.Target.sphereChartTransition_divergence`, `OAI.Yau.Target.sphereL2Resolvent_compact`, `OAI.Yau.Target.sphere_affine_kernel_implies_simplicity`, `OAI.Yau.Target.sphere_eigen_all_finite_weak_jets`, `OAI.Yau.Target.sphere_eigen_differentiated_equation`, `OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness`, `OAI.Yau.Target.sphere_eigen_global_representative`, `OAI.Yau.Target.sphere_eigen_hessian_localized_energy`, `OAI.Yau.Target.sphere_eigen_interior_fourth_weak_derivatives`, `OAI.Yau.Target.sphere_finite_norm_C1_intrinsic_limit`, `OAI.Yau.Target.sphere_finite_norm_indexed_compactness`, `OAI.Yau.Target.sphere_finite_norm_indexed_eigenvalue_continuity`, `OAI.Yau.Target.sphere_finite_norm_simple_oriented_persistence`, `OAI.Yau.Target.sphere_finite_norm_simple_uniform_persistence`, `OAI.Yau.Target.sphere_finite_weak_jet_iteration`, `OAI.Yau.Target.sphere_interior_localized_energy`, `OAI.Yau.Target.sphere_normalized_global_limit`, `OAI.Yau.Target.sphere_reference_literal_nodal_persistence`, `OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal`, `OAI.Yau.Target.sphere_resolvent_finite_smooth_frame`, `OAI.Yau.Target.sphere_resolvent_finite_variational_frame`, `OAI.Yau.Target.sphere_resolvent_interior_gradient_difference_bound`, `OAI.Yau.Target.sphere_same_second_differentiated_equation`, `OAI.Yau.Target.sphere_same_third_difference_bound`, `OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood`, `OAI.Yau.Target.uniform_intrinsic_coefficient_nodal_transfer`, `OAI.Yau.Target.uniform_small_correction_nodal_transfer` and `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny002
import Definitions.Def_OAIQ237Ny003

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetWarpedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

variable (B : Base → AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ)
    (hB : ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v)
    (q : Base → ℝ) (hq : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ q) (hpos : ∀ x, 0 < q x)

def ambientWeightedMetric : SmoothMetric :=
  immersionMetric targetEmbedding targetEmbedding_smooth targetEmbedding_immersion
    (fun x ↦ warpedAmbientForm (B x.1) (q x.1))
    (warpedAmbientForm_smooth _ _ (hB.comp contMDiff_fst) (hq.comp contMDiff_fst))
    (fun x ↦ warpedAmbientForm_symm _ _ (hs x.1))
    (fun x ↦ warpedAmbientForm_pos _ (hp x.1) (hpos x.1))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IndependentAmbientMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

def independentAmbientMetric : SmoothMetric :=
  ambientWeightedMetric
    (fun x ↦ ambientMatrixForm (weightedBaseMatrix (A x) (rho x)))
    (ambientWeightedBase_smooth A rho hA hp hr)
    (fun x ↦ ambientMatrixForm_symm _ (weightedBaseMatrix_posDef (hp x) (hrp x)).1)
    (fun x ↦ ambientMatrixForm_pos _ (weightedBaseMatrix_posDef (hp x) (hrp x)))
    (fun x ↦ ambientCircleWeight (A x) (rho x))
    (ambientCircleWeight_smooth A rho hA hp hr hrp)
    (fun x ↦ ambientCircleWeight_pos _ (hp x) (hrp x))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_BaseChartFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def baseChartFlux (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (f : Base → ℝ) (p : Base) (i : Fin 4) (z : BaseModel) : ℝ :=
  baseChartDensity rho p z * ∑ j, (baseChartMetric A rho p z)⁻¹ i j *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ j)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section

def roundTensorFlux (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (f : Base → ℝ) (p : Base) (i : Fin 4) (z : BaseModel) : ℝ :=
  roundChartDensity p z * ∑ j, sphereChartTensor A p z i j *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ j)

def ambientWeightedChartOperator (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (rho : Base → ℝ) (f : Base → ℝ) (p : Base) (z : BaseModel) : ℝ :=
  (rho ((extChartAt (𝓡 4) p).symm z))⁻¹ * (roundChartDensity p z)⁻¹ *
    ∑ i, fderiv ℝ (roundTensorFlux A f p i) z (EuclideanSpace.basisFun (Fin 4) ℝ i)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TargetWarpedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def roundProductMetric : SmoothMetric :=
  ambientWeightedMetric (fun _ ↦ innerSL ℝ) contMDiff_const
    (fun _ v w ↦ by change @inner ℝ AmbientBase _ v w = @inner ℝ AmbientBase _ w v; exact real_inner_comm w v)
    (fun _ v hv ↦ by
      change 0 < @inner ℝ AmbientBase _ v v
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hv))
    (fun _ ↦ 1) contMDiff_const (fun _ ↦ zero_lt_one)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicWeightedLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)

def intrinsicWeightedMetric : SmoothMetric :=
  independentAmbientMetric (intrinsicAmbientMatrix A) rho
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp) hr hrp

def intrinsicWeightedChartOperator (f : Base → ℝ) (p : Base) (z : BaseModel) : ℝ :=
  (rho ((extChartAt (𝓡 4) p).symm z))⁻¹ * (roundChartDensity p z)⁻¹ *
    ∑ i, fderiv ℝ (intrinsicRoundFlux A f p i) z (EuclideanSpace.basisFun (Fin 4) ℝ i)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundChartConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_5_r297a3e_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
lemma roundChartMetric_apply (p : Base) (y u v : BaseModel) :
    roundChartMetric p y u v = ⟪sphereChartDerivative p y u,sphereChartDerivative p y v⟫ := rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def seedRoundAdmissible (y : BaseModel) : Prop :=
  let g := roundChartMetric seedPoint
  let p := localMetricGradient g seedRealChart y
  let H := localMetricHessian g seedRealChart y
  p ≠ 0 ∧ ∃ t : BaseModel, g y p t = 0 ∧ g y t t = 1 ∧
    0 < H p p + (g y p p+4)*H t t

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedMetricNeighborhood
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def roundMetricJet (y : BaseModel) : MetricJet BaseModel :=
  (roundChartMetric seedPoint y,fderiv ℝ (roundChartMetric seedPoint) y)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCoefficientJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundChartMetric_positive (y : BaseModel) (v : BaseModel) (hv : v ≠ 0) :
    0 < roundChartMetric seedPoint y v v := by
  rw [roundChartMetric_apply]
  apply real_inner_self_pos.mpr
  intro he
  apply hv
  apply sphereChartDerivative_injective seedPoint (by rw [centeredSphereChart_target]; trivial)
  simpa using he

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordAdmissibility
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

def seedCoordMetric (c : BaseModel → CoefficientPoint BaseModel) :
    _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ :=
  linearMetricField seedCoordEquiv (coefficientMetricValue ∘ c)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicSeedPatch
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

def intrinsicSeedCoordMetric (A : IntrinsicTensor) (ρ : Base → ℝ) :
    _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ :=
  linearMetricField seedCoordEquiv
    (fun z ↦ matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ seedPoint z))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

def seedCoordImag : _root_.OAI.Yau.Jets.Coord → ℝ := seedImagChart ∘ seedCoordEquiv

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordinateField
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section

def seedCoordinateField (N : ℕ) : _root_.OAI.Yau.Jets.Coord → ℝ :=
  ambientRealSeed N ∘ seedChartAmbient ∘ seedCoordEquiv

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentTensor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst2
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst3
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst4
def sphereRoundMusical (x : Base) : TangentSpace (𝓡 4) x ≃L[ℝ] SphereCotangent x :=
  positiveMetricEquiv (sphereRoundForm x) (sphereRoundForm_pos x)

attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst1
def sphereCotangentRepresentative (x : Base) : SphereCotangent x →L[ℝ] AmbientBase :=
  (sphereAmbientDerivative x).comp (sphereRoundMusical x).symm.toContinuousLinearMap

lemma sphereCotangentRepresentative_pair (x : Base) (ell : SphereCotangent x)
    (v : TangentSpace (𝓡 4) x) :
    ⟪sphereCotangentRepresentative x ell,sphereAmbientDerivative x v⟫ = ell v := by
  exact congrArg (fun L : SphereCotangent x ↦ L v) ((sphereRoundMusical x).apply_symm_apply ell)

lemma sphereCotangentRepresentative_restriction (x : Base) (ell : SphereCotangent x) :
    sphereCovectorRestriction x (sphereCotangentRepresentative x ell) = ell := by
  ext v
  exact sphereCotangentRepresentative_pair x ell v

def roundCotangentTensor : IntrinsicTensor := fun x ↦
  bilinearPullback (innerSL ℝ) (sphereCotangentRepresentative x)

lemma roundCotangentTensor_apply (x : Base) (v w : SphereCotangent x) :
    roundCotangentTensor x v w =
      ⟪sphereCotangentRepresentative x v,sphereCotangentRepresentative x w⟫ := rfl

lemma roundCotangentTensor_symm (x : Base) (v w : SphereCotangent x) :
    roundCotangentTensor x v w = roundCotangentTensor x w v := by
  simp only [roundCotangentTensor_apply]
  exact real_inner_comm _ _

lemma roundCotangentTensor_pos (x : Base) (v : SphereCotangent x) (hv : v ≠ 0) :
    0 < roundCotangentTensor x v v := by
  rw [roundCotangentTensor_apply]
  apply real_inner_self_pos.mpr
  intro h
  have hh := sphereCotangentRepresentative_restriction x v
  rw [h,map_zero] at hh
  exact hv hh.symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentSmooth
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.roundCotangentSmoothLocalInst1
attribute [local instance] OAI.Yau.Target.roundCotangentSmoothLocalInst2
attribute [local instance] OAI.Yau.Target.roundCotangentSmoothLocalInst3
local instance roundCotangentSmoothLocalInst4_r297a3e_1 (x : Base) : FiniteDimensional ℝ (TangentSpace (𝓡 4) x) := inferInstanceAs (FiniteDimensional ℝ BaseModel)
lemma sphereRoundMusical_smooth :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,BaseModel →L[ℝ] CotangentModel)) ∞
      (fun x ↦ TotalSpace.mk' (BaseModel →L[ℝ] CotangentModel)
        (E := fun x ↦ TangentSpace (𝓡 4) x →L[ℝ] SphereCotangent x) x
        (sphereRoundMusical x).toContinuousLinearMap) := by
  exact smooth_bilinear_pullback (fun _ ↦ innerSL ℝ) sphereAmbientDerivative contMDiff_const
    (smooth_ambient_derivative (Subtype.val : Base → AmbientBase) (contMDiff_coe_sphere (n := 4)))

lemma sphereRoundMusical_inverse_smooth :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel →L[ℝ] BaseModel)) ∞
      (fun x ↦ TotalSpace.mk' (CotangentModel →L[ℝ] BaseModel)
        (E := fun x ↦ SphereCotangent x →L[ℝ] TangentSpace (𝓡 4) x) x
        (sphereRoundMusical x).symm.toContinuousLinearMap) :=
  smooth_bundle_inverse sphereRoundMusical sphereRoundMusical_smooth

local instance localInst_r297a3e_1 : ContinuousSMul ℝ AmbientBase := IsBoundedSMul.continuousSMul
lemma sphereCotangentRepresentative_smooth :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel →L[ℝ] AmbientBase)) ∞
      (fun x ↦ TotalSpace.mk' (CotangentModel →L[ℝ] AmbientBase)
        (E := fun x ↦ SphereCotangent x →L[ℝ] Bundle.Trivial Base AmbientBase x) x
        (sphereCotangentRepresentative x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have ht := ((contMDiffAt_hom_bundle _).mp (sphereRoundMusical_inverse_smooth x)).2
  have hd := ((contMDiffAt_hom_bundle _).mp
    (smooth_ambient_derivative (Subtype.val : Base → AmbientBase)
      (contMDiff_coe_sphere (n := 4)) x)).2
  change ContMDiffAt (𝓡 4) 𝓘(ℝ,BaseModel →L[ℝ] AmbientBase) ∞
    (fun y ↦ inCoordinates BaseModel (TangentSpace (𝓡 4)) AmbientBase
      (Bundle.Trivial Base AmbientBase) x y x y (sphereAmbientDerivative y)) x at hd
  apply (hd.clm_comp ht).congr_of_eventuallyEq
  filter_upwards [(trivializationAt BaseModel (TangentSpace (𝓡 4)) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt BaseModel (TangentSpace (𝓡 4)) x),
    (trivializationAt CotangentModel SphereCotangent x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt CotangentModel SphereCotangent x)] with y hy hz
  have hw : y ∈ (trivializationAt AmbientBase (Bundle.Trivial Base AmbientBase) x).baseSet := Set.mem_univ y
  simp only [inCoordinates_eq hy hw,inCoordinates_eq hz hy,inCoordinates_eq hz hw]
  apply ContinuousLinearMap.ext
  intro v
  let e := (trivializationAt BaseModel (TangentSpace (𝓡 4)) x).continuousLinearEquivAt ℝ y hy
  let u : TangentSpace (𝓡 4) y := (sphereRoundMusical y).symm
    ((trivializationAt CotangentModel SphereCotangent x).symm y v)
  change sphereAmbientDerivative y u = sphereAmbientDerivative y (e.symm (e u))
  exact congrArg (sphereAmbientDerivative y) (e.symm_apply_apply u).symm

lemma roundCotangentTensor_smooth : IntrinsicTensorSmooth roundCotangentTensor := by
  exact smooth_bilinear_pullback (fun _ ↦ innerSL ℝ) sphereCotangentRepresentative
    contMDiff_const sphereCotangentRepresentative_smooth

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold Matrix Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst1
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst2
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst9
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst10
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst11
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst12
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst13
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst14
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst15
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst16
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst17
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst18
def roundTensorPerturbation (alpha : Base → ℝ) : IntrinsicTensor :=
  fun x ↦ alpha x • roundCotangentTensor x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PositiveSphereCorrection
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance positiveSphereCorrectionLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance positiveSphereCorrectionLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance positiveSphereCorrectionLocalInst5_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst6_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance positiveSphereCorrectionLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance positiveSphereCorrectionLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance
local instance positiveSphereCorrectionLocalInst12_r297a3e_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance positiveSphereCorrectionLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace

local instance positiveSphereCorrectionLocalInst14_r297a3e_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance positiveSphereCorrectionLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance positiveSphereCorrectionLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTangentTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereConformalFrame_orthonormal (p : Base) (y : BaseModel) :
    Orthonormal ℝ (sphereConformalFrame p y) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [sphereConformalFrame,Sum.elim_inl,real_inner_smul_left,
      real_inner_smul_right,sphereChartDerivative_conformal]
    rw [(EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite]
    have hd : ‖y‖^2+4 ≠ 0 := by positivity
    split_ifs <;> simp_all
    field_simp
  · change ⟪((‖y‖^2+4)/4) • sphereChartDerivative p y _,
      ((extChartAt (𝓡 4) p).symm y : AmbientBase)⟫ = 0
    rw [real_inner_smul_left,real_inner_comm,sphereChartDerivative_normal,mul_zero]
  · simp only [sphereConformalFrame,Sum.elim_inl,Sum.elim_inr,real_inner_smul_right,
      sphereChartDerivative_normal,mul_zero,Sum.inr_ne_inl,ite_false, if_false]
  · simp [sphereConformalFrame,Subsingleton.elim i j]

def sphereConformalBasis (p : Base) (y : BaseModel) :
    OrthonormalBasis (Fin 4 ⊕ Fin 1) ℝ AmbientBase :=
  OrthonormalBasis.mk (sphereConformalFrame_orthonormal p y)
    ((sphereConformalFrame_orthonormal p y).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [AmbientBase])).ge

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedChartPrincipal
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

def seedCoordWeight (rho : Base → ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) *
    roundChartDensity seedPoint (seedCoordEquiv x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedDeviationCoordinates
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Geometry Yau.Jets
open scoped Topology
noncomputable section

def seedDeviationCoordinates (K : Set Base) : Set _root_.OAI.Yau.Jets.Coord :=
  (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) ⁻¹' K

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCorrectionResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

def seedCoordDensity (rho : Base → ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x))

def intrinsicCorrectionResidual (A : IntrinsicTensor) (rho : Base → ℝ)
    (lam : ℝ) (u : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  -(seedCoordDensity rho x:ℂ) *
    realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) lam u x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoordinateCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
variable {n : ℕ}

def pairing (u : Coord n → ℝ) (V : Coord n → Coord n) (x : Coord n) : ℝ :=
  ∑ i, coordPartial u x i * V x i

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Function Set
open scoped ContDiff
variable {n : ℕ}

def correctionDenominator (u : Coord n → ℝ) (V : Coord n → Coord n)
    (lam : ℝ) (x : Coord n) : ℝ := pairing u V x + lam * u x ^ 2

def densityCorrection (gamma u f : Coord n → ℝ) (V : Coord n → Coord n)
    (lam : ℝ) (x : Coord n) : ℝ :=
  f x * u x - lam⁻¹ * weightedDiv gamma (fun y i ↦ f y * V y i) x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundCoordinateGradient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

def roundCoordFactor (x : Yau.Jets.Coord) : ℝ := ((‖seedCoordEquiv x‖^2+4)/4)^2

def roundCoordGradient (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  roundCoordFactor x * fderiv ℝ u x (Pi.single i 1)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCorrectionDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

def roundCorrectionDenominator (u : Yau.Jets.Coord → ℝ) (n : ℕ) : Yau.Jets.Coord → ℝ :=
  Yau.correctionDenominator u (roundCoordGradient u) (seedEigenvalue n)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicRealCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

def intrinsicRealCorrectionResidual (A : IntrinsicTensor) (rho : Base → ℝ)
    (lam : ℝ) (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  (intrinsicCorrectionResidual A rho lam u x).re

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicCorrectedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst7
local instance intrinsicCorrectedChartLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance intrinsicCorrectedChartLocalInst1_r297a3e_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst2_r297a3e_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst3_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst4_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst5_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst6_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicCorrectedChartLocalInst10_r297a3e_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicCorrectedChartLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasureInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureInvarianceLocal1
attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureInvarianceLocal2
lemma sphereReferenceMeasure_integral_chart (p : Base) (f : Base → ℝ) :
    (∫ z, f z ∂sphereReferenceMeasure) =
      ∫ x, roundChartDensity p (seedCoordEquiv x)*f (sphereChartCoordMap p x) := by
  rw [sphereReferenceMeasure_eq_chart p,(sphereChartCoordMap_measurableEmbedding p).integral_map]
  simp only [roundChartDensity_coord_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
    roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul]

lemma sphereReferenceMeasure_integrable_chart (p : Base) (f : Base → ℝ) :
    Integrable f sphereReferenceMeasure ↔
      Integrable (fun x ↦ roundChartDensity p (seedCoordEquiv x)*f (sphereChartCoordMap p x)) := by
  rw [sphereReferenceMeasure_eq_chart p,(sphereChartCoordMap_measurableEmbedding p).integrable_map_iff]
  simp only [roundChartDensity_coord_eq]
  rw [integrable_withDensity_iff_integrable_smul'
    roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul,Function.comp_apply]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance sphereEnergyFormLocal1_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyFormLocal2_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereEnergyDensity (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ) (p : Base) : ℝ :=
  roundTensorPerturbation a p (sphereDifferential v p) (sphereDifferential w p) - lam*b p*v p*w p

def sphereEnergyForm (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ) : ℝ :=
  ∫ p, sphereEnergyDensity a b lam v w p ∂sphereReferenceMeasure

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCoordinateEllipticLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau
open scoped ContDiff
variable {n : ℕ}

lemma real_coordPartial_mul (f g : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ f y*g y) x i =
      coordPartial f x i*g x + f x*coordPartial g x i := by
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

def realEllipticDrift (gamma : Coord n → ℝ)
    (B : Coord n → Fin n → Fin n → ℝ) (x : Coord n) (j : Fin n) : ℝ :=
  (gamma x)⁻¹ * ∑ i, coordPartial (fun y ↦ gamma y*B y i j) x i

end Yau

namespace Yau.Target
open Set
open scoped ContDiff
variable {d : ℕ}

def simplicityDensityPerturbation (gamma u zeta : Yau.Coord d → ℝ)
    (V : Yau.Coord d → Yau.Coord d) (lam : ℝ) (x : Yau.Coord d) : ℝ :=
  -lam⁻¹ * (u x * Yau.weightedDiv gamma (fun y i ↦ zeta y * V y i) x +
    2*zeta x*Yau.pairing u V x)

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRealCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def intrinsicRealPotential (rho : Base → ℝ) (lam : ℝ) (p : Base) (x : Yau.Jets.Coord) : ℝ :=
  lam*rho (sphereChartCoordMap p x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereRayleighQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

def sphereRayleighQuotient (A : IntrinsicTensor) (rho u : Base → ℝ) : ℝ :=
  sphereDirichletForm A u u / sphereWeightedPairing rho u u

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

def sphereEnergyToCompletion (d : SphereEnergyData) :
    SphereEnergySmooth d →ₗᵢ[ℝ] SphereEnergyHilbert d := UniformSpace.Completion.toComplₗᵢ

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundSphereEnergyData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Matrix Set Metric
open scoped ContDiff RealInnerProductSpace
noncomputable section

def roundSphereEnergyData : SphereEnergyData :=
  ⟨roundCotangentTensor,roundCotangentTensor_smooth,roundCotangentTensor_symm,
    roundCotangentTensor_pos,fun _ ↦ 1,continuous_const,fun _ ↦ zero_lt_one⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SimplicityEnergyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

def roundSimplicitySquare (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  roundCoordFactor x * ∑ i : Fin 4,
    (u x*Yau.coordPartial v x i-v x*Yau.coordPartial u x i)^2

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

def weightedSkewTransport (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (w : Coord n → ℝ) (x : Coord n) : ℝ :=
  2*pairing w V x + weightedDiv gamma V x*w x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTransportDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open scoped ContDiff
noncomputable section
variable {n : ℕ}

lemma real_coordPartial_add (u v : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ u y+v y) x i = coordPartial u x i+coordPartial v x i := by
  unfold coordPartial
  rw [fderiv_fun_add (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) (hv.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  rfl

lemma real_coordPartial_const_mul (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (a : ℝ) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ a*u y) x i = a*coordPartial u x i := by
  rw [real_coordPartial_mul _ _ contDiff_const hu]
  simp [coordPartial]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ENNReal
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereWeightedL2Measurable
attribute [local instance] OAI.Yau.Target.sphereWeightedL2Borel
def sphereWeightedMeasure (rho : Base → ℝ) : Measure Base :=
  sphereReferenceMeasure.withDensity (fun x ↦ ENNReal.ofReal (rho x))

theorem sphereWeightedMeasure_finite (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) : IsFiniteMeasure (sphereWeightedMeasure rho) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (sphereReferenceMeasure_integrable_continuous rho hr) (Filter.Eventually.of_forall hp)]
  exact ENNReal.ofReal_ne_top

theorem sphereWeightedMeasure_integral (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (f : Base → ℝ) :
    (∫ x, f x ∂sphereWeightedMeasure rho) = ∫ x, rho x*f x ∂sphereReferenceMeasure := by
  rw [sphereWeightedMeasure,integral_withDensity_eq_integral_toReal_smul
    hr.measurable.ennreal_ofReal (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp _),smul_eq_mul]

theorem sphereWeighted_memLp (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    MemLp u 2 (sphereWeightedMeasure rho) := by
  let := sphereWeightedMeasure_finite rho hr hp
  exact hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)

def sphereWeightedToLp (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    Lp ℝ 2 (sphereWeightedMeasure rho) := (sphereWeighted_memLp rho hr hp u hu).toLp u

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyL2Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereEnergyL2MapMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
abbrev SphereWeightedL2 (d : SphereEnergyData) := Lp ℝ 2 (sphereWeightedMeasure d.density)

def sphereEnergyL2Linear (d : SphereEnergyData) : SphereEnergySmooth d →ₗ[ℝ] SphereWeightedL2 d where
  toFun u := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous
  map_add' u v := by
    exact MemLp.toLp_add
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous)
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d v) (SphereEnergySmooth.toSmooth d v).property.continuous)
  map_smul' t u := by
    exact MemLp.toLp_const_smul t
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous)

def sphereEnergyL2Map (d : SphereEnergyData) : SphereEnergyHilbert d →L[ℝ] SphereWeightedL2 d :=
  (sphereEnergyL2Linear d).extendOfNorm (sphereEnergyToCompletion d).toLinearMap

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedChartL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereWeightedChartL2Measurable : MeasurableSpace Base := borel Base
local instance sphereWeightedChartL2Borel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedMeasure_ae_iff (d : SphereEnergyData) (P : Base → Prop) :
    (∀ᵐ x ∂sphereWeightedMeasure d.density, P x) ↔ ∀ᵐ x ∂sphereReferenceMeasure, P x := by
  rw [sphereWeightedMeasure,ae_withDensity_iff d.continuous.measurable.ennreal_ofReal]
  simp only [ne_eq,ENNReal.ofReal_eq_zero,not_le.mpr (d.positive _),not_false_eq_true,true_implies]

theorem sphereWeightedMeasure_ae_chart_iff (d : SphereEnergyData) (p : Base) (P : Base → Prop) :
    (∀ᵐ x ∂sphereWeightedMeasure d.density, P x) ↔ ∀ᵐ y, P (sphereChartCoordMap p y) := by
  rw [sphereWeightedMeasure_ae_iff,sphereReferenceMeasure_eq_chart p,
    (sphereChartCoordMap_measurableEmbedding p).ae_map_iff]
  simp only [roundChartDensity_coord_eq]
  rw [ae_withDensity_iff roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal]
  simp only [ne_eq,ENNReal.ofReal_eq_zero,not_le.mpr (roundCoordDensity_pos _),not_false_eq_true,true_implies]

theorem sphereWeightedMeasure_integrable_iff (d : SphereEnergyData) (F : Base → ℝ) :
    Integrable F (sphereWeightedMeasure d.density) ↔
      Integrable (fun x ↦ d.density x*F x) sphereReferenceMeasure := by
  rw [sphereWeightedMeasure,integrable_withDensity_iff_integrable_smul'
    d.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (d.positive _).le,smul_eq_mul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereL2LocalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
noncomputable section
local instance sphereL2LocalPullbackMeasurable : MeasurableSpace Base := borel Base
local instance sphereL2LocalPullbackBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedL2_chart_aestronglyMeasurable (d : SphereEnergyData)
    (f : SphereWeightedL2 d) (p : Base) : AEStronglyMeasurable (fun x ↦ f (sphereChartCoordMap p x)) := by
  have hr : sphereReferenceMeasure ≪ sphereWeightedMeasure d.density :=
    withDensity_absolutelyContinuous' d.continuous.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (d.positive x)).ne'))
  have hf := AEStronglyMeasurable.mono_ac hr (Lp.aestronglyMeasurable f)
  rw [sphereReferenceMeasure_eq_chart p,
    (sphereChartCoordMap_measurableEmbedding p).aestronglyMeasurable_map_iff] at hf
  simp only [roundChartDensity_coord_eq] at hf
  exact AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous' roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (roundCoordDensity_pos x)).ne'))) hf

theorem sphereWeightedL2_norm_sq_integral (d : SphereEnergyData) (f : SphereWeightedL2 d) :
    ‖f‖^2 = ∫ x, d.density x*(f x)^2 ∂sphereReferenceMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,
    sphereWeightedMeasure_integral d.density d.continuous (fun x ↦ (d.positive x).le)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs])

theorem sphereWeightedL2_compact_chart_bound (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict K) ∧
      (∫ x in K, (f (sphereChartCoordMap p x))^2) ≤ C*‖f‖^2 := by
  let a := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)
  obtain ⟨q,hq,_,_,hqb⟩ := Yau.Jets.compact_positive_bounds hK a
    ((roundCoordDensity_smooth.continuous.mul
      (d.continuous.comp (sphereChartCoordMap_smooth p).continuous)).continuousOn)
    (fun x _ ↦ mul_pos (roundCoordDensity_pos x) (d.positive _))
  refine ⟨q⁻¹,inv_pos.mpr hq,?_⟩
  intro f
  have hf := sphereWeightedL2_chart_aestronglyMeasurable d f p
  have hs := (Lp.memLp f).integrable_sq
  have hi : Integrable (fun x ↦ a x*(f (sphereChartCoordMap p x))^2) := by
    have h := (sphereReferenceMeasure_integrable_chart p _).mp
      ((sphereWeightedMeasure_integrable_iff d _).mp hs)
    simpa only [roundChartDensity_coord_eq,a,mul_assoc] using h
  have hbound : ∀ x ∈ K, (f (sphereChartCoordMap p x))^2 ≤ q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) := by
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hqb x hx).1 (sq_nonneg (f (sphereChartCoordMap p x)))
    calc
      _ = q⁻¹*(q*(f (sphereChartCoordMap p x))^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hq.le)
  have his : IntegrableOn (fun x ↦ (f (sphereChartCoordMap p x))^2) K := by
    apply ((hi.const_mul q⁻¹).integrableOn).mono' (hf.pow 2).restrict
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change |(f (sphereChartCoordMap p x))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hbound x hx
  refine ⟨(memLp_two_iff_integrable_sq hf.restrict).mpr his,?_⟩
  calc
    _ ≤ ∫ x in K, q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) :=
      setIntegral_mono_on his (hi.const_mul q⁻¹).integrableOn hK.measurableSet hbound
    _ ≤ ∫ x, q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) :=
      setIntegral_le_integral (hi.const_mul q⁻¹) (Filter.Eventually.of_forall (fun x ↦ by
        exact mul_nonneg (inv_nonneg.mpr hq.le)
          (mul_nonneg (mul_pos (roundCoordDensity_pos x) (d.positive _)).le (sq_nonneg _))))
    _ = _ := by
      rw [integral_const_mul,sphereWeightedL2_norm_sq_integral,sphereReferenceMeasure_integral_chart p]
      simp only [roundChartDensity_coord_eq,a,mul_assoc]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartDerivativeMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section

def sphereSmoothChartPartial (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : Yau.Jets.Coord → ℝ :=
  fun x ↦ Yau.coordPartial ((SphereEnergySmooth.toSmooth d u) ∘ sphereChartCoordMap p) x i

theorem sphereSmoothChartPartial_continuous (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : Continuous (sphereSmoothChartPartial d p i u) :=
  (Yau.real_coordPartial_smooth _
    (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) i).continuous

theorem sphereSmoothChartPartial_memLp (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : MemLp (sphereSmoothChartPartial d p i u) 2
      (volume.restrict (realFinCube 4)) :=
  Yau.real_continuous_memLp_compact (realFinCube_isCompact 4) _ (sphereSmoothChartPartial_continuous d p i u)

def sphereChartDerivativeLinear (d : SphereEnergyData) (p : Base) (i : Fin 4) :
    SphereEnergySmooth d →ₗ[ℝ] SphereChartCubeL2 where
  toFun u := (sphereSmoothChartPartial_memLp d p i u).toLp (sphereSmoothChartPartial d p i u)
  map_add' u v := by
    have he : sphereSmoothChartPartial d p i (u+v) =
        sphereSmoothChartPartial d p i u+sphereSmoothChartPartial d p i v := by
      funext x
      exact Yau.real_coordPartial_add _ _
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d v).property p) x i
    exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_add (sphereSmoothChartPartial_memLp d p i u) (sphereSmoothChartPartial_memLp d p i v))
  map_smul' a u := by
    have he : sphereSmoothChartPartial d p i (a • u) = a • sphereSmoothChartPartial d p i u := by
      funext x
      exact Yau.real_coordPartial_const_mul _
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) a x i
    exact (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_const_smul a (sphereSmoothChartPartial_memLp d p i u))

def sphereChartDerivativeMap (d : SphereEnergyData) (p : Base) (i : Fin 4) :
    SphereEnergyHilbert d →L[ℝ] SphereChartCubeL2 :=
  (sphereChartDerivativeLinear d p i).extendOfNorm (sphereEnergyToCompletion d).toLinearMap

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartScalarExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable (center : Base)

def sphereChartToCoord (p : Base) : Yau.Jets.Coord :=
  seedCoordEquiv.symm ((extChartAt (𝓡 4) center) p)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartValueMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section

local instance sphereChartValueMapMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereChartValueMapBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartValue_memLp (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d) :
    MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict (realFinCube 4)) := by
  obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  exact (hb f).1

def sphereChartValueLinear (d : SphereEnergyData) (p : Base) :
    SphereWeightedL2 d →ₗ[ℝ] SphereChartCubeL2 where
  toFun f := (sphereChartValue_memLp d p f).toLp (fun x ↦ f (sphereChartCoordMap p x))
  map_add' f g := by
    have h := (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ (f+g) x=f x+g x)).mp (Lp.coeFn_add f g)
    exact (MemLp.toLp_congr _ _ (ae_restrict_of_ae h)).trans
      (MemLp.toLp_add (sphereChartValue_memLp d p f) (sphereChartValue_memLp d p g))
  map_smul' t f := by
    have h := (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ (t • f) x=t*f x)).mp (Lp.coeFn_smul t f)
    exact (MemLp.toLp_congr _ _ (ae_restrict_of_ae h)).trans
      (MemLp.toLp_const_smul t (sphereChartValue_memLp d p f))

theorem sphereChartValueLinear_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d, ‖sphereChartValueLinear d p f‖ ≤ C*‖f‖ := by
  obtain ⟨C,hC,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro f
  have hn : ‖sphereChartValueLinear d p f‖^2 = ∫ x in realFinCube 4, (f (sphereChartCoordMap p x))^2 :=
    Yau.real_toLp_norm_sq _ (sphereChartValue_memLp d p f)
  have hs : (Real.sqrt C*‖f‖)^2=C*‖f‖^2 := by rw [mul_pow,Real.sq_sqrt hC.le]
  nlinarith [(hb f).2,norm_nonneg (sphereChartValueLinear d p f),
    mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f)]

def sphereChartValueMap (d : SphereEnergyData) (p : Base) :
    SphereWeightedL2 d →L[ℝ] SphereChartCubeL2 :=
  (sphereChartValueLinear d p).mkContinuous
    (sphereChartValueLinear_bound d p).choose (sphereChartValueLinear_bound d p).choose_spec.2

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartCutoffApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereChartCutoffApproxMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereChartCutoffApproxBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereCutoffValueMap (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) :
    SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realCompactL2Map (realFinCube_isCompact 4) eta he.continuous hs).comp
    ((sphereChartValueMap d p).comp (sphereEnergyL2Map d))

def sphereCutoffDerivativeMap (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) :
    SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realCompactL2Map (realFinCube_isCompact 4) eta he.continuous hs).comp
    (sphereChartDerivativeMap d p i) +
  (Yau.realCompactL2Map (realFinCube_isCompact 4) (fun x ↦ Yau.coordPartial eta x i)
    (Yau.real_coordPartial_smooth eta he i).continuous
    ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs)).comp
    ((sphereChartValueMap d p).comp (sphereEnergyL2Map d))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTestFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Set
open scoped ContDiff
noncomputable section

def sphereChartTestFlux (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  roundCoordDensity x * ∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothGreenLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

def sphereChartFlux (A : IntrinsicTensor) (v : Base → ℝ) (p : Base) : Yau.Jets.Coord → Yau.Jets.Coord :=
  fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*Yau.coordPartial (v ∘ sphereChartCoordMap p) y j

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothL2Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereSmoothL2DensityMeasurable : MeasurableSpace Base := borel Base

local instance sphereSmoothL2DensityBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereSmoothToContinuous (d : SphereEnergyData) (u : SphereEnergySmooth d) : C(Base,ℝ) :=
  ⟨SphereEnergySmooth.toSmooth d u,(SphereEnergySmooth.toSmooth d u).property.continuous⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereWeakResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Filter
open scoped InnerProduct
noncomputable section

local instance sphereWeakResolventMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereCompletedDirichlet (d : SphereEnergyData) (u v : SphereEnergyHilbert d) : ℝ :=
  inner ℝ u v-inner ℝ (sphereEnergyL2Map d u) (sphereEnergyL2Map d v)

def sphereWeakSolution (d : SphereEnergyData) : SphereWeightedL2 d →L[ℝ] SphereEnergyHilbert d :=
  (sphereEnergyL2Map d).adjoint

def sphereL2Resolvent (d : SphereEnergyData) : SphereWeightedL2 d →L[ℝ] SphereWeightedL2 d :=
  (sphereEnergyL2Map d).comp (sphereWeakSolution d)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartDivergenceData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartDivergenceDataMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereChartPrincipalDensity (d : SphereEnergyData) (p : Base) (x : Yau.Jets.Coord)
    (i j : Fin 4) : ℝ := roundCoordDensity x*intrinsicRealPrincipal d.tensor p x i j

def sphereChartResolventForcing (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d)
    (x : Yau.Jets.Coord) : ℝ :=
  roundCoordDensity x*d.density (sphereChartCoordMap p x)*
    (f (sphereChartCoordMap p x)-(sphereL2Resolvent d f) (sphereChartCoordMap p x))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartFluxL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartFluxL2Measurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereChartFluxL2Borel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereChartCompletedFlux (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (j : Fin 4) (x : Yau.Jets.Coord) : ℝ :=
  ∑ i, sphereChartPrincipalDensity d p x i j*(sphereChartDerivativeMap d p i z) x

def sphereChartFluxZero (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (j : Fin 4) : Yau.Jets.Coord → ℝ :=
  (realFinCube 4).indicator (sphereChartCompletedFlux d p z j)

def sphereChartForcingZero (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d) :
    Yau.Jets.Coord → ℝ := (realFinCube 4).indicator (sphereChartResolventForcing d p f)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceTestMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereDifferenceTestMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceTestBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereDifferenceTestMap (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) : SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realGlobalCompactMap (realFinCube_isCompact 4) theta ht.continuous hts).comp
    ((Yau.realL2DifferenceMap i h).comp (sphereCutoffValueMap d p eta he hes))

def sphereDifferenceTestDerivativeMap (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) : SphereEnergyHilbert d →L[ℝ] Yau.RealEuclideanL2 4 :=
  (Yau.realGlobalCompactMap (realFinCube_isCompact 4) theta ht.continuous hts).comp
    ((Yau.realL2DifferenceMap i h).comp (sphereCutoffDerivativeMap d p eta he hes j)) +
  (Yau.realGlobalCompactMap (realFinCube_isCompact 4) (fun x ↦ Yau.coordPartial theta x j)
    (Yau.real_coordPartial_smooth theta ht j).continuous
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hts)).comp
    ((Yau.realL2DifferenceMap i h).comp (sphereCutoffValueMap d p eta he hes))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicitySquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def sphereCrossDifferential (u v : Base → ℝ) (p : Base) : SphereCotangent p :=
  u p • sphereDifferential v p-v p • sphereDifferential u p

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereTransitionScalar
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def sphereScalarPartial (f : Base → ℝ) (p : Base) (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) (seedCoordEquiv x)
    (EuclideanSpace.basisFun (Fin 4) ℝ i)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereTransitionFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix
open scoped ContDiff

def sphereCoordFlux (A : IntrinsicTensor) (f : Base → ℝ) (p : Base)
    (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (intrinsicRoundFlux A f p i (seedCoordEquiv x) : ℂ)

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SupportedFiniteAtlasBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

def sphereCoefficientDistance (P : Finset Base) (J : ℕ)
    (A : IntrinsicTensor) (rho : Base → ℝ) (B : IntrinsicTensor) (sigma : Base → ℝ) : ℝ :=
  finiteChartDerivativeSize P sphereAtlasCore J (fun p z ↦
    intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicDivergenceCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

def intrinsicDivergencePrincipal (A : IntrinsicTensor) (p : Base) (x : Yau.Jets.Coord) :
    Matrix (Fin 4) (Fin 4) ℝ := roundCoordDensity x • intrinsicRealPrincipal A p x

def intrinsicDivergencePotential (rho : Base → ℝ) (lam : ℝ) (p : Base) (x : Yau.Jets.Coord) : ℝ :=
  roundCoordDensity x * intrinsicRealPotential rho lam p x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

def coefficientPrincipalEntry (i j : Fin 4) : CoefficientPoint BaseModel →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp ((ContinuousLinearMap.apply ℝ BaseModel (EuclideanSpace.proj j)).comp
    (ContinuousLinearMap.fst ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) ℝ))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ExteriorCorrectedEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance exteriorCorrectedEquationLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance exteriorCorrectedEquationLocalInst1_r297a3e_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst2_r297a3e_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst3_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst4_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst5_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst6_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst10_r297a3e_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance exteriorCorrectedEquationLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorWeakAddLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

def realWeakGradientCommutator {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (k j : Fin n) (x : Coord n) : ℝ :=
  ∑ a, coordPartial (fun y ↦ C y a j) x k*U a x

def realWeakGradientCommutatorDerivative {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k j l : Fin n) (x : Coord n) : ℝ :=
  ∑ a, (coordPartial (fun y ↦ C y a j) x k*H a l x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l*U a x)

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSquareCutoffWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSquareCutoffGradient {n : ℕ} (eta u : Coord n → ℝ)
    (g : Fin n → Coord n → ℝ) (j : Fin n) : Coord n → ℝ :=
  fun x ↦ eta x^2*g j x+2*eta x*coordPartial eta x j*u x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakSecondCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSecondCommutator {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k l j : Fin n) (x : Coord n) : ℝ :=
  ∑ a, (coordPartial (fun y ↦ C y a j) x l*H a k x+
    coordPartial (fun y ↦ C y a j) x k*H a l x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l*U a x)

def realSecondCommutatorDerivative {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (J : Fin n → Fin n → Fin n → Coord n → ℝ) (k l j i : Fin n) (x : Coord n) : ℝ :=
  ∑ a, ((coordPartial (fun y ↦ C y a j) x l*J a k i x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y l) x i*H a k x)+
    (coordPartial (fun y ↦ C y a j) x k*J a l i x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x i*H a l x)+
    (coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l*H a i x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ coordPartial (fun t ↦ C t a j) z k) y l) x i*U a x))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakSecondForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSecondScalarForcing {n : ℕ} (B w : Coord n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k l : Fin n) (x : Coord n) : ℝ :=
  B x*H k l x+coordPartial B x l*U k x+
    coordPartial B x k*U l x+coordPartial (fun y ↦ coordPartial B y k) x l*w x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SimplicityCoordinateEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section

def roundSimplicityEnergy (u v zeta : Yau.Jets.Coord → ℝ) (lam : ℝ) : ℝ :=
  ∫ x, roundCoordDensity x * (zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
    lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PerturbedNodalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance perturbedNodalTransferLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance perturbedNodalTransferLocalInst1_r297a3e_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst2_r297a3e_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst3_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst4_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst5_r297a3e_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst6_r297a3e_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst10_r297a3e_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance perturbedNodalTransferLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenResolventForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereEigenForcingMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereEigenForcingBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereEigenForcingCoefficient (d : SphereEnergyData) (p : Base) (mu : ℝ)
    (x : Yau.Jets.Coord) : ℝ :=
  (mu⁻¹-1)*(roundCoordDensity x*d.density (sphereChartCoordMap p x))

def sphereEigenForcingDerivative (d : SphereEnergyData) (p : Base) (mu : ℝ)
    (f : SphereWeightedL2 d) (k : Fin 4) (x : Yau.Jets.Coord) : ℝ :=
  sphereEigenForcingCoefficient d p mu x*(sphereChartDerivativeMap d p k (sphereWeakSolution d f)) x+
    Yau.coordPartial (sphereEigenForcingCoefficient d p mu) x k*
      (sphereL2Resolvent d f) (sphereChartCoordMap p x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereIndexedRayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set
open scoped ContDiff
noncomputable section

local instance sphereIndexedRayleighMeasurable_r297a3e_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedRayleighBorel_r297a3e_1 : BorelSpace Base := ⟨rfl⟩
def sphereRayleighUpperLevels (d : SphereEnergyData) (N : ℕ) : Set ℝ :=
  {a | ∃ V : Submodule ℝ sphereSmoothFunctions,
    FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
    ∀ x ∈ V, x ≠ 0 → sphereRayleighQuotient d.tensor d.density x ≤ a}

def sphereIndexedEigenvalue (d : SphereEnergyData) (N : ℕ) : ℝ :=
  sInf (sphereRayleighUpperLevels d N)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereIterationInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal
noncomputable section

structure SphereNodalStage (r delta : ℝ) (k : ℕ) extends SphereComparisonPair r delta where
  frequency : ℕ
  frequency_pos : 0 < frequency
  charts : Finset Base
  radius : ℝ
  radius_pos : 0 < radius
  persistence : ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
    sphereCoefficientDistance charts 8 energy.tensor energy.density b.tensor b.density < radius →
    ∃ (mu : ℝ) (v : Base → ℝ), mu ∈ Icc (seedEigenvalue frequency/2) (2*seedEigenvalue frequency) ∧
      0 < mu ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
        mu*v ((extChartAt (𝓡 4) p).symm y)) ∧
      ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
      (∀ x : Manifold5, -chartLaplacian
        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
        (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
          mu*circleLift v x) ∧
      ENNReal.ofReal ((k:ℝ)+1) < nodalMeasure
        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
        (circleLift v) / ENNReal.ofReal (Real.sqrt mu)

def SphereStageExtension (r delta : ℝ) : Prop :=
  ∀ (d : SphereComparisonPair r delta) (k : ℕ) (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps →
    ∀ n₀ : ℕ, ∃ s : SphereNodalStage r delta k, n₀ ≤ s.frequency ∧ d.support ⊆ s.support ∧
      sphereCoefficientDistance P J d.energy.tensor d.energy.density s.energy.tensor s.energy.density < eps

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereSummableSmoothPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance summablePairTangentNormedGroup (x : Base) : NormedAddCommGroup (TangentSpace (𝓡 4) x) :=
  inferInstanceAs (NormedAddCommGroup BaseModel)
local instance summablePairTangentNormedSpace (x : Base) : NormedSpace ℝ (TangentSpace (𝓡 4) x) :=
  inferInstanceAs (NormedSpace ℝ BaseModel)
local instance summablePairCotangentNormedGroup (x : Base) : NormedAddCommGroup (SphereCotangent x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance summablePairCotangentNormedSpace (x : Base) : NormedSpace ℝ (SphereCotangent x) :=
  ContinuousLinearMap.toNormedSpace

end
end Yau.Target

end OAI
end


