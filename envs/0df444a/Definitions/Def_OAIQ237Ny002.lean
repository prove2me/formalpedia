-- Prove2me | Definitions.Def_OAIQ237Ny002
-- name    : OAIQ237Ny002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:23:42.347312+00:00
-- url     : https://prove2.me/theorems/d36e3151-2b58-4f70-abcb-598b1d9c6cc4
-- title:
--   Definitions bundle OAIQ237Ny002 of the split of OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 266 declarations of OpenAI's Lean: 158 definitions, 3 inductive types or structures, 5 instances and 100 theorems. The definitions and types are `OAI.Yau.Geometry.metricPerpProjection`, `OAI.Yau.Geometry.normalizedLogJet`, `OAI.Yau.Geometry.normalizedRescaling`, `OAI.Yau.Geometry.partialCubeControl`, `OAI.Yau.Geometry.positiveContravariantEquiv`, `OAI.Yau.Geometry.positiveMetricEquiv`, `OAI.Yau.Geometry.pullbackMetric`, `OAI.Yau.Geometry.pulledFlux`, `OAI.Yau.Geometry.radialVolumeMatrix`, `OAI.Yau.Geometry.realBallCutoff`, `OAI.Yau.Geometry.realConvexifiedPhase`, `OAI.Yau.Geometry.realCoordGradient`, `OAI.Yau.Geometry.realCoordinateDual`, `OAI.Yau.Geometry.realCoordinateSquare`, `OAI.Yau.Geometry.realCubeAverage`, `OAI.Yau.Geometry.realCubeCell`, `OAI.Yau.Geometry.realCubeCellMean`, `OAI.Yau.Geometry.realCubeL2Control`, `OAI.Yau.Geometry.realCutoffWeight`, `OAI.Yau.Geometry.realDerivativeErrorFlux`, `OAI.Yau.Geometry.realEllipticResidual`, `OAI.Yau.Geometry.realFiniteJetSquare`, `OAI.Yau.Geometry.realGradientSquare`, `OAI.Yau.Geometry.realIndentedPhase`, `OAI.Yau.Geometry.realJetErrorFlux`, `OAI.Yau.Geometry.realJetErrorSource`, `OAI.Yau.Geometry.realJetProductSum`, `OAI.Yau.Geometry.realMatrixEnergy`, `OAI.Yau.Geometry.realMatrixFlux`, `OAI.Yau.Geometry.realSourceResidual`, `OAI.Yau.Geometry.realTransportBilinear`, `OAI.Yau.Geometry.realTransportDeformation`, `OAI.Yau.Geometry.realTransportQuadratic`, `OAI.Yau.Geometry.realWeightedElliptic`, `OAI.Yau.Geometry.removeFrame`, `OAI.Yau.Geometry.rescaledAmplitudeRatio`, `OAI.Yau.Geometry.rescaledGaussianField`, `OAI.Yau.Geometry.rescaledPhaseDefect`, `OAI.Yau.Geometry.rescaledSeed`, `OAI.Yau.Geometry.rescaledSeedNormalizer` and 121 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `NodalSets_Charts_BaseChartFlux`, `NodalSets_Charts_ChartFrameSmooth`, `NodalSets_Charts_ChartMetric`, `NodalSets_Charts_ComplexMetricFlux`, `NodalSets_Charts_IntrinsicChartTensor`, `NodalSets_Charts_IntrinsicCorrectedChart`, `NodalSets_Charts_IntrinsicDifferentialPairChart`, `NodalSets_Charts_IntrinsicGlobalSphereStage`, `NodalSets_Charts_IntrinsicLiftGeometry`, `NodalSets_Charts_IntrinsicUniformPositiveSphereStage`, `NodalSets_Charts_MetricFrameOps`, `NodalSets_Charts_MetricFrequencyBounds`, `NodalSets_Charts_PositiveMetric`, `NodalSets_Charts_RoundChartConnection`, `NodalSets_Charts_SeedChartPrincipal`, `NodalSets_Charts_SeedChartScalarExtension`, `NodalSets_Charts_SmoothInverseChart`, `NodalSets_Charts_SphereChartConformal`, `NodalSets_Charts_SphereChartOpenMap`, `NodalSets_Charts_SphereChartTransition`, `NodalSets_Charts_SphereChartVolume`, `NodalSets_Charts_SphereContravariant`, `NodalSets_Charts_SphereCotangentCoordinates`, `NodalSets_Charts_SphereCovectorRestriction`, `NodalSets_Charts_SphereDifferentialCoordinates`, `NodalSets_Charts_SphereDirichletBilinear`, `NodalSets_Charts_SphereEnergyBilinear`, `NodalSets_Charts_SphereEnergyCompletion`, `NodalSets_Charts_SphereEnergyInnerProduct`, `NodalSets_Charts_SphereMeasureChartGeometry`, `NodalSets_Charts_SphereReferenceMeasure`, `NodalSets_Charts_SphereReferenceMeasureFinite`, `NodalSets_Charts_SphereReferenceMeasureInvariance`, `NodalSets_Charts_SphereReferenceMeasurePositive`, `NodalSets_Charts_SphereSmoothFromCharts`, `NodalSets_Charts_SphereTransitionFrame`, `NodalSets_Charts_SupportedFiniteAtlasBounds`, `NodalSets_Coefficients_CoordinateCorrection`, `NodalSets_Coefficients_CutoffResidualProductLemmas`, `NodalSets_Coefficients_IntrinsicCoefficientMap`, `NodalSets_Coefficients_IntrinsicCoefficientSmooth`, `NodalSets_Coefficients_JetCoefficient`, `NodalSets_Coefficients_RoundCoefficientJets`, `NodalSets_Coefficients_RoundSupportedCorrection`, `NodalSets_Coefficients_SeedCoefficientPlacement`, `NodalSets_Coefficients_SeededResidual`, `NodalSets_Coefficients_SmoothFiniteResidual`, `NodalSets_Elliptic_AdmissibleDirectionTriple`, `NodalSets_Elliptic_CommutatorBounds`, `NodalSets_Elliptic_CompactSourceOperator`, `NodalSets_Elliptic_CoordinateTransverseDisk`, `NodalSets_Elliptic_CorrugationGainStage`, `NodalSets_Elliptic_CubeGradientBound`, `NodalSets_Elliptic_DirectionTripleAlgebra`, `NodalSets_Elliptic_EikonalPolynomial`, `NodalSets_Elliptic_IntrinsicAmbientSmooth`, `NodalSets_Elliptic_IntrinsicEnergyIntegrable`, `NodalSets_Elliptic_IntrinsicRealCoordinates`, `NodalSets_Elliptic_IntrinsicRoundPerturbation`, `NodalSets_Elliptic_IntrinsicWeightedLift`, `NodalSets_Elliptic_Logarithm`, `NodalSets_Elliptic_NormalizedRescaling`, `NodalSets_Elliptic_PhaseContactFamily`, `NodalSets_Elliptic_PlacedEnvelopeDomains`, `NodalSets_Elliptic_PolynomialEvaluation`, `NodalSets_Elliptic_PositiveContravariant`, `NodalSets_Elliptic_RadialVolumeMatrix`, `NodalSets_Elliptic_RealBallCutoffChain`, `NodalSets_Elliptic_RealCarlemanLocalConditions`, `NodalSets_Elliptic_RealConvexifiedPhase`, `NodalSets_Elliptic_RealConvexifiedQuadraticLemmas`, `NodalSets_Elliptic_RealCoordinateDual`, `NodalSets_Elliptic_RealCoordinateEllipticLemmas`, `NodalSets_Elliptic_RealCubeAverage`, `NodalSets_Elliptic_RealCubeCellApproximation`, `NodalSets_Elliptic_RealCubeCellPartition`, `NodalSets_Elliptic_RealCubeL2Control`, `NodalSets_Elliptic_RealCutoffIntegralsLemmas`, `NodalSets_Elliptic_RealDifferentiatedEquation`, `NodalSets_Elliptic_RealEllipticLocalityLemmas`, `NodalSets_Elliptic_RealFiniteJetSquare`, `NodalSets_Elliptic_RealJetErrorEquation`, `NodalSets_Elliptic_RealJetProductExpansion`, `NodalSets_Elliptic_RealMatrixEnergy`, `NodalSets_Elliptic_RealMatrixTransport`, `NodalSets_Elliptic_RealTransportQuadratic`, `NodalSets_Elliptic_RealWeightedElliptic`, `NodalSets_Elliptic_RecursiveJet`, `NodalSets_Elliptic_RescaledHigherJets`, `NodalSets_Elliptic_RescaledPhaseDefect`, `NodalSets_Elliptic_RescaledSeedBounds`, `NodalSets_Elliptic_RoundCoordinateGradient`, `NodalSets_Elliptic_SeedCoordAdmissibility`, `NodalSets_Elliptic_SeedCoordPatchTopology`, `NodalSets_Elliptic_SeedLogExtension`, `NodalSets_Elliptic_SmoothDefectBounds`, `NodalSets_Elliptic_SmoothSymmetry`, `NodalSets_Elliptic_TaylorMatching`, `NodalSets_Elliptic_TaylorPolynomial`, `NodalSets_Elliptic_TransportJet`, `NodalSets_Elliptic_TransverseCylinderVolume`, `NodalSets_Elliptic_TransverseSpanning`, `NodalSets_Elliptic_UniformDirectional`, `NodalSets_Elliptic_WarpedAmbientForm`, `NodalSets_Elliptic_WeightedCoordinateOperator`, `NodalSets_Elliptic_WeightedHessianStability`, `NodalSets_Elliptic_WeightedLift`, `NodalSets_SmoothLimit_SphereIterationInterface`, `NodalSets_Spectral_MetricProjectionBounds`, `NodalSets_Spectral_SphereEigenGlobalRepresentative`, `NodalSets_Spectral_SphereRayleighQuotient`, `NodalSets_Waves_FiniteWaveJet`, `NodalSets_Waves_PlacedFirstJetProbability`, `NodalSets_Waves_RescaledGaussianField`, `NodalSets_Waves_WaveJetAssembly`.
--
--   **Imports.** It imports the published bundle `Def_YauCounterexample`; the bundles `OAIQ237Ny000` and `OAIQ237Ny001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ237Ny004`; the statements `OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_main_coefficient_jets`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_sign_coefficient_upper`, `OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_factor_jets`, `OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_phase_first`, `OAI.Yau.Geometry.corrugation_actual_angular_estimates`, `OAI.Yau.Geometry.corrugation_actual_high_admissibility`, `OAI.Yau.Geometry.corrugation_actual_low_old_margin`, `OAI.Yau.Geometry.corrugation_actual_low_radial`, `OAI.Yau.Geometry.corrugation_projected_direction_freezing`, `OAI.Yau.Geometry.exists_placed_envelope`, `OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain`, `OAI.Yau.Geometry.lattice_actual_two_point_energy_fixed_domain`, `OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain`, `OAI.Yau.Geometry.real_compact_interior_pointwise`, `OAI.Yau.Geometry.real_global_unique_continuation`, `OAI.Yau.Target.PlacedEnvelopeData.waves_in_domain` and `OAI.Yau.Target.seed_envelope_coordinate_patch`; the proofs of `OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_main_coefficient_jets`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_sign_coefficient_upper`, `OAI.Yau.Geometry.NormalOperatorFamily.solve_jets`, `OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second`, `OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_factor_jets`, `OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_phase_first`, `OAI.Yau.Geometry.compact_actual_metric_wave_jets`, `OAI.Yau.Geometry.construct_triple_source_waves`, `OAI.Yau.Geometry.constructed_coordinate_wave_estimates`, `OAI.Yau.Geometry.corrugation_actual_angular_estimates`, `OAI.Yau.Geometry.corrugation_actual_high_admissibility`, `OAI.Yau.Geometry.corrugation_actual_low_gradient`, `OAI.Yau.Geometry.corrugation_actual_low_old_margin`, `OAI.Yau.Geometry.corrugation_actual_low_radial`, `OAI.Yau.Geometry.corrugation_actual_metric_unit_errors`, `OAI.Yau.Geometry.corrugation_grid_admissibility`, `OAI.Yau.Geometry.corrugation_grid_integrated_gain`, `OAI.Yau.Geometry.corrugation_projected_direction_freezing`, `OAI.Yau.Geometry.corrugation_speed_freezing`, `OAI.Yau.Geometry.exists_placed_envelope`, `OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain`, `OAI.Yau.Geometry.lattice_actual_two_point_energy_fixed_domain`, `OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain`, `OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain` and `OAI.Yau.Target.PlacedEnvelopeData.waves_in_domain`.
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
import Definitions.Def_OAIQ237Ny000
import Definitions.Def_OAIQ237Ny001

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RecursiveJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def gradientJet (v : Fin 4 → ℂ) (a : Jet) (k : ℕ) (i : Fin 4) : CPoly :=
  if k = 0 then C (v i) else pderiv i (a (k + 1))

def eikonalKnown (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a : Jet) : CPoly :=
  (∑ t ∈ Finset.range n, ∑ i,
    gradientJet v a (t + 1) i * gradientJet v a (n - t) i) +
  ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - r), ∑ i, ∑ j,
    g (r + 1) i j * gradientJet v a t i * gradientJet v a (n - r - t) j

def eikonalCoefficient (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a : Jet) : CPoly :=
  homogeneousComponent (n + 1)
    ((∑ t ∈ Finset.range (n + 2), ∑ i,
      gradientJet v a t i * gradientJet v a (n + 1 - t) i) +
    ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - r), ∑ i, ∑ j,
      g (r + 1) i j * gradientJet v a t i * gradientJet v a (n - r - t) j)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransportJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def transportKnown (W : ℕ → Fin 4 → CPoly) (c f : Jet) (n : ℕ) (a : Jet) : CPoly :=
  (∑ r ∈ Finset.range n, ∑ i, W (r + 1) i * pderiv i (a (n - r))) +
    (∑ r ∈ Finset.range (n + 1), c r * a (n - r)) - f n

def transportCoefficient (w : Fin 4 → ℂ) (W : ℕ → Fin 4 → CPoly)
    (c f : Jet) (n : ℕ) (a : Jet) : CPoly :=
  homogeneousComponent n
    ((∑ r ∈ Finset.range (n + 1), ∑ i,
      (if r = 0 then C (w i) else W r i) * pderiv i (a (n - r + 1))) +
      (∑ r ∈ Finset.range (n + 1), c r * a (n - r)) - f n)

def secondOrderCoefficient (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (b : ℕ → Fin 4 → CPoly) (a : Jet) (n : ℕ) : CPoly :=
  homogeneousComponent n
    ((∑ r ∈ Finset.range (n + 1), ∑ i, ∑ j,
      g r i j * pderiv i (pderiv j (a (n - r + 2)))) +
    ∑ r ∈ Finset.range (n + 1), ∑ i, b r i * pderiv i (a (n - r + 1)))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteWaveJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def truncateJet (a : Jet) (d : ℕ) : CPoly := ∑ k ∈ Finset.range (d + 1), a k

def polynomialJet (p : CPoly) : Jet := fun k ↦ homogeneousComponent k p

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_JetCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialSecondOrder (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (p : CPoly) : CPoly :=
  (∑ i, ∑ j, g i j * pderiv i (pderiv j p)) + ∑ i, b i * pderiv i p

def polynomialTransport (W : Fin 4 → CPoly) (c f a : CPoly) : CPoly :=
  (∑ i, W i * pderiv i a) + c * a - f

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EikonalPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def polynomialEikonal (g : Fin 4 → Fin 4 → CPoly) (p : CPoly) : CPoly :=
  (∑ i, ∑ j, g i j * (pderiv i p * pderiv j p)) + C 4

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveJetAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def beamVector (g : Fin 4 → Fin 4 → CPoly) (phi : CPoly) (i : Fin 4) : CPoly :=
  C 2 * ∑ j, g i j * pderiv j phi

def beamScalar (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (phi : CPoly) : CPoly :=
  polynomialSecondOrder g b phi + C 6

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialEvaluation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def coordCLM (i : Fin 4) : Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformDirectional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def directionalPrimitive (v : Fin 4 → ℂ) (i : Fin 4) (p : CPoly) : CPoly :=
  aeval (transverse v i) (Yau.primitive i (aeval (original v i) p))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WarpedAmbientForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Manifold ContinuousLinearMap
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "F" => EuclideanSpace ℝ (Fin 5)
local notation "W" => ℂ

def warpedAmbientForm (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ) :
    (F × W) →L[ℝ] (F × W) →L[ℝ] ℝ :=
  bilinearPullback B (fst ℝ F W) + q^2 • bilinearPullback (innerSL ℝ) (snd ℝ F W)

lemma warpedAmbientForm_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ) (v w : F × W) :
    warpedAmbientForm B q v w = B v.1 w.1 + q^2 * inner ℝ v.2 w.2 := rfl

lemma warpedAmbientForm_smooth (B : M → F →L[ℝ] F →L[ℝ] ℝ) (q : M → ℝ)
    (hB : ContMDiff I 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) ∞ B)
    (hq : ContMDiff I 𝓘(ℝ,ℝ) ∞ q) :
    ContMDiff I 𝓘(ℝ,(F × W) →L[ℝ] (F × W) →L[ℝ] ℝ) ∞
      (fun x ↦ warpedAmbientForm (B x) (q x)) := by
  unfold warpedAmbientForm bilinearPullback
  exact (contMDiff_const.clm_comp (hB.clm_comp contMDiff_const)).add
    (((contDiff_id.pow 2).contMDiff.comp hq).smul contMDiff_const)

lemma warpedAmbientForm_symm (B : F →L[ℝ] F →L[ℝ] ℝ) (q : ℝ)
    (hs : ∀ v w, B v w = B w v) (v w : F × W) :
    warpedAmbientForm B q v w = warpedAmbientForm B q w v := by
  simp only [warpedAmbientForm_apply,hs v.1 w.1,real_inner_comm v.2 w.2]

lemma warpedAmbientForm_pos (B : F →L[ℝ] F →L[ℝ] ℝ) {q : ℝ}
    (hp : ∀ v, v ≠ 0 → 0 < B v v) (hq : 0 < q)
    (v : F × W) (hv : v ≠ 0) : 0 < warpedAmbientForm B q v v := by
  rw [warpedAmbientForm_apply,real_inner_self_eq_norm_sq]
  by_cases h : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun hz ↦ hv (Prod.ext h hz)
    simp only [h,map_zero,zero_add]
    exact mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos (norm_pos_iff.mpr h2))
  · exact add_pos_of_pos_of_nonneg (hp _ h) (mul_nonneg (sq_nonneg q) (sq_nonneg ‖v.2‖))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RadialVolumeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

local instance instDecidableEqFinOfNatNat_solutions_r6182f2_1 : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
attribute [local instance] OAI.Yau.Geometry.instFintypeFinOfNatNat_solutions
def radialVolumeMatrix (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ) (x : Fin 5 → ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  weightedBaseMatrix A rho + replicateCol (Fin 1) ((1-rho) • x) * replicateRow (Fin 1) x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

def sphereWeightedChartMatrix (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (p : Base) (y : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  (sphereChartFrame p y).transpose * weightedBaseMatrix A rho * sphereChartFrame p y

lemma sphereWeightedChartMatrix_posDef (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    (sphereWeightedChartMatrix A rho p y).PosDef := by
  simpa [sphereWeightedChartMatrix,conjTranspose_eq_transpose_of_trivial] using
    (weightedBaseMatrix_posDef hA hr).conjTranspose_mul_mul_same (sphereChartFrame_injective p hy)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SmoothInverseChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Manifold
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_inverse_chart_comp (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) ∞ f)
    (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    ContDiffAt ℝ ∞ (f ∘ (extChartAt I p).symm) y := by
  exact ((hf _).comp y (inverse_chart_smooth_at p hy)).contDiffAt

lemma smooth_inverse_chart_derivative (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) ∞ f)
    (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    ContDiffAt ℝ ∞ (fderiv ℝ (f ∘ (extChartAt I p).symm)) y :=
  (smooth_inverse_chart_comp f hf p hy).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartFrameSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
attribute [local instance] finrank_real_complex_fact'

attribute [local instance] OAI.Yau.Target.instFactEqNatFinrankRealAmbientBaseHAddOfNat_3
lemma sphereChartDerivative_eq_fderiv (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    sphereChartDerivative p y =
      fderiv ℝ ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) y := by
  exact (inverse_chart_comp_derivative _ (contMDiff_coe_sphere (n := 4)) p hy).symm

lemma sphereChartDerivative_smooth_at (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (sphereChartDerivative p) y := by
  apply (smooth_inverse_chart_derivative _ (contMDiff_coe_sphere (n := 4)) p hy).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact sphereChartDerivative_eq_fderiv p hz

lemma sphereChartFrame_smooth_at (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) (i : Fin 5) (j : Fin 4) :
    ContDiffAt ℝ ∞ (fun z ↦ sphereChartFrame p z i j) y := by
  simp_rw [sphereChartFrame_apply]
  exact (contDiffAt_piLp_apply 2).comp y
    ((sphereChartDerivative_smooth_at p hy).clm_apply contDiffAt_const)

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

def baseChartMetric (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (p : Base) (z : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p).symm z))
    (rho ((extChartAt (𝓡 4) p).symm z)) p z

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

include hA hp hr in
lemma baseChartMetric_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w ↦ baseChartMetric A rho p w i j) z := by
  have ha (i j : Fin 5) := smooth_inverse_chart_comp _ (hA i j) p hz
  have hi := matrix_inverse_smooth_at (fun w ↦ A ((extChartAt (𝓡 4) p).symm w)) ha
    (hp _).det_pos.ne'
  have hw (i j : Fin 5) : ContDiffAt ℝ ∞
      (fun w ↦ weightedBaseMatrix (A ((extChartAt (𝓡 4) p).symm w))
        (rho ((extChartAt (𝓡 4) p).symm w)) i j) z :=
    (smooth_inverse_chart_comp rho hr p hz).mul (hi i j)
  simp only [baseChartMetric,sphereWeightedChartMatrix,mul_apply,transpose_apply]
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro l _
    exact (sphereChartFrame_smooth_at p hz l i).mul (hw l k)
  · exact sphereChartFrame_smooth_at p hz k j

include hA hp hr hrp in
lemma baseChartMetric_inverse_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w ↦ (baseChartMetric A rho p w)⁻¹ i j) z := by
  apply matrix_inverse_smooth_at _ (baseChartMetric_smooth_at A rho hA hp hr p hz)
  exact (sphereWeightedChartMatrix_posDef _ (hp _) (hrp _) p hz).det_pos.ne'

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartMetric
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.Yau.Geometry.clmTopology
attribute [local instance] OAI.Yau.Geometry.clmAdd
attribute [local instance] OAI.Yau.Geometry.clmModule
def pullbackMetric (g : E → E →L[ℝ] E →L[ℝ] ℝ) (F : E → E) (x u v : E) : ℝ :=
  g (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PositiveMetric
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positive_metric_injective (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) : Function.Injective g := by
  intro u v huv
  apply sub_eq_zero.mp
  by_contra h
  have hz : g (u-v) = 0 := by rw [map_sub, huv, sub_self]
  have hh := hp (u-v) h
  rw [hz, zero_apply] at hh
  exact (lt_irrefl 0 hh)

variable [FiniteDimensional ℝ E]

def positiveMetricEquiv (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) : E ≃L[ℝ] E →L[ℝ] ℝ :=
  (g.toLinearMap.linearEquivOfInjective (positive_metric_injective g hp)
    dual_continuous_finrank.symm).toContinuousLinearEquiv

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TaylorPolynomial
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def tensorPolynomial : {n : ℕ} →
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ → CPoly
  | 0, T => C (T 0)
  | _n + 1, T => ∑ i : Fin 4, X i * tensorPolynomial (T.curryLeft (Pi.single i 1))

def taylorPolynomial (f : Coord → ℂ) (y : Coord) (m : ℕ) : CPoly :=
  ∑ k ∈ Finset.range (m + 1), C (((k.factorial : ℝ)⁻¹ : ℝ) : ℂ) *
    tensorPolynomial (iteratedFDeriv ℝ k f y)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFrameOps
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {ι : Type*} [Fintype ι]
def removeFrame (g : E →L[ℝ] E →L[ℝ] ℝ) (e : ι → E) (v : E) : E :=
  v - ∑ i, g (e i) v • e i

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothSymmetry
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def directionalList (l : List Coord) (f : Coord → ℂ) : Coord → ℂ :=
  match l with
  | [] => f
  | v :: l => fun x ↦ fderiv ℝ (directionalList l f) x v

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TaylorMatching
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def finiteTaylorSeries (f : Coord → ℂ) (y : Coord) (m : ℕ) :
    FormalMultilinearSeries ℝ Coord ℂ := fun k ↦
  if k ≤ m then (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f y else 0

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedCoordinateOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def densityDrift (W : Coord → ℂ) (a : Fin 4 → Fin 4 → Coord → ℂ)
    (j : Fin 4) (x : Coord) : ℂ :=
  (W x)⁻¹ * ∑ i, coordPartial i (fun z ↦ W z * a i j z) x

def weightedCoordinateOperator (W : Coord → ℂ) (a : Fin 4 → Fin 4 → Coord → ℂ)
    (u : Coord → ℂ) (x : Coord) : ℂ :=
  (W x)⁻¹ * ∑ i, ∑ j,
    coordPartial i (fun z ↦ (W z * a i j z) * coordPartial j u z) x

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ComplexMetricFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def pulledFlux (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (u : _root_.OAI.Yau.Jets.Coord → ℂ) (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  ∑ j, ((chartDensity w p x : ℂ) * complexPrincipal g i j p x) * _root_.OAI.Yau.Jets.coordPartial j u x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereContravariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

attribute [local instance] OAI.Yau.Target.instFactEqNatFinrankRealAmbientBaseHAddOfNat_4
lemma sphereChart_contravariant (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hrad : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i)) :
    frameContravariant A (sphereChartFrame p z) =
      rho • (sphereWeightedChartMatrix A rho p z)⁻¹ := by
  obtain ⟨T,hT⟩ := sphereChartFrame_invariant A hA p hz hrad
  exact invariant_frame_inverse A hA _ (sphereChartFrame_injective p hz) T hT hr

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

def sphereChartTensor (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p : Base) (z : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  frameContravariant (A ((extChartAt (𝓡 4) p).symm z)) (sphereChartFrame p z)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereCotangentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma sphereChartTensor_pullback (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p : Base) (z : BaseModel) :
    sphereChartTensor A p z = frameLeftInverse (sphereChartFrame p z) *
      A ((extChartAt (𝓡 4) p).symm z) * (frameLeftInverse (sphereChartFrame p z)).transpose :=
  frameContravariant_pullback _ _

lemma sphereChart_covector_representative (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v : Fin 4 → ℝ) :
    (sphereChartFrame p z).transpose *ᵥ
      ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v) = v :=
  frameLeftInverse_covector _ (sphereChartFrame_injective p hz) v

lemma sphereChartTensor_pairing (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p : Base) (z : BaseModel) (v w : Fin 4 → ℝ) :
    v ⬝ᵥ (sphereChartTensor A p z *ᵥ w) =
      ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v) ⬝ᵥ
        (A ((extChartAt (𝓡 4) p).symm z) *ᵥ
          ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ w)) := by
  rw [sphereChartTensor_pullback,← mulVec_mulVec,← mulVec_mulVec]
  rw [dotProduct_mulVec,← mulVec_transpose]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereCovectorRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance : Fact (Module.finrank ℝ AmbientBase = 4 + 1) := ⟨by simp [AmbientBase]⟩

lemma sphereCovectorRestriction_smooth (v : AmbientBase) :
    ContMDiff (𝓡 4) ((𝓡 4).prod 𝓘(ℝ,CotangentModel)) ∞
      (fun x ↦ TotalSpace.mk' CotangentModel
        (E := SphereCotangent) x (sphereCovectorRestriction x v)) := by
  let f : Base → ℝ := fun x ↦ ⟪v,(x : AmbientBase)⟫
  have hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f :=
    (innerSL ℝ v).contMDiff.comp (contMDiff_coe_sphere (n := 4))
  have he (x : Base) : mfderiv (𝓡 4) 𝓘(ℝ,ℝ) f x = sphereCovectorRestriction x v := by
    have h := mfderiv_comp x ((innerSL ℝ v).mdifferentiableAt)
      ((contMDiff_coe_sphere (n := 4) (m := ∞)).mdifferentiable (by simp) x)
    rw [mfderiv_eq_fderiv, (innerSL ℝ v).fderiv] at h
    exact h
  simpa only [he] using Yau.Geometry.smooth_ambient_derivative f hf

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicAmbientSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)

attribute [local instance] OAI.Yau.Target.instNormedAddCommGroupCotangentModel
attribute [local instance] OAI.Yau.Target.instNormedSpaceRealCotangentModel
attribute [local instance] OAI.Yau.Target.instNormedAddCommGroupContinuousLinearMapRealIdCotangentModel
attribute [local instance] OAI.Yau.Target.instNormedSpaceRealContinuousLinearMapIdCotangentModel
attribute [local instance] OAI.Yau.Target.instAddCommGroupSphereCotangent
attribute [local instance] OAI.Yau.Target.instModuleRealSphereCotangent
attribute [local instance] OAI.Yau.Target.instAddCommGroupContinuousLinearMapRealIdSphereCotangent
attribute [local instance] OAI.Yau.Target.instModuleRealContinuousLinearMapIdSphereCotangent
attribute [local instance] OAI.Yau.Target.instTopologicalSpaceContinuousLinearMapRealIdSphereCotangent
attribute [local instance] OAI.Yau.Target.instIsTopologicalAddGroupContinuousLinearMapRealIdSphereCotangent
attribute [local instance] OAI.Yau.Target.instContinuousSMulRealContinuousLinearMapIdSphereCotangent
attribute [local instance] OAI.Yau.Target.instTopologicalSpaceTotalSpaceElemEuclideanSpaceRealFinOfNatNatBaseContinuousLinearMapIdCotangentModelSphereCotangent
include hA in
lemma intrinsic_restriction_pairing_smooth (v w : AmbientBase) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞
      (fun x ↦ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)) := by
  have h := hA.clm_bundle_apply₂ (sphereCovectorRestriction_smooth v)
    (sphereCovectorRestriction_smooth w)
  intro x
  have hh := (contMDiffAt_totalSpace.mp (h x)).2
  simpa using hh

local instance localInst_r6182f2_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
include hA in
lemma intrinsicAmbientMatrix_smooth (i j : Fin 5) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ intrinsicAmbientMatrix A x i j) := by
  let v := EuclideanSpace.basisFun (Fin 5) ℝ i
  let w := EuclideanSpace.basisFun (Fin 5) ℝ j
  have hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ ⟪(x : AmbientBase),v⟫) := by
    have h := (innerSL ℝ v).contMDiff.comp (contMDiff_coe_sphere (n := 4) (m := ∞))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext x; exact real_inner_comm _ _)
  have hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ ⟪(x : AmbientBase),w⟫) := by
    have h := (innerSL ℝ w).contMDiff.comp (contMDiff_coe_sphere (n := 4) (m := ∞))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext x; exact real_inner_comm _ _)
  exact (intrinsic_restriction_pairing_smooth A hA v w).add (hv.smul hw)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicChartTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def sphereCoordinateCovector (p : Base) (z : BaseModel) (v : Fin 4 → ℝ) :
    SphereCotangent ((extChartAt (𝓡 4) p).symm z) :=
  sphereCovectorRestriction _ (WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v))

lemma sphereCoordinateCovector_apply (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v w : Fin 4 → ℝ) :
    sphereCoordinateCovector p z v
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z (WithLp.toLp 2 w)) =
      v ⬝ᵥ w := by
  change ⟪WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v),
    sphereChartDerivative p z (WithLp.toLp 2 w)⟫ = _
  have he : ∀ u t : AmbientBase, ⟪u,t⟫ = (⇑u) ⬝ᵥ ⇑t := by
    intro u t
    simp [PiLp.inner_apply,dotProduct,mul_comm]
  rw [he]
  change ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v) ⬝ᵥ
    (fun i ↦ sphereChartDerivative p z (WithLp.toLp 2 w) i) = _
  rw [← sphereChartFrame_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    sphereChart_covector_representative p hz]

lemma sphereCoordinateCovector_unique (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (v : Fin 4 → ℝ)
    (ell : SphereCotangent ((extChartAt (𝓡 4) p).symm z))
    (hell : ∀ w : Fin 4 → ℝ, ell
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z (WithLp.toLp 2 w)) = v ⬝ᵥ w) :
    ell = sphereCoordinateCovector p z v := by
  have hs := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 4) hz).surjective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at hs
  ext u
  obtain ⟨w,rfl⟩ := hs u
  exact (hell (WithLp.ofLp w)).trans (sphereCoordinateCovector_apply p hz v (WithLp.ofLp w)).symm

lemma sphereChart_representative_radial (p : Base) (z : BaseModel) (v : Fin 4 → ℝ) :
    ⟪((extChartAt (𝓡 4) p).symm z : AmbientBase),
      WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v)⟫ = 0 := by
  have he : ∀ u t : AmbientBase, ⟪u,t⟫ = (⇑u) ⬝ᵥ ⇑t := by
    intro u t
    simp [PiLp.inner_apply,dotProduct,mul_comm]
  rw [he, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose,
    frameLeftInverse, ← mulVec_mulVec, sphereChartFrame_orthogonal, mulVec_zero, zero_dotProduct]

lemma intrinsicAmbientMatrix_chart_pairing (A : IntrinsicTensor)
    (p : Base) (z : BaseModel) (v w : Fin 4 → ℝ) :
    v ⬝ᵥ (sphereChartTensor (intrinsicAmbientMatrix A) p z *ᵥ w) =
      A ((extChartAt (𝓡 4) p).symm z)
        (sphereCoordinateCovector p z v) (sphereCoordinateCovector p z w) := by
  rw [sphereChartTensor_pairing]
  have h := intrinsicAmbientMatrix_tangent A ((extChartAt (𝓡 4) p).symm z)
    (WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ v))
    (WithLp.toLp 2 ((frameLeftInverse (sphereChartFrame p z)).transpose *ᵥ w))
    (sphereChart_representative_radial p z v)
  rw [ambientMatrixForm_dot] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

def intrinsicSphereChartTensor (A : IntrinsicTensor) (p : Base) (z : BaseModel) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j ↦
  A ((extChartAt (𝓡 4) p).symm z)
    (sphereCoordinateCovector p z (Pi.single i 1))
    (sphereCoordinateCovector p z (Pi.single j 1))

lemma intrinsicSphereChartTensor_eq (A : IntrinsicTensor) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor A p z = sphereChartTensor (intrinsicAmbientMatrix A) p z := by
  ext i j
  have h := intrinsicAmbientMatrix_chart_pairing A p z (Pi.single i 1) (Pi.single j 1)
  simpa [intrinsicSphereChartTensor] using h.symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_DirectionTripleAlgebra
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def transverseTriple (eps : ℝ) : Fin 3 → _root_.OAI.Yau.Jets.Coord :=
  ![Pi.single 1 1, Pi.single 1 1 + eps • Pi.single 2 1,
    Pi.single 1 1 + eps • Pi.single 3 1]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AdmissibleDirectionTriple
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def transverseDirection (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (b eps : ℝ) (j : Fin 3) : _root_.OAI.Yau.Jets.Coord :=
  b • metricNormalize g (e (transverseTriple eps j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseContactFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff Topology
open MvPolynomial Filter
noncomputable section
variable {T : Type*} [TopologicalSpace T]

def realTensorMap (k : ℕ) :
    (Coord [×k]→L[ℝ] ℂ) →L[ℝ] (Coord [×k]→L[ℝ] ℝ) :=
  ({ toFun := fun A ↦ Complex.reCLM.compContinuousMultilinearMap A
     map_add' := by intro A B; ext v; simp
     map_smul' := by intro c A; ext v; simp } :
    (Coord [×k]→L[ℝ] ℂ) →ₗ[ℝ] (Coord [×k]→L[ℝ] ℝ)).mkContinuous ‖Complex.reCLM‖
      (fun A ↦ Complex.reCLM.norm_compContinuousMultilinearMap_le A)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothDefectBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

def UniformSmoothBounded (s : Set T) (R : ℝ) (f : T → Coord → ℂ) : Prop :=
  (∀ t, ContDiff ℝ ∞ (f t)) ∧
    ∀ k, ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f t) x C

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SmoothFiniteResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def revalLinear (x : Coord) : CPoly →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval (fun i ↦ (x i : ℂ))).toLinearMap

def secondOrderAt (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (x : Coord) : CPoly →ₗ[ℂ] ℂ :=
  (∑ i, ∑ j, g i j x • ((revalLinear x).comp
    ((pderiv i).toLinearMap.comp (pderiv j).toLinearMap))) +
    ∑ i, b i x • ((revalLinear x).comp (pderiv i).toLinearMap)

def transportAt (W : Fin 4 → Coord → ℂ) (c : Coord → ℂ)
    (x : Coord) : CPoly →ₗ[ℂ] ℂ :=
  (∑ i, W i x • ((revalLinear x).comp (pderiv i).toLinearMap)) + c x • revalLinear x

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CutoffResidualProductLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Jets

open scoped ContDiff

def finiteResidualCore (E a t0 : Coord → ℂ) (tj : ℕ → Coord → ℂ)
    (L : Coord → ℂ) (J : ℕ) (N : ℝ) : Coord → ℂ := fun x ↦
  (N : ℂ)^2 * (E x * a x) + (N : ℂ) * t0 x +
    (∑ j ∈ Finset.range J, ((N : ℂ)⁻¹^j) * tj j x) + ((N : ℂ)⁻¹^J) * L x

end Yau.Jets

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CommutatorBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def cutoffCommutator (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) (N : ℝ) (y : Coord) : Coord → ℂ :=
  fun x ↦ smoothSecondOrder g b (fun z ↦ Yau.Waves.scaledCutoff N y z • u z) x -
    Yau.Waves.scaledCutoff N y x • smoothSecondOrder g b u x

open Filter
open scoped Topology

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_Logarithm
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

def normalizedLogJet (N : ℝ) (V : _root_.OAI.Yau.Jets.Coord → ℂ) (x v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (N:ℂ)⁻¹ * (fderiv ℝ V x v / V x)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransverseSpanning
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def transverseEnergy (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) : ℝ := ∑ j, (g (q j) v)^2

end
end Yau.Geometry

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

def intrinsicRoundFlux (f : Base → ℝ) (p : Base) (i : Fin 4) (z : BaseModel) : ℝ :=
  roundChartDensity p z * ∑ j, intrinsicSphereChartTensor A p z i j *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ j)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicLiftGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)

include hs hp hrp in
lemma intrinsic_horizontal_inverse (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    (sphereWeightedChartMatrix (intrinsicAmbientMatrix A ((extChartAt (𝓡 4) p).symm z))
      (rho ((extChartAt (𝓡 4) p).symm z)) p z)⁻¹ =
      (rho ((extChartAt (𝓡 4) p).symm z))⁻¹ • intrinsicSphereChartTensor A p z := by
  rw [intrinsicSphereChartTensor_eq]
  change _ = _ • Yau.Geometry.frameContravariant _ _
  rw [sphereChart_contravariant _ (intrinsicAmbientMatrix_posDef A hs hp _) (hrp _) p hz
    (intrinsicAmbientMatrix_radial A _), smul_smul, inv_mul_cancel₀ (hrp _).ne', one_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveContravariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def positiveContravariantEquiv (A : (E →L[ℝ] ℝ) →L[ℝ] E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (A α)) : (E →L[ℝ] ℝ) ≃L[ℝ] E :=
  (A.toLinearMap.linearEquivOfInjective (positiveContravariant_injective A hp)
    dual_continuous_finrank).toContinuousLinearEquiv

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def intrinsicChartCoefficient (A : IntrinsicTensor) (ρ : Base → ℝ)
    (p : Base) (z : BaseModel) : CoefficientPoint BaseModel :=
  (matrixContravariant (intrinsicSphereChartTensor A p z), ρ ((extChartAt (𝓡 4) p).symm z))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hA hs hp in
lemma intrinsicSphereChartTensor_smoothAt (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w ↦ intrinsicSphereChartTensor A p w i j) z := by
  have h := baseChartMetric_inverse_smooth_at (intrinsicAmbientMatrix A) (fun _ ↦ 1)
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp)
    contMDiff_const (fun _ ↦ zero_lt_one) p hz i j
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  have he := intrinsic_horizontal_inverse A hs hp (fun _ ↦ 1) (fun _ ↦ zero_lt_one) p hw
  simpa only [inv_one,one_smul,baseChartMetric] using (congrArg (fun B : Matrix (Fin 4) (Fin 4) ℝ ↦ B i j) he).symm

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

local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_5_r6182f2_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
def roundChartMetric (p : Base) (y : BaseModel) : BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ :=
  bilinearPullback ambientRoundBilinear (sphereChartDerivative p y)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCoefficientJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

def roundCoefficients (y : BaseModel) : CoefficientPoint BaseModel :=
  (ContinuousLinearMap.inverse (roundChartMetric seedPoint y),1)

def roundCoefficientJet (y : BaseModel) : CoefficientFirstJet BaseModel :=
  (roundCoefficients y,fderiv ℝ roundCoefficients y)

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

def seedCoordEquiv : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] BaseModel :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).symm

def seedCoordReal : _root_.OAI.Yau.Jets.Coord → ℝ := seedRealChart ∘ seedCoordEquiv

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

def seedCoordBranch : Set _root_.OAI.Yau.Jets.Coord := {x | seedChartAmbient (seedCoordEquiv x) ∈ seedLogDomain}

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedChartScalarExtension
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

def seedSphereFromCoord (x : Yau.Jets.Coord) : Base :=
  (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)

def seedSphereToCoord (p : Base) : Yau.Jets.Coord :=
  seedCoordEquiv.symm ((extChartAt (𝓡 4) seedPoint) p)

lemma seedSphereFromCoord_continuous : Continuous seedSphereFromCoord :=
  seedSphereChart_inverse_continuous.comp seedCoordEquiv.continuous

lemma seedSphereToCoord_from (x : Yau.Jets.Coord) :
    seedSphereToCoord (seedSphereFromCoord x) = x := by
  unfold seedSphereToCoord seedSphereFromCoord
  rw [(extChartAt (𝓡 4) seedPoint).right_inv (by rw [centeredSphereChart_target]; trivial)]
  exact seedCoordEquiv.symm_apply_apply x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartConformal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereChartDerivative_stereo (p : Base) (y v : BaseModel) :
    sphereChartDerivative p y v =
      fderiv ℝ (stereoInvFunAux (-(p:AmbientBase))) (centeredSphereIsometry p y)
        (centeredSphereIsometry p v) := by
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]
  have h := (((contDiff_stereoInvFunAux (v := -(p:AmbientBase)) (m := ∞)).differentiable
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (centeredSphereIsometry p y)).hasFDerivAt).comp y
      (centeredSphereIsometry p).toContinuousLinearMap.hasFDerivAt
  exact congrArg (fun L : BaseModel →L[ℝ] AmbientBase ↦ L v) h.fderiv

lemma sphereChartDerivative_conformal (p : Base) (y u v : BaseModel) :
    ⟪sphereChartDerivative p y u,sphereChartDerivative p y v⟫ =
      (4/(‖y‖^2+4))^2*⟪u,v⟫ := by
  have hp : ⟪(p:AmbientBase),(p:AmbientBase)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖(p:AmbientBase)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
    rw [hn,one_pow]
  have ho (v : BaseModel) : ⟪centeredSphereIsometry p v,(p:AmbientBase)⟫ = 0 :=
    (real_inner_comm _ _).trans (centeredSphereIsometry_orthogonal p v)
  rw [sphereChartDerivative_stereo,sphereChartDerivative_stereo,
    stereoInvFunAux_fderiv,stereoInvFunAux_fderiv]
  simp only [stereoReciprocal,stereoNumerator,
    (centeredSphereIsometry p).norm_map,(centeredSphereIsometry p).inner_map_map,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    inner_neg_left,inner_neg_right,ho,
    real_inner_comm (centeredSphereIsometry p y) (p:AmbientBase),
    real_inner_comm (centeredSphereIsometry p v) (p:AmbientBase),hp]
  simp only [real_inner_self_eq_norm_sq,real_inner_comm u y,real_inner_comm v y]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  field_simp
  ring

lemma sphereRoundChartMatrix_conformal (p : Base) (y : BaseModel) :
    sphereRoundChartMatrix p y = (4/(‖y‖^2+4))^2 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  rw [sphereRoundChartMatrix_inner,sphereChartDerivative_conformal]
  rw [(EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite]
  simp [Matrix.one_apply,mul_ite]

lemma roundChartDensity_conformal (p : Base) (y : BaseModel) :
    roundChartDensity p y = (4/(‖y‖^2+4))^4 := by
  rw [roundChartDensity,sphereRoundChartMatrix_conformal,Matrix.det_smul]
  simp only [Fintype.card_fin,Matrix.det_one,mul_one]
  have h : ((4/(‖y‖^2+4))^2)^4 = ((4/(‖y‖^2+4))^4)^2 := by ring
  rw [h,Real.sqrt_sq (by positivity)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
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
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst3
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst4
local instance intrinsicRoundPerturbationLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicRoundPerturbationLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicRoundPerturbationLocalInst7 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicRoundPerturbationLocalInst8 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst9
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst10
local instance intrinsicRoundPerturbationLocalInst11 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicRoundPerturbationLocalInst12 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicRoundPerturbationLocalInst13 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance
local instance intrinsicRoundPerturbationLocalInst14 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicRoundPerturbationLocalInst15 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicRoundPerturbationLocalInst16 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance intrinsicRoundPerturbationLocalInst17 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicRoundPerturbationLocalInst18 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSourceOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def smoothFluxOperator (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  v x * ∑ i, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j u z) x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SeededResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def realSourceResidual (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (lam : ℝ) (u : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+(lam:ℂ)*(u x:ℂ)

end
end Yau.Geometry

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

lemma seedCoordEquiv_basis (i : Fin 4) :
    seedCoordEquiv (Pi.single i 1) = EuclideanSpace.basisFun (Fin 4) ℝ i := by
  ext j
  simp [seedCoordEquiv, EuclideanSpace.basisFun_apply]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_MetricProjectionBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def metricPerpProjection (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e t : _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord :=
  t-g e t • e

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedHessianStability
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

def weightedHessianValue (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p t : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  H p p/(g p p+4)+H t t

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGainStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

abbrev sourceDirectionalAdmissibleOn
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (D : Set _root_.OAI.Yau.Jets.Coord) : Prop :=
  ∀ x ∈ D, metricGradient g S x ≠ 0 ∧
    ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordPatchTopology
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped Topology
noncomputable section

def seedCoordPatch (r : ℝ) : Set _root_.OAI.Yau.Jets.Coord := seedCoordEquiv ⁻¹' ball (0 : BaseModel) r

def seedCoordCube (a : ℝ) : Set _root_.OAI.Yau.Jets.Coord := Icc (fun _ ↦ -a) (fun _ ↦ a)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SeedCoefficientPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def SeedEnvelopePlaced (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (r a : ℝ) (K : Set _root_.OAI.Yau.Jets.Coord) (T : ℝ) : Prop :=
  ∃ (S : _root_.OAI.Yau.Jets.Coord → ℝ) (gap : ℝ) (C V : Set _root_.OAI.Yau.Jets.Coord), 0 < gap ∧
    ContDiffOn ℝ ∞ S seedCoordBranch ∧ IsCompact C ∧ C ⊆ seedCoordPatch r ∧
    seedCoordCube a ∪ K ⊆ C ∧
    (∀ x ∈ seedCoordCube a ∪ K, seedCoordReal x+gap ≤ S x) ∧
    (∀ x ∉ C, S x ≤ seedCoordReal x-gap) ∧
    IsOpen V ∧ closure (seedCoordPatch r) ⊆ V ∧ V ⊆ seedCoordBranch ∧
    sourceDirectionalAdmissibleOn g S V ∧
    T < ∫ x in seedCoordCube a, corrugationOldSlope g S x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PlacedEnvelopeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

structure PlacedEnvelopeData (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (r a : ℝ) (K : Set _root_.OAI.Yau.Jets.Coord) (T : ℝ) where
  S : _root_.OAI.Yau.Jets.Coord → ℝ
  gap : ℝ
  U : Set _root_.OAI.Yau.Jets.Coord
  Ω : Set _root_.OAI.Yau.Jets.Coord
  V : Set _root_.OAI.Yau.Jets.Coord
  C : Set _root_.OAI.Yau.Jets.Coord
  gap_pos : 0 < gap
  smooth : ContDiffOn ℝ ∞ S seedCoordBranch
  compact_C : IsCompact C
  C_patch : C ⊆ seedCoordPatch r
  inner_C : seedCoordCube a ∪ K ⊆ C
  inner_gap : ∀ x ∈ seedCoordCube a ∪ K, seedCoordReal x+gap ≤ S x
  outer_gap : ∀ x ∉ C, S x ≤ seedCoordReal x-gap
  open_V : IsOpen V
  patch_V : closure (seedCoordPatch r) ⊆ V
  V_branch : V ⊆ seedCoordBranch
  admissible : sourceDirectionalAdmissibleOn g S V
  gain : T < ∫ x in seedCoordCube a, corrugationOldSlope g S x
  open_U : IsOpen U
  open_Ω : IsOpen Ω
  C_U : C ⊆ U
  compact_closure_U : IsCompact (closure U)
  closure_U_Ω : closure U ⊆ Ω
  compact_closure_Ω : IsCompact (closure Ω)
  closure_Ω_patch : closure Ω ⊆ seedCoordPatch r
  compact_high : IsCompact {x | x ∈ seedCoordPatch r ∧ seedCoordReal x-gap/2 ≤ S x}
  high_U : {x | x ∈ seedCoordPatch r ∧ seedCoordReal x-gap/2 ≤ S x} ⊆ U

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

def coordPartial (u : Coord n → ℝ) (x : Coord n) (i : Fin n) : ℝ :=
  fderiv ℝ u x (Pi.single i 1)

def coordDiv (V : Coord n → Coord n) (x : Coord n) : ℝ :=
  ∑ i, coordPartial (fun y ↦ V y i) x i

def weightedDiv (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (x : Coord n) : ℝ :=
  (gamma x)⁻¹ * coordDiv (fun y i ↦ gamma y * V y i) x

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

lemma coord_covector_sum (L : Yau.Jets.Coord →L[ℝ] ℝ) (v : Yau.Jets.Coord) :
    (∑ i, L (Pi.single i 1)*v i) = L v := by
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hv]
  simp [mul_comm]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundSupportedCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

def roundCoordDensity (x : Yau.Jets.Coord) : ℝ :=
  roundChartDensity seedPoint (seedCoordEquiv x)

lemma roundCoordDensity_pos (x : Yau.Jets.Coord) : 0 < roundCoordDensity x := by
  rw [roundCoordDensity,roundChartDensity_conformal]
  positivity

lemma roundCoordDensity_smooth : ContDiff ℝ ∞ roundCoordDensity := by
  have he : roundCoordDensity = fun x : Yau.Jets.Coord ↦ (4/(‖seedCoordEquiv x‖^2+4))^4 :=
    funext (fun x ↦ roundChartDensity_conformal seedPoint (seedCoordEquiv x))
  rw [he]
  exact (contDiff_const.div (((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const)
    (fun x ↦ by change ‖seedCoordEquiv x‖^2+4 ≠ 0; positivity)).pow 4

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

local instance intrinsicCorrectedChartLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTransition
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

def sphereChartCoordMap (p : Base) (x : Yau.Jets.Coord) : Base :=
  (extChartAt (𝓡 4) p).symm (seedCoordEquiv x)

def sphereChartTransitionDomain (p q : Base) : Set Yau.Jets.Coord :=
  sphereChartCoordMap p ⁻¹' (extChartAt (𝓡 4) q).source

def sphereChartTransition (p q : Base) (x : Yau.Jets.Coord) : Yau.Jets.Coord :=
  seedCoordEquiv.symm ((extChartAt (𝓡 4) q) (sphereChartCoordMap p x))

lemma sphereChartCoordMap_smooth (p : Base) : ContMDiff 𝓘(ℝ,Yau.Jets.Coord) (𝓡 4) ∞ (sphereChartCoordMap p) := by
  intro x
  exact (inverse_chart_smooth_at (I := 𝓡 4) p
    (y := seedCoordEquiv x) (by rw [centeredSphereChart_target]; trivial)).comp x
      seedCoordEquiv.contDiff.contMDiff.contMDiffAt

lemma sphereChartCoordMap_source (p : Base) (x : Yau.Jets.Coord) :
    sphereChartCoordMap p x ∈ (extChartAt (𝓡 4) p).source :=
  (extChartAt (𝓡 4) p).map_target (by rw [centeredSphereChart_target]; trivial)

lemma sphereChartTransitionDomain_open (p q : Base) : IsOpen (sphereChartTransitionDomain p q) :=
  (isOpen_extChartAt_source q).preimage (sphereChartCoordMap_smooth p).continuous

lemma sphereChartTransition_smoothOn (p q : Base) :
    ContDiffOn ℝ ∞ (sphereChartTransition p q) (sphereChartTransitionDomain p q) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  have hc := (contMDiffAt_extChartAt' (I := 𝓡 4) (x := q) (by simpa [sphereChartTransitionDomain] using hx)).comp x (sphereChartCoordMap_smooth p x)
  exact (seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp x hc).contDiffAt

lemma sphereChartTransition_point (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartCoordMap q (sphereChartTransition p q x) = sphereChartCoordMap p x := by
  unfold sphereChartCoordMap sphereChartTransition
  rw [seedCoordEquiv.apply_symm_apply]
  exact (extChartAt (𝓡 4) q).left_inv hx

lemma sphereChartTransition_mem (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartTransition p q x ∈ sphereChartTransitionDomain q p := by
  change sphereChartCoordMap q (sphereChartTransition p q x) ∈ (extChartAt (𝓡 4) p).source
  rw [sphereChartTransition_point p q hx]
  exact sphereChartCoordMap_source p x

lemma sphereChartTransition_inverse (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartTransition q p (sphereChartTransition p q x) = x := by
  rw [sphereChartTransition,sphereChartTransition_point p q hx]
  unfold sphereChartCoordMap
  rw [(extChartAt (𝓡 4) p).right_inv (by rw [centeredSphereChart_target]; trivial)]
  exact seedCoordEquiv.symm_apply_apply x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferentialCoordinates
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
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def sphereDifferential (u : Base → ℝ) (p : Base) : SphereCotangent p :=
  mfderiv (𝓡 4) 𝓘(ℝ,ℝ) u p

lemma spherePullback_smooth (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (p : Base) :
    ContDiff ℝ ∞ (u ∘ sphereChartCoordMap p) :=
  (hu.comp (sphereChartCoordMap_smooth p)).contDiff

lemma sphereDifferential_chart_apply (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (p : Base) (x w : Yau.Jets.Coord) :
    sphereDifferential u (sphereChartCoordMap p x)
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm
        (seedCoordEquiv x) (seedCoordEquiv w)) =
      fderiv ℝ (u ∘ sphereChartCoordMap p) x w := by
  have hi := (inverse_chart_smooth_at (I := 𝓡 4) p (y := seedCoordEquiv x)
    (by rw [centeredSphereChart_target]; trivial)).mdifferentiableAt (by simp)
  have hm := mfderiv_comp x hi seedCoordEquiv.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv,seedCoordEquiv.fderiv] at hm
  have h := mfderiv_comp x (hu.mdifferentiable (by simp) (sphereChartCoordMap p x))
    ((sphereChartCoordMap_smooth p).mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (u ∘ sphereChartCoordMap p) x = _ at h
  change mfderiv 𝓘(ℝ,Yau.Jets.Coord) (𝓡 4) (sphereChartCoordMap p) x = _ at hm
  rw [hm] at h
  exact (congrArg (fun L : Yau.Jets.Coord →L[ℝ] ℝ ↦ L w) h).symm

lemma sphereDifferential_chart (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (p : Base) (x : Yau.Jets.Coord) :
    sphereDifferential u (sphereChartCoordMap p x) =
      sphereCoordinateCovector p (seedCoordEquiv x)
        (fun i ↦ Yau.coordPartial (u ∘ sphereChartCoordMap p) x i) := by
  apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
  intro w
  exact (sphereDifferential_chart_apply u hu p x w).trans (coord_covector_sum _ w).symm

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

lemma real_coordPartial_smooth (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (fun x ↦ coordPartial f x i) :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end Yau

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

def intrinsicRealPrincipal (A : IntrinsicTensor) (p : Base) (x : Yau.Jets.Coord) :
    Matrix (Fin 4) (Fin 4) ℝ := intrinsicSphereChartTensor A p (seedCoordEquiv x)

lemma intrinsicRealPrincipal_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicRealPrincipal A p x i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p
    (by rw [centeredSphereChart_target]; trivial) i j).comp x seedCoordEquiv.contDiff.contDiffAt

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicDifferentialPairChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsic_differential_pair_chart (A : IntrinsicTensor) (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (p : Base) (x : Yau.Jets.Coord) :
    A (sphereChartCoordMap p x) (sphereDifferential u (sphereChartCoordMap p x))
      (sphereDifferential v (sphereChartCoordMap p x)) =
      ∑ i, ∑ j, Yau.coordPartial (u ∘ sphereChartCoordMap p) x i*
        intrinsicRealPrincipal A p x i j*Yau.coordPartial (v ∘ sphereChartCoordMap p) x j := by
  rw [sphereDifferential_chart u hu,sphereDifferential_chart v hv]
  change A ((extChartAt (𝓡 4) p).symm (seedCoordEquiv x)) _ _ = _
  rw [← intrinsicAmbientMatrix_chart_pairing,← intrinsicSphereChartTensor_eq]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,intrinsicRealPrincipal,mul_assoc]

lemma intrinsic_differential_pair_pullback_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ A (sphereChartCoordMap p x)
      (sphereDifferential u (sphereChartCoordMap p x)) (sphereDifferential v (sphereChartCoordMap p x))) := by
  simp_rw [intrinsic_differential_pair_chart A u v hu hv]
  exact ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
    (((Yau.real_coordPartial_smooth _ (spherePullback_smooth u hu p) i).mul
      (intrinsicRealPrincipal_smooth A hA hs hp p i j)).mul
        (Yau.real_coordPartial_smooth _ (spherePullback_smooth v hv p) j))))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereTransitionFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereTransitionFrameDim_r6182f2_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
lemma sphereChartCoordMap_ambient_derivative (p : Base) (x : Yau.Jets.Coord) :
    fderiv ℝ (fun y ↦ (sphereChartCoordMap p y : AmbientBase)) x =
      (sphereChartDerivative p (seedCoordEquiv x)).comp seedCoordEquiv.toContinuousLinearMap := by
  change fderiv ℝ (((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) ∘ seedCoordEquiv) x = _
  rw [seedCoordEquiv.comp_right_fderiv,
    sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)]

lemma sphereChartTransition_frame_derivative (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) (v : Yau.Jets.Coord) :
    sphereChartDerivative q (seedCoordEquiv (sphereChartTransition p q x))
      (seedCoordEquiv (fderiv ℝ (sphereChartTransition p q) x v)) =
      sphereChartDerivative p (seedCoordEquiv x) (seedCoordEquiv v) := by
  have hq : ContDiff ℝ ∞ (fun y ↦ (sphereChartCoordMap q y : AmbientBase)) :=
    ((contMDiff_coe_sphere (n := 4)).comp (sphereChartCoordMap_smooth q)).contDiff
  have hF := (sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)
  have he : (fun y ↦ (sphereChartCoordMap q y : AmbientBase)) ∘ sphereChartTransition p q =ᶠ[𝓝 x]
      (fun y ↦ (sphereChartCoordMap p y : AmbientBase)) := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    exact congrArg (Subtype.val : Base → AmbientBase) (sphereChartTransition_point p q hy)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x (hq.differentiable (by simp) _) (hF.differentiableAt (by simp)),
    sphereChartCoordMap_ambient_derivative,sphereChartCoordMap_ambient_derivative] at hd
  exact congrArg (fun L : Yau.Jets.Coord →L[ℝ] AmbientBase ↦ L v) hd

lemma sphereChartTransition_frame (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartFrame p (seedCoordEquiv x) =
      sphereChartFrame q (seedCoordEquiv (sphereChartTransition p q x)) * jacobian (sphereChartTransition p q) x := by
  ext i j
  have h := congrArg (fun v : AmbientBase ↦ v i)
    (sphereChartTransition_frame_derivative p q hx (Pi.single j 1))
  rw [seedCoordEquiv_basis] at h
  have hm := sphereChartFrame_mulVec q (seedCoordEquiv (sphereChartTransition p q x))
    (fderiv ℝ (sphereChartTransition p q) x (Pi.single j 1))
  have hm' := congrFun hm i
  change _ = (sphereChartDerivative q (seedCoordEquiv (sphereChartTransition p q x))
    (seedCoordEquiv (fderiv ℝ (sphereChartTransition p q) x (Pi.single j 1)))) i at hm'
  rw [sphereChartFrame_apply]
  exact h.symm.trans hm'.symm

lemma sphereChartTransition_round_matrix (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereRoundChartMatrix p (seedCoordEquiv x) =
      (jacobian (sphereChartTransition p q) x).transpose *
        sphereRoundChartMatrix q (seedCoordEquiv (sphereChartTransition p q x)) *
          jacobian (sphereChartTransition p q) x := by
  simp only [sphereRoundChartMatrix,sphereChartTransition_frame p q hx,transpose_mul,Matrix.mul_assoc]

lemma sphereChartTransition_round_density (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    roundChartDensity p (seedCoordEquiv x) =
      |(jacobian (sphereChartTransition p q) x).det| *
        roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)) := by
  have hd : (sphereRoundChartMatrix p (seedCoordEquiv x)).det =
      (jacobian (sphereChartTransition p q) x).det^2 *
        (sphereRoundChartMatrix q (seedCoordEquiv (sphereChartTransition p q x))).det := by
    rw [sphereChartTransition_round_matrix p q hx]
    simp only [det_mul,det_transpose]
    ring
  unfold roundChartDensity
  rw [hd,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFrequencyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

def sourceFrequency (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (q : _root_.OAI.Yau.Jets.Coord) (s : ℝ) : _root_.OAI.Yau.Jets.Coord :=
  fun i ↦ g q (Pi.single i 1)/s

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledSeedBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def rescaledSeed (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ) (N s σ : ℝ) (x v : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v) /
    (σ*Real.exp (fderiv ℝ S x v / s))

def rescaledSeedPhase (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (p : _root_.OAI.Yau.Jets.Coord × ℝ) (v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (S0 (p.1+p.2 • v):ℂ)+Complex.I*(T0 (p.1+p.2 • v):ℂ)

def rescaledSeedNormalizer (S : _root_.OAI.Yau.Jets.Coord → ℝ) (p : _root_.OAI.Yau.Jets.Coord × ℝ) (v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (Real.exp (-p.2 * fderiv ℝ S p.1 v):ℂ)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateTransverseDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

def transverseInclusion (j : Fin 4) : TransverseCoord →L[ℝ] _root_.OAI.Yau.Jets.Coord where
  toFun := Fin.insertNth (α := fun _ : Fin 4 ↦ ℝ) j 0
  map_add' := by
    intro x y
    ext k
    induction k using j.succAboveCases <;> simp
  map_smul' := by
    intro a x
    ext k
    induction k using j.succAboveCases <;> simp
  cont := by
    apply continuous_pi
    intro k
    induction k using j.succAboveCases
    · simpa using (continuous_const : Continuous (fun _ : TransverseCoord ↦ (0:ℝ)))
    · simpa using continuous_apply _

def transverseDisk (r : ℝ) : Set TransverseCoord :=
  {z | Real.sqrt (∑ k : Fin 3, (z k)^2) ≤ r}

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransverseCylinderVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def transverseCylinder (r : ℝ) : Set _root_.OAI.Yau.Jets.Coord :=
  {z | z 0 ∈ Icc (-1:ℝ) 1 ∧ Fin.tail z ∈ transverseDisk r}

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NormalizedRescaling
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def normalizedRescaling (f : _root_.OAI.Yau.Jets.Coord → ℂ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N s σ : ℝ) (x v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (σ⁻¹:ℂ)*rescaledSeedNormalizer S (x,s⁻¹) v*f (x+(N*s)⁻¹ • v)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_RescaledGaussianField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

def rescaledGaussianField (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N s σ : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (coeff : ι × Fin 2 → ℝ) (v : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v)+
    gaussianWaveField V coeff (x+(N*s)⁻¹ • v)) /
      (σ*Real.exp (fderiv ℝ S x v/s))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CubeGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Set
open scoped ENNReal ContDiff
noncomputable section

def partialCubeControl (f : _root_.OAI.Yau.Jets.Coord → ℝ) (ds : List (Fin 4)) : ℝ≥0∞ :=
  cubeControl (partialJet f) [0,1,2,3] ds 0

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledPhaseDefect
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

def rescaledPhaseDefect (phi : _root_.OAI.Yau.Jets.Coord → ℂ) (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ)
    (N s : ℝ) (x v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (N:ℂ)*(phi (x+(N*s)⁻¹ • v)-phi x)-(s⁻¹:ℝ) • L v

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledHigherJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def rescaledAmplitudeRatio (amp : _root_.OAI.Yau.Jets.Coord → ℂ) (N s : ℝ) (x v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  amp (x+(N*s)⁻¹ • v)/amp x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_PlacedFirstJetProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {r a : ℝ}
  {Kset : Set _root_.OAI.Yau.Jets.Coord}
  {T : ℝ}
  {m J K k0 : ℕ}

def PlacedEnvelopeData.representativeWaves (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (he : ∀ x ∈ closure d.Ω, S =ᶠ[𝓝 x] d.S) :
    LocalCompactWaveData g w S (closure d.U) m J K k0 :=
  b.withEnvelope S (envelope_germ_open d.S S)
    (fun x hx ↦ he x (subset_closure (d.closure_U_Ω hx))) (fun _ hx ↦ hx)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicUniformPositiveSphereStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
local instance intrinsicUniformPositiveSphereStageLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicUniformPositiveSphereStageLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicUniformPositiveSphereStageLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicUniformPositiveSphereStageLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicUniformPositiveSphereStageLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicUniformPositiveSphereStageLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicUniformPositiveSphereStageLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance intrinsicUniformPositiveSphereStageLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance intrinsicUniformPositiveSphereStageLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicUniformPositiveSphereStageLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicUniformPositiveSphereStageLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance
local instance intrinsicUniformPositiveSphereStageLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicUniformPositiveSphereStageLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicUniformPositiveSphereStageLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance intrinsicUniformPositiveSphereStageLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicUniformPositiveSphereStageLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicGlobalSphereStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
local instance intrinsicGlobalSphereStageLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicGlobalSphereStageLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicGlobalSphereStageLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicGlobalSphereStageLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicGlobalSphereStageLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicGlobalSphereStageLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicGlobalSphereStageLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance intrinsicGlobalSphereStageLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance intrinsicGlobalSphereStageLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicGlobalSphereStageLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance intrinsicGlobalSphereStageLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := inferInstance
local instance intrinsicGlobalSphereStageLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicGlobalSphereStageLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicGlobalSphereStageLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance intrinsicGlobalSphereStageLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicGlobalSphereStageLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereMeasureChartGeometry
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section

lemma sphereChartCoordMap_injective (p : Base) : Function.Injective (sphereChartCoordMap p) := by
  intro x y h
  have h' := congrArg (extChartAt (𝓡 4) p) h
  have hx : seedCoordEquiv x ∈ (extChartAt (𝓡 4) p).target := by rw [centeredSphereChart_target]; trivial
  have hy : seedCoordEquiv y ∈ (extChartAt (𝓡 4) p).target := by rw [centeredSphereChart_target]; trivial
  rw [sphereChartCoordMap,sphereChartCoordMap,(extChartAt (𝓡 4) p).right_inv hx,
    (extChartAt (𝓡 4) p).right_inv hy] at h'
  exact seedCoordEquiv.injective h'

lemma sphereChartTransitionDomain_ae (p q : Base) :
    ∀ᵐ x : Yau.Jets.Coord, x ∈ sphereChartTransitionDomain p q := by
  have hs : (sphereChartTransitionDomain p q)ᶜ = sphereChartCoordMap p ⁻¹' {-q} := by
    simp only [sphereChartTransitionDomain,centeredSphereChart_source,preimage_compl,compl_compl]
  apply (ae_iff).mpr
  change volume ((sphereChartTransitionDomain p q)ᶜ) = 0
  rw [hs]
  exact (Set.subsingleton_singleton.preimage (sphereChartCoordMap_injective p)).measure_zero volume

lemma sphereChartTransition_injOn (p q : Base) :
    InjOn (sphereChartTransition p q) (sphereChartTransitionDomain p q) := by
  intro x hx y hy h
  have he := congrArg (sphereChartTransition q p) h
  simpa only [sphereChartTransition_inverse p q hx,sphereChartTransition_inverse p q hy] using he

lemma sphereChartTransition_image_domain (p q : Base) :
    sphereChartTransition p q '' sphereChartTransitionDomain p q = sphereChartTransitionDomain q p := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact sphereChartTransition_mem p q hx
  · intro y hy
    exact ⟨sphereChartTransition q p y,sphereChartTransition_mem q p hy,
      sphereChartTransition_inverse q p hy⟩

lemma sphereChartTransition_hasFDeriv (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    HasFDerivAt (sphereChartTransition p q) (fderiv ℝ (sphereChartTransition p q) x) x :=
  ((sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.hasFDerivAt

lemma jacobian_det_eq (f : Yau.Jets.Coord → Yau.Jets.Coord) (x : Yau.Jets.Coord) :
    (jacobian f x).det = (fderiv ℝ f x).det := by
  have he : jacobian f x = LinearMap.toMatrix (Pi.basisFun ℝ (Fin 4))
      (Pi.basisFun ℝ (Fin 4)) (fderiv ℝ f x).toLinearMap := by
    ext i j
    simp [jacobian]
  rw [he,LinearMap.det_toMatrix]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartOpenMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Topology
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereChartOpenMapLocal1
lemma sphereChartCoordMap_isOpenMap (p : Base) : IsOpenMap (sphereChartCoordMap p) := by
  intro U hU
  have he : sphereChartCoordMap p '' U =
      (chartAt BaseModel p).symm '' (seedCoordEquiv '' U) := by
    rw [Set.image_image]
    rfl
  rw [he]
  apply (chartAt BaseModel p).symm.isOpen_image_of_subset_source
    (seedCoordEquiv.toHomeomorph.isOpenMap _ hU)
  intro z hz
  change z ∈ (stereographic' 4 (-p)).target
  simp

lemma sphereChartCoordMap_zero (p : Base) : sphereChartCoordMap p 0 = p := by
  unfold sphereChartCoordMap
  rw [map_zero,centeredSphereChart_inverse_zero]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureLocal1
attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureLocal2
def sphereReferenceMeasure : Measure Base :=
  Measure.map seedSphereFromCoord
    (volume.withDensity (fun x ↦ ENNReal.ofReal (roundCoordDensity x)))

lemma seedSphereFromCoord_measurableEmbedding : MeasurableEmbedding seedSphereFromCoord :=
  seedSphereFromCoord_continuous.measurableEmbedding
    (Function.LeftInverse.injective seedSphereToCoord_from)

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
lemma sphereChartCoordMap_measurableEmbedding (p : Base) : MeasurableEmbedding (sphereChartCoordMap p) :=
  (sphereChartCoordMap_smooth p).continuous.measurableEmbedding (sphereChartCoordMap_injective p)

lemma roundChartDensity_coord_eq (p : Base) (x : Yau.Jets.Coord) :
    roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x := by
  simp only [roundCoordDensity,roundChartDensity_conformal]

lemma sphereReferenceMeasure_lintegral_chart_change (p q : Base) (f : Base → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (roundCoordDensity x)*f (sphereChartCoordMap p x)) =
      ∫⁻ x, ENNReal.ofReal (roundCoordDensity x)*f (sphereChartCoordMap q x) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (sphereChartTransitionDomain_open p q).measurableSet
    (fun x hx ↦ (sphereChartTransition_hasFDeriv p q hx).hasFDerivWithinAt)
    (sphereChartTransition_injOn p q)
    (fun y ↦ ENNReal.ofReal (roundCoordDensity y)*f (sphereChartCoordMap q y))
  rw [sphereChartTransition_image_domain] at h
  have hp : volume.restrict (sphereChartTransitionDomain p q) = volume :=
    Measure.restrict_eq_self_of_ae_mem (sphereChartTransitionDomain_ae p q)
  have hq : volume.restrict (sphereChartTransitionDomain q p) = volume :=
    Measure.restrict_eq_self_of_ae_mem (sphereChartTransitionDomain_ae q p)
  rw [hp,hq] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [sphereChartTransitionDomain_ae p q] with x hx
  have hd := sphereChartTransition_round_density p q hx
  simp only [roundChartDensity_coord_eq,jacobian_det_eq] at hd
  rw [sphereChartTransition_point p q hx,hd,ENNReal.ofReal_mul (abs_nonneg _),mul_assoc]

theorem sphereReferenceMeasure_eq_chart (p : Base) :
    sphereReferenceMeasure = Measure.map (sphereChartCoordMap p)
      (volume.withDensity (fun x ↦ ENNReal.ofReal (roundChartDensity p (seedCoordEquiv x)))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  simp only [sphereReferenceMeasure,roundChartDensity_coord_eq]
  rw [seedSphereFromCoord_measurableEmbedding.lintegral_map,
    (sphereChartCoordMap_measurableEmbedding p).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  exact sphereReferenceMeasure_lintegral_chart_change seedPoint p f

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance sphereEnergyBilinearLocal1_r6182f2_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyBilinearLocal2_r6182f2_1 : BorelSpace Base := ⟨rfl⟩
lemma sphereDifferential_add (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    sphereDifferential (u+v) p = sphereDifferential u p+sphereDifferential v p :=
  mfderiv_add (hu.mdifferentiable (by simp) p) (hv.mdifferentiable (by simp) p)

lemma sphereDifferential_smul (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (t : ℝ) (p : Base) :
    sphereDifferential (t • u) p = t • sphereDifferential u p :=
  const_smul_mfderiv (hu.mdifferentiable (by simp) p) t

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasureFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Metric
open scoped ENNReal Topology
noncomputable section

lemma roundCoordDensity_le_one (x : Yau.Jets.Coord) : roundCoordDensity x ≤ 1 := by
  rw [roundCoordDensity,roundChartDensity_conformal]
  have h : 4/(‖seedCoordEquiv x‖^2+4) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (‖seedCoordEquiv x‖)])
  exact pow_le_one₀ (by positivity) h

lemma roundCoordMeasure_le_volume :
    volume.withDensity (fun x ↦ ENNReal.ofReal (roundCoordDensity x)) ≤ volume := by
  calc
    _ ≤ volume.withDensity 1 := withDensity_mono (Filter.Eventually.of_forall (fun x ↦ by
      simpa using ENNReal.ofReal_le_ofReal (roundCoordDensity_le_one x)))
    _ = _ := withDensity_one

attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureFiniteLocal1
attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureFiniteLocal2
lemma sphereReferenceMeasure_chart_ball_finite (p : Base) (r : ℝ) :
    sphereReferenceMeasure (sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) r) < ∞ := by
  rw [sphereReferenceMeasure_eq_chart p]
  simp only [roundChartDensity_coord_eq]
  rw [Measure.map_apply (sphereChartCoordMap_smooth p).continuous.measurable
    ((sphereChartCoordMap_isOpenMap p) _ isOpen_ball).measurableSet,
    Set.preimage_image_eq _ (sphereChartCoordMap_injective p)]
  exact lt_of_le_of_lt (roundCoordMeasure_le_volume _)
    (lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : Yau.Jets.Coord) r).measure_lt_top)

lemma sphereReferenceMeasure_locallyFinite : IsLocallyFiniteMeasure sphereReferenceMeasure := by
  constructor
  intro p
  refine ⟨sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1,?_,sphereReferenceMeasure_chart_ball_finite p 1⟩
  apply ((sphereChartCoordMap_isOpenMap p) _ isOpen_ball).mem_nhds
  exact ⟨0,mem_ball_self (by norm_num),sphereChartCoordMap_zero p⟩

lemma sphereReferenceMeasure_finite : IsFiniteMeasure sphereReferenceMeasure := by
  let := sphereReferenceMeasure_locallyFinite
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma sphereReferenceMeasure_integrable_continuous (f : Base → ℝ) (hf : Continuous f) :
    Integrable f sphereReferenceMeasure := by
  let := sphereReferenceMeasure_finite
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasurePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma roundCoordMeasure_openPos :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (roundCoordDensity x))).IsOpenPosMeasure := by
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure
    (μ := (volume : Measure Yau.Jets.Coord))
  exact withDensity_absolutelyContinuous'
    roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (roundCoordDensity_pos x)).ne'))

attribute [local instance] OAI.Yau.Target.sphereReferenceMeasurePositiveLocal1
attribute [local instance] OAI.Yau.Target.sphereReferenceMeasurePositiveLocal2
lemma sphereReferenceMeasure_openPos : sphereReferenceMeasure.IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨p,hp⟩ := hUne
  rw [sphereReferenceMeasure_eq_chart p]
  simp only [roundChartDensity_coord_eq]
  rw [Measure.map_apply (sphereChartCoordMap_smooth p).continuous.measurable hU.measurableSet]
  let := roundCoordMeasure_openPos
  exact (hU.preimage (sphereChartCoordMap_smooth p).continuous).measure_ne_zero _
    ⟨0,by simpa only [mem_preimage,sphereChartCoordMap_zero] using hp⟩

def sphereWeightedPairing (rho u v : Base → ℝ) : ℝ :=
  ∫ p, rho p*u p*v p ∂sphereReferenceMeasure

lemma sphereWeightedPairing_integrable (rho u v : Base → ℝ)
    (hr : Continuous rho) (hu : Continuous u) (hv : Continuous v) :
    Integrable (fun p ↦ rho p*u p*v p) sphereReferenceMeasure :=
  sphereReferenceMeasure_integrable_continuous _ ((hr.mul hu).mul hv)

lemma sphereWeightedPairing_self_pos (rho u : Base → ℝ)
    (hr : Continuous rho) (hp : ∀ p, 0 < rho p) (hu : Continuous u) (hne : u ≠ 0) :
    0 < sphereWeightedPairing rho u u := by
  let := sphereReferenceMeasure_openPos
  obtain ⟨p,hp'⟩ : ∃ p, u p ≠ 0 := by
    by_contra h
    apply hne
    funext p
    simpa using not_exists.mp h p
  apply integral_pos_of_integrable_nonneg_nonzero ((hr.mul hu).mul hu)
    (sphereWeightedPairing_integrable rho u u hr hu hu)
  · intro q
    change 0 ≤ rho q*u q*u q
    nlinarith [sq_nonneg (u q),hp q]
  · have h : 0 < rho p*u p*u p := by nlinarith [sq_pos_of_ne_zero hp',hp p]
    exact h.ne'

lemma sphereWeightedPairing_symm (rho u v : Base → ℝ) :
    sphereWeightedPairing rho u v = sphereWeightedPairing rho v u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p ↦ by ring)

lemma sphereWeightedPairing_smul_left (rho u v : Base → ℝ) (t : ℝ) :
    sphereWeightedPairing rho (t • u) v = t*sphereWeightedPairing rho u v := by
  unfold sphereWeightedPairing
  have he : (fun p ↦ rho p*(t • u) p*v p) = fun p ↦ t*(rho p*u p*v p) := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul]

lemma sphereWeightedPairing_add_left (rho u v w : Base → ℝ)
    (hr : Continuous rho) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    sphereWeightedPairing rho (u+v) w = sphereWeightedPairing rho u w+sphereWeightedPairing rho v w := by
  unfold sphereWeightedPairing
  simp only [Pi.add_apply,mul_add,add_mul]
  exact integral_add (sphereWeightedPairing_integrable rho u w hr hu hw)
    (sphereWeightedPairing_integrable rho v w hr hv hw)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothFromCharts
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff Topology
noncomputable section

lemma sphere_smooth_of_chart_pullbacks (f : Base → ℝ)
    (hf : ∀ p, ContDiff ℝ ∞ (f ∘ sphereChartCoordMap p)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f := by
  intro x
  have hc := contMDiffAt_extChartAt' (I := 𝓡 4) (n := ∞) (x := x) (x' := x)
    (mem_chart_source BaseModel x)
  have hh := (((hf x).comp seedCoordEquiv.symm.contDiff).contMDiff.contMDiffAt).comp x hc
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓡 4) x).mem_nhds (mem_extChartAt_source (I := 𝓡 4) x)] with y hy
  simp only [Function.comp_apply,sphereChartCoordMap,seedCoordEquiv.apply_symm_apply,
    (extChartAt (𝓡 4) x).left_inv hy]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicEnergyIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsic_differential_pair_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) :=
  sphere_smooth_of_chart_pullbacks _ (intrinsic_differential_pair_pullback_smooth A hA hs hp u v hu hv)

lemma intrinsic_differential_pair_integrable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) :
    Integrable (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) sphereReferenceMeasure :=
  sphereReferenceMeasure_integrable_continuous _
    (intrinsic_differential_pair_smooth A hA hs hp u v hu hv).continuous

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

def sphereDirichletForm (A : IntrinsicTensor) (u v : Base → ℝ) : ℝ :=
  ∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure

lemma sphereDirichletForm_symm (A : IntrinsicTensor)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha) (u v : Base → ℝ) :
    sphereDirichletForm A u v = sphereDirichletForm A v u :=
  integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ hs x _ _))

lemma intrinsic_quadratic_nonneg (A : IntrinsicTensor)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) (x : Base) (alpha : SphereCotangent x) :
    0 ≤ A x alpha alpha := by
  by_cases hz : alpha = 0
  · simp [hz]
  · exact (hp x alpha hz).le

lemma sphereDirichletForm_nonneg (A : IntrinsicTensor)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) (u : Base → ℝ) :
    0 ≤ sphereDirichletForm A u u :=
  integral_nonneg (fun x ↦ intrinsic_quadratic_nonneg A hp x _)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDirichletBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

lemma sphereDirichletForm_add_left (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v w : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    sphereDirichletForm A (u+v) w = sphereDirichletForm A u w+sphereDirichletForm A v w := by
  simp only [sphereDirichletForm,sphereDifferential_add u v hu hv,map_add,_root_.add_apply]
  exact integral_add (intrinsic_differential_pair_integrable A hA hs hp u w hu hw)
    (intrinsic_differential_pair_integrable A hA hs hp v w hv hw)

lemma sphereDirichletForm_smul_left (A : IntrinsicTensor) (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (t : ℝ) :
    sphereDirichletForm A (t • u) v = t*sphereDirichletForm A u v := by
  simp only [sphereDirichletForm,sphereDifferential_smul u hu,map_smul,_root_.smul_apply,smul_eq_mul]
  exact integral_const_mul t _

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

def sphereSmoothFunctions : Submodule ℝ (Base → ℝ) where
  carrier := {u | ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u}
  zero_mem' := contMDiff_const
  add_mem' := fun hu hv ↦ hu.add hv
  smul_mem' := fun t _ hu ↦ (contMDiff_const (c := t)).mul hu

def sphereSobolevForm (A : IntrinsicTensor) (rho u v : Base → ℝ) : ℝ :=
  sphereWeightedPairing rho u v+sphereDirichletForm A u v

theorem sphereSobolevForm_pos (A : IntrinsicTensor)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho u : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x)
    (hu : Continuous u) (hne : u ≠ 0) : 0 < sphereSobolevForm A rho u u :=
  add_pos_of_pos_of_nonneg (sphereWeightedPairing_self_pos rho u hr hrp hu hne)
    (sphereDirichletForm_nonneg A hp u)

@[instance_reducible]
def sphereEnergyInnerCore (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x) :
    InnerProductSpace.Core ℝ sphereSmoothFunctions where
  inner u v := sphereSobolevForm A rho u v
  conj_inner_symm u v := by
    change sphereSobolevForm A rho v u = sphereSobolevForm A rho u v
    simp only [sphereSobolevForm,sphereWeightedPairing_symm rho v u,sphereDirichletForm_symm A hs v u]
  re_inner_nonneg u := by
    change 0 ≤ sphereWeightedPairing rho u u+sphereDirichletForm A u u
    apply add_nonneg _ (sphereDirichletForm_nonneg A hp u)
    apply integral_nonneg
    intro x
    change 0 ≤ rho x*((u : Base → ℝ) x)*((u : Base → ℝ) x)
    simpa only [mul_assoc] using
      mul_nonneg (hrp x).le (mul_self_nonneg ((u : Base → ℝ) x))
  add_left u v w := by
    change sphereSobolevForm A rho ((u : Base → ℝ)+v) w =
      sphereSobolevForm A rho u w+sphereSobolevForm A rho v w
    rw [sphereSobolevForm,sphereWeightedPairing_add_left rho u v w hr
      u.property.continuous v.property.continuous w.property.continuous,
      sphereDirichletForm_add_left A hA hs hp u v w u.property v.property w.property]
    simp only [sphereSobolevForm]
    ring
  smul_left u v t := by
    change sphereSobolevForm A rho (t • (u : Base → ℝ)) v = t*sphereSobolevForm A rho u v
    rw [sphereSobolevForm,sphereWeightedPairing_smul_left,sphereDirichletForm_smul_left A u v u.property]
    simp only [sphereSobolevForm,mul_add]
  definite u hu := by
    by_contra hne
    have hn : (u : Base → ℝ) ≠ 0 := fun h ↦ hne (Subtype.ext h)
    exact (ne_of_gt (sphereSobolevForm_pos A hp rho u hr hrp u.property.continuous hn)) hu

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

structure SphereEnergyData where
  tensor : IntrinsicTensor
  smooth : IntrinsicTensorSmooth tensor
  symm : ∀ x alpha beta, tensor x alpha beta = tensor x beta alpha
  pos : ∀ x alpha, alpha ≠ 0 → 0 < tensor x alpha alpha
  density : Base → ℝ
  continuous : Continuous density
  positive : ∀ x, 0 < density x

def SphereEnergySmooth (_d : SphereEnergyData) : Type := sphereSmoothFunctions

namespace SphereEnergySmooth
variable (d : SphereEnergyData)
instance instAddCommGroup : AddCommGroup (SphereEnergySmooth d) := inferInstanceAs (AddCommGroup sphereSmoothFunctions)
instance instModule : Module ℝ (SphereEnergySmooth d) := inferInstanceAs (Module ℝ sphereSmoothFunctions)
instance instInnerCore : InnerProductSpace.Core ℝ (SphereEnergySmooth d) :=
  sphereEnergyInnerCore d.tensor d.smooth d.symm d.pos d.density d.continuous d.positive
instance instNormedAddCommGroup : NormedAddCommGroup (SphereEnergySmooth d) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance instInnerProductSpace : InnerProductSpace ℝ (SphereEnergySmooth d) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (SphereEnergySmooth d))

def toSmooth (u : SphereEnergySmooth d) : sphereSmoothFunctions := u

end SphereEnergySmooth

abbrev SphereEnergyHilbert (d : SphereEnergyData) := UniformSpace.Completion (SphereEnergySmooth d)

end
end Yau.Target

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

def sphereAtlasCore : Set BaseModel := seedCoordEquiv '' closedBall (0 : Yau.Jets.Coord) 1

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixEnergy
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def realCoordGradient (w : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : Yau.Jets.Coord := fun i ↦ Yau.coordPartial w x i

def realMatrixEnergy (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  coordMatrixForm (B x) (realCoordGradient u x) (realCoordGradient v x)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedElliptic
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section

def realMatrixFlux (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  ∑ j, B x i j*Yau.coordPartial w x j

def realWeightedElliptic (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) : Yau.Jets.Coord → ℝ := Yau.weightedDiv gamma (realMatrixFlux B w)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealEllipticLocalityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Filter
open scoped Topology ContDiff

def realEllipticResidual (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ)
    (x : Yau.Jets.Coord) : ℝ := realWeightedElliptic gamma B f x+potential x*f x

open Matrix MeasureTheory
open scoped ContDiff

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDifferentiatedEquation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

def realDerivativeErrorFlux (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (k : Fin 4) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  ∑ j, Yau.coordPartial (fun y ↦ C y i j) x k*Yau.coordPartial W x j

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixTransport
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

def realTransportDeformation (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    (2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i*Yau.coordPartial v x k*Yau.coordPartial v x j -
      V x k*Yau.coordPartial (fun y ↦ B y i j) x k*Yau.coordPartial v x i*Yau.coordPartial v x j)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTransportQuadratic
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

def realTransportQuadratic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (x xi : Yau.Jets.Coord) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    (2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i*xi k*xi j -
      V x k*Yau.coordPartial (fun y ↦ B y i j) x k*xi i*xi j)

def realGradientSquare (v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  ∑ i, (Yau.coordPartial v x i)^2

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCutoffIntegralsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open MeasureTheory
open scoped ContDiff

def realCutoffWeight (eta : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  eta x^2+realGradientSquare eta x

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetErrorEquation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

def realJetErrorFlux (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) : List (Fin 4) → Yau.Jets.Coord → Yau.Jets.Coord
  | [] => fun _ _ ↦ 0
  | l::ds => fun x i ↦ Yau.coordPartial (fun y ↦ realJetErrorFlux C W ds y i) x l -
      realDerivativeErrorFlux C (partialJet W ds) l x i

def realJetErrorSource (V W : Yau.Jets.Coord → ℝ) : List (Fin 4) → Yau.Jets.Coord → ℝ
  | [] => fun _ ↦ 0
  | l::ds => fun x ↦ Yau.coordPartial (realJetErrorSource V W ds) x l -
      Yau.coordPartial V x l*partialJet W ds x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteJetSquare
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

def realFiniteJetSquare (W : Yau.Jets.Coord → ℝ) (n : ℕ) (x : Yau.Jets.Coord) : ℝ :=
  ∑ r ∈ Finset.range (n+1), ∑ w : Fin r → Fin 4, (partialJet W (List.ofFn w) x)^2

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetProductExpansion
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

def realJetProductSum (a b : Yau.Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4))) (x : Yau.Jets.Coord) : ℝ :=
  (ts.map (fun t ↦ partialJet a t.1 x * partialJet b t.2 x)).sum

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealBallCutoffChain
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Metric
open scoped ContDiff
noncomputable section

def realBallCutoff (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (n : ℕ) : ContDiffBump y :=
  ⟨realCutoffRadius r R (n+1),realCutoffRadius r R n,
    hr.trans (realCutoffRadius_gt r R hR _),realCutoffRadius_succ_lt r R hR n⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanLocalConditions
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def realTransportBilinear (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (x : Yau.Jets.Coord) :
    Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ :=
  ∑ i, ∑ j, ∑ k,
    ((2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i) •
      ((ContinuousLinearMap.proj k).smulRight (ContinuousLinearMap.proj j)) -
    (V x k*Yau.coordPartial (fun y ↦ B y i j) x k) •
      ((ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealConvexifiedPhase
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

def realConvexifiedPhase (psi : Yau.Jets.Coord → ℝ) (K : ℝ) (x : Yau.Jets.Coord) : ℝ :=
  psi x+K*(psi x)^2

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealConvexifiedQuadraticLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Matrix
open scoped ContDiff

open Metric

def realCoordinateSquare (x0 x : Yau.Jets.Coord) : ℝ := ∑ i, (x i-x0 i)^2

def realIndentedPhase (psi : Yau.Jets.Coord → ℝ) (x0 : Yau.Jets.Coord)
    (x : Yau.Jets.Coord) : ℝ := psi x-realCoordinateSquare x0 x

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeL2Control
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

def realCubeL2Control (W : Yau.Jets.Coord → ℝ) :
    List (Fin 4) → List (Fin 4) → Yau.Jets.Coord → ℝ
  | [], ds, x => (partialJet W ds x)^2
  | i::is, ds, x => 2*∫ t in Icc (-1:ℝ) 1,
    (realCubeL2Control W is ds (update x i t)+realCubeL2Control W is (i::ds) (update x i t))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeAverage
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

def realCubeAverage (F : Yau.Jets.Coord → ℝ) : List (Fin 4) → Yau.Jets.Coord → ℝ
  | [], x => F x
  | i::is, x => ∫ t in Icc (-1:ℝ) 1, realCubeAverage F is (update x i t)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCoordinateDual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

def realCoordinateDual : Yau.Jets.Coord →L[ℝ] (Yau.Jets.Coord →L[ℝ] ℝ) :=
  ∑ i : Fin 4, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeCellPartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set Function Metric
noncomputable section

def realCubeCell (n : ℕ) (k : Fin 4 → Fin n) : Set Yau.Jets.Coord :=
  realScaledCube 4 (corrugationCubeCenter (fun _ ↦ -1) 2 n k) (1/(n:ℝ))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeCellApproximation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set Function
open scoped ContDiff
noncomputable section

def realCubeCellMean (W : Yau.Jets.Coord → ℝ) (n : ℕ) (k : Fin 4 → Fin n) : ℝ :=
  (∫ x in realCubeCell n k, W x)/(2/(n:ℝ))^4

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenGlobalRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Filter Yau.Geometry
open scoped ContDiff Topology
noncomputable section
local instance sphereGlobalRepresentativeMeasurable : MeasurableSpace Base := borel Base
local instance sphereGlobalRepresentativeBorel : BorelSpace Base := ⟨rfl⟩

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

structure SphereComparisonPair (r delta : ℝ) where
  energy : SphereEnergyData
  density_smooth : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ energy.density
  comparison : ∀ y ∈ closedBall (0 : BaseModel) r,
    dist ((intrinsicChartCoefficient energy.tensor energy.density seedPoint y,
      fderiv ℝ (intrinsicChartCoefficient energy.tensor energy.density seedPoint) y) : CoefficientFirstJet BaseModel)
      (roundCoefficientJet y) < delta
  support : Set Base
  support_compact : IsCompact support
  support_patch : support ⊆ seedSpherePatch r
  exterior_tensor : ∀ x ∉ support, ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
    energy.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫
  exterior_density : ∀ x ∉ support, energy.density x=1

end
end Yau.Target

end OAI
end


