-- Prove2me | Definitions.Def_OAIQ249SI005
-- name    : OAIQ249SI005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:04:06.45398+00:00
-- url     : https://prove2.me/theorems/fc600af2-6074-4243-82e7-e48834f7454d
-- title:
--   Definitions bundle OAIQ249SI005 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 265 declarations of OpenAI's Lean: 207 definitions and 58 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.axisDirectionJet`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeGroup`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.centeredEqualHomotopy`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.centeredEqualNormal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.centeredOppositeNormal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartPushforward`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartedAtlasFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartedAtlasFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cleanSurfacePairs`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactProjectionDirections`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.conjugateFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDifferential`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coupledModelNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coupledModelSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscapParameterLinear`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscapSourceEquiv`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscapSourceLinear`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscapTargetShear`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.curveNormalLinear`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberGroup`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.diagonalDefectModel`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionBlock`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.euclideanPad`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.explicitAtlasMeanFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.explicitAtlasMeanFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.filledDoubleRotation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.filledShiftedRotation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataDualNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataDualSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteMeanModelNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteMeanModelSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.firstColumnLength` and 167 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_PositiveBasis`, `Immersion_ClosedSurface_QuadraticMean`, `SurfaceImmersion_Atlas_AtlasTensorDerivatives`, `SurfaceImmersion_Atlas_ChartPushforward`, `SurfaceImmersion_Atlas_CompactCurvePhaseParameters`, `SurfaceImmersion_Atlas_CurvePhaseParameterGraph`, `SurfaceImmersion_Atlas_IndependentPhaseProjections`, `SurfaceImmersion_Atlas_LowJetCoordinateChange`, `SurfaceImmersion_Atlas_NonparallelPhaseCovectors`, `SurfaceImmersion_Atlas_NormalDefectCoordinates`, `SurfaceImmersion_Atlas_PairCurveChartDerivative`, `SurfaceImmersion_Atlas_PlaneCommonCoordinate`, `SurfaceImmersion_Atlas_PlaneCurveCoordinates`, `SurfaceImmersion_Atlas_ShrinkingJetCutoff`, `SurfaceImmersion_Atlas_SurfaceChartRepresentative`, `SurfaceImmersion_Atlas_TensorCoordinatePullbackBounds`, `SurfaceImmersion_Atlas_TensorReadReconstruction`, `SurfaceImmersion_Atlas_TimeCoordinateBlend`, `SurfaceImmersion_Atlas_TriangularTimeCoordinates`, `SurfaceImmersion_Correction_CenteredPairModels`, `SurfaceImmersion_Correction_ChartedAtlasMeanIdentity`, `SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual`, `SurfaceImmersion_Correction_ConjugatedPolynomialOperator`, `SurfaceImmersion_Correction_CoordinatePolynomialPullback`, `SurfaceImmersion_Correction_CoupledSmoothing`, `SurfaceImmersion_Correction_DiagonalDefectModel`, `SurfaceImmersion_Correction_FinitePolynomialPhases`, `SurfaceImmersion_Correction_JetPolynomialAlgebra`, `SurfaceImmersion_Correction_JetPolynomialDerivative`, `SurfaceImmersion_Correction_JetPolynomialFullCorrector`, `SurfaceImmersion_Correction_LocalFullPeriodicCorrector`, `SurfaceImmersion_Correction_NormalizedLinearModel`, `SurfaceImmersion_Correction_PairModelCoordinates`, `SurfaceImmersion_Correction_PeriodicCorrectorFormula`, `SurfaceImmersion_Correction_PolynomialAtlasMean`, `SurfaceImmersion_Correction_PolynomialCoefficientExtension`, `SurfaceImmersion_Correction_PolynomialFiniteAtlasMean`, `SurfaceImmersion_Correction_PolynomialFiniteAtlasTrial`, `SurfaceImmersion_Correction_PolynomialMeanIteration`, `SurfaceImmersion_Correction_PolynomialPerturbationCalculus`, `SurfaceImmersion_Correction_PolynomialProfileTransfer`, `SurfaceImmersion_Correction_PolynomialRotationFrame`, `SurfaceImmersion_Correction_PolynomialSmoothingProfiles`, `SurfaceImmersion_Correction_PolynomialSolveFactors`, `SurfaceImmersion_Correction_PolynomialTensorMean`, `SurfaceImmersion_Correction_PolynomialTensorReadBudget`, `SurfaceImmersion_Correction_PolynomialVariationScaling`, `SurfaceImmersion_Correction_PrimitiveInitialMean`, `SurfaceImmersion_Correction_ProfiledAtlasAdjustedMean`, `SurfaceImmersion_Correction_SmoothPeriodicCorrector`, `SurfaceImmersion_Correction_SmoothedInputCloseness`, `SurfaceImmersion_Correction_SpecialPointCorrection`, `SurfaceImmersion_Correction_TensorAtlasMeanExplicit`, `SurfaceImmersion_Correction_TensorFiniteMean`, `SurfaceImmersion_Correction_TensorSmoothingSymmetry`, `SurfaceImmersion_Correction_UniformAtlasMean`, `SurfaceImmersion_Correction_WeightedPolynomialBounds`, `SurfaceImmersion_Geometry_AxisDirectionJet`, `SurfaceImmersion_Geometry_C1ImmersionJets`, `SurfaceImmersion_Geometry_CompactNormalTriple`, `SurfaceImmersion_Geometry_ComplexJetDecomposition`, `SurfaceImmersion_Geometry_CurveNormalFrame`, `SurfaceImmersion_Geometry_GenericProjectionParameter`, `SurfaceImmersion_Geometry_JetPullbackExpressions`, `SurfaceImmersion_Geometry_LocalQuadraticReplacement`, `SurfaceImmersion_Geometry_ManifoldMetricCalculus`, `SurfaceImmersion_Geometry_MixedJetDerivatives`, `SurfaceImmersion_Geometry_NormalDefectDomain`, `SurfaceImmersion_Geometry_NormalFrameJet`, `SurfaceImmersion_Geometry_NormalFrameTransport`, `SurfaceImmersion_Geometry_NormalizeFrameColumn`, `SurfaceImmersion_Geometry_ParameterTaylorRemainder`, `SurfaceImmersion_Geometry_PlaneCurveFrame`, `SurfaceImmersion_Geometry_PlaneDefectInterpolation`, `SurfaceImmersion_Geometry_PositiveDensityInverse`, `SurfaceImmersion_Geometry_QuantitativeMetricExpansion`, `SurfaceImmersion_Geometry_RegularProjectionParameter`, `SurfaceImmersion_Geometry_RoundedReturnCurve`, `SurfaceImmersion_Geometry_SafeNormalizationStability`, `SurfaceImmersion_Geometry_ScalarFlatHolder`, `SurfaceImmersion_Geometry_ScalarFlatTaylor`, `SurfaceImmersion_Geometry_ScalarJetTransport`, `SurfaceImmersion_Geometry_ScaledGraphJoin`, `SurfaceImmersion_Geometry_SingleTensorRestoreBound`, `SurfaceImmersion_Geometry_SmallGraphBlends`, `SurfaceImmersion_Geometry_SurfaceDirectionJet`, `SurfaceImmersion_Geometry_SurfaceGermTranslation`, `SurfaceImmersion_Geometry_SurfaceRegularPairLocus`, `SurfaceImmersion_Geometry_TensorBundleInverse`, `SurfaceImmersion_Geometry_TensorExpressionLinearMap`, `SurfaceImmersion_Geometry_TensorFrameAlgebra`, `SurfaceImmersion_Geometry_TransverseJetConvexity`, `SurfaceImmersion_Geometry_UnorderedLinePair`, `SurfaceImmersion_Primitive_BoundedPrimitiveAmplitude`, `SurfaceImmersion_Primitive_CircularBoundaryParam`, `SurfaceImmersion_Primitive_FinitePrimitiveOperatorTolerance`, `SurfaceImmersion_Primitive_InteriorVelocityPath`, `SurfaceImmersion_Primitive_LeadingProfileMap`, `SurfaceImmersion_Primitive_LocalPeriodicPrimitive`, `SurfaceImmersion_Primitive_LoopDensityLinear`, `SurfaceImmersion_Primitive_LoopDensityTriangle`, `SurfaceImmersion_Primitive_PrimitiveDataC1`, `SurfaceImmersion_Primitive_PrimitiveOperatorConjugation`, `SurfaceImmersion_Primitive_PrimitiveOperatorMask`, `SurfaceImmersion_Primitive_PrimitiveOperatorStability`, `SurfaceImmersion_Primitive_VelocityFrame`, `SurfaceImmersion_Primitive_VelocityNormalGeometry`, `SurfaceImmersion_Primitive_VelocitySpatialDerivative`, `SurfaceImmersion_Whitney_CleanSurfacePairs`, `SurfaceImmersion_Whitney_CrosscapKernelLine`, `SurfaceImmersion_Whitney_CrosscapLinearCoordinates`, `SurfaceImmersion_Whitney_DoubleLocusAugmentation`, `SurfaceImmersion_Whitney_DoubleLocusChart`, `SurfaceImmersion_Whitney_DoubleRotationFilling`, `SurfaceImmersion_Whitney_EuclideanImmersionReduction`, `SurfaceImmersion_Whitney_LoopDensityArcTriangle`, `SurfaceImmersion_Whitney_ProjectionCrosscapJet`, `SurfaceImmersion_Whitney_QuadraticCrosscapFactorization`, `SurfaceImmersion_Whitney_QuadraticCrosscapNormalForm`, `SurfaceImmersion_Whitney_ShiftedRotationFilling`, `SurfaceImmersion_Whitney_ShiftedRotationFrame`, `SurfaceImmersion_Whitney_StandardCrosscapDerivative`, `SurfaceImmersion_Whitney_SurfacePairDerivative`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI001` and `OAIQ249SI002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI008` and `OAIQ249SI009`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_circularPhase_frame_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_diagonal_mem_closure`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_crosscap_coordinate_strip`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_corner_bridges`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_surface_pair_clean_relative`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_normalized_pair_frame_filling`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_crosscap_ordered_arc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_signed_diagonal_filling`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_simple_prepared_crosscap_ordered_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_crosscap_connecting_arc_endpoint_regular`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_crosscap_source_geometry`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_normalizedPolynomialMean_bounds` and `OAI.ClosedSurfaceR4.PhaseGeometry.polynomial_profiled_split_cancellation`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SurfacePairTranslationPatch.regularize_avoiding_points`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_surface_pair_clean_relative` and `OAI_ClosedSurfaceR4_RealModes_contDiffOn_realLinearizedTensor`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI001
import Definitions.Def_OAIQ249SI002

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

def doublePair {n : ℕ} (θ : ℝ) (A B : CVec n) : ℝ :=
  (phase (2 * θ) * (A ⬝ᵥ B)).re / 2

def quadraticMetric {n : ℕ} (U : Base → RVec n) (v w p : Base) : ℝ :=
  fderiv ℝ U p v ⬝ᵥ fderiv ℝ U p w


def leadingAmplitude {n : ℕ} (δ b ξ : ℝ) (N : RVec n) : CVec n :=
  fun j => I * ((Real.sqrt 2 * δ * b * ξ * N j : ℝ) : ℂ)

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PositiveBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean
open Set


def basisCoefficient (t u v : ℝ) : PhaseMean.Tensor →L[ℝ] ℝ :=
  (((t - u) * (t - v))⁻¹) •
    ((ContinuousLinearMap.proj 2 : PhaseMean.Tensor →L[ℝ] ℝ) -
      (u + v) • ContinuousLinearMap.proj 1 + (u * v) • ContinuousLinearMap.proj 0)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_WeightedPolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for the finite higher-jet monomials in paper 094-01.
The loss exponent adds under products and is unchanged when the output
order increases; only the multiplicative constant depends on that order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weightedBound_const (U : Set A) (s : ℝ) (m : ℕ) (c : E) :
    WeightedBound U s m ‖c‖ (fun _ => c) := by
  intro j _ x _
  by_cases hj : j = 0
  · subst j
    simp only [pow_zero, one_mul, norm_iteratedFDerivWithin_zero]
    exact le_rfl
  · rw [iteratedFDerivWithin_const_of_ne hj]
    simp [norm_nonneg c]

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothingSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor coordinate maps commute with transposition. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

local instance symmetryModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance symmetryModelSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation in a real parameter commutes with the actual finite
atlas restoration and chart reading. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base planeCoordinateIsometry)
open PhaseMean
local instance tensorDerivativeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorDerivativeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance tensorDerivativeDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance tensorDerivativeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance tensorDerivativeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorDerivativeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

omit [CompactSpace M] in
lemma chart_mdifferentiable (p : M) : (chart p).MDifferentiable planeModel 𝓘(ℝ,Base) :=
  ⟨(chart_smooth p).mdifferentiableOn (by simp),
    (chart_symm_smooth p).mdifferentiableOn (by simp)⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartPushforward
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero of a compactly supported coordinate correction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V]

def chartPushforward (p : M) (δ : Base → V) : M → V :=
  (chart p).source.indicator (δ ∘ chart p)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CurvePhaseParameterGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A chart of the critical-point equation for an affine perturbation of
a quadratic phase along a regular plane curve. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry

def curvePhaseVelocity (u v : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) : ℝ :=
  (ell.1+L*(u t).1)*(v t).1+(ell.2+L*(u t).2)*(v t).2

def curvePhaseAcceleration (u v w : ℝ → CurvePlane) (L t : ℝ) (ell : CurvePlane) : ℝ :=
  L*((v t).1^2+(v t).2^2)+(ell.1+L*(u t).1)*(w t).1+
    (ell.2+L*(u t).2)*(w t).2

def curvePhaseParameterGraph (u v : ℝ → CurvePlane) (L : ℝ)
    (x : CurvePlane) : CurvePlane :=
  ((-x.2*(v x.1).2-L*((u x.1).1*(v x.1).1+(u x.1).2*(v x.1).2))/(v x.1).1,x.2)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactCurvePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On compact regular arcs the nondegenerate phase parameters form an
open dense set, suitable for independent choices in a finite product. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry

local instance compactCurveVolumeHaar_ra07c31_1 : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
def goodCompactCurvePhases (u v w : ℝ → CurvePlane) (L : ℝ) (K : Set ℝ) : Set CurvePlane :=
  {ell | ∀ t ∈ K, curvePhaseVelocity u v L t ell = 0 →
    curvePhaseAcceleration u v w L t ell ≠ 0}

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonparallelPhaseCovectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two independently perturbed phase covectors can avoid parallelism in
every open parameter set. Only the two-dimensional determinant is used. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry

local instance nonparallelVolumeHaar_ra07c31_1 : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
def covectorDetMap (v : CurvePlane) : CurvePlane →L[ℝ] ℝ :=
  v.1 • ContinuousLinearMap.snd ℝ ℝ ℝ-v.2 • ContinuousLinearMap.fst ℝ ℝ ℝ

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_IndependentPhaseProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent linear phase parameters give open surjective projections.
This transfers the elementary nonparallel-covector condition to any finite
family of independently perturbed phases. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phasePairProjection (i j : ι) : (ι → CurvePlane) →L[ℝ] (CurvePlane × CurvePlane) :=
  (ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LowJetCoordinateChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact order-two jet transport under a fixed smooth coordinate map.
The new position is supplied separately, so no inverse coordinate map is
required and the construction applies to arbitrary smooth maps. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology

namespace ClosedSurfaceR4.JetPolynomial

/-- One fixed coordinate derivative of a scalar function. -/
def coordinatePartial (f : Base → ℝ) (v : Fin 2) : Base → ℝ :=
  fun x => fderiv ℝ f x (coordinateVector v)

/-- First derivative of the composed map, linear in the supplied jet. -/
def coordinateChangeFirst (T : Base → Base) (x : Base) (J : LowJet)
    (v : Fin 2) (a : Fin 4) : ℝ :=
  ∑ i : Fin 2, coordinatePartial (fun y => T y i) v x * J (.inr (firstJetSlot i,a))

/-- Ordered second derivative, with both the Hessian and acceleration terms. -/
def coordinateChangeSecond (T : Base → Base) (x : Base) (J : LowJet)
    (v w : Fin 2) (a : Fin 4) : ℝ :=
  ∑ i : Fin 2,
    (coordinatePartial (fun y => T y i) w x *
      (∑ j : Fin 2, coordinatePartial (fun y => T y j) v x * J (.inr (secondJetSlot j i,a))) +
    coordinatePartial (coordinatePartial (fun y => T y i) w) v x * J (.inr (firstJetSlot i,a)))

/-- Transport a positional low jet at `T x` to the positional low jet at `x`.
The old positional components are unnecessary; the value and ordered jets
are evaluated by the chain rule. -/
def lowJetCoordinateChange (T : Base → Base) (p : Base × LowJet) : LowJet
  | .inl i => p.1 i
  | .inr (w,a) => ![p.2 (.inr (0,a)),
      coordinateChangeFirst T p.1 p.2 0 a,
      coordinateChangeFirst T p.1 p.2 1 a,
      coordinateChangeSecond T p.1 p.2 0 0 a,
      coordinateChangeSecond T p.1 p.2 0 1 a,
      coordinateChangeSecond T p.1 p.2 1 0 a,
      coordinateChangeSecond T p.1 p.2 1 1 a] w

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GenericProjectionParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common graph direction avoids every tangent plane in a finite family
of smooth surface-coordinate derivatives when the projection target has
dimension at least four. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

def tangentSlope (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ)
    (b : Bool) (z : Base × ℝ) : ProjectionTarget n :=
  ((H z.1 (tangentRay b z.2)).2)⁻¹ • (H z.1 (tangentRay b z.2)).1

def tangentSlopeDomain (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ)
    (b : Bool) : Set (Base × ℝ) :=
  {z | (H z.1 (tangentRay b z.2)).2 ≠ 0}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularProjectionParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular graph-projection parameters in dimension three. Unlike the
higher-dimensional avoidance result, this gives finite exceptional
directions on compact coordinate sets. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def compactProjectionDirections (a : ProjectionTarget 3)
    (H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ) (K : Set Base) (b : Bool) :
    Set (Base × ℝ) :=
  (K ×ˢ Icc (-1 : ℝ) 1) ∩ {z | graphProjection a (H z.1 (tangentRay b z.2)) = 0}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EuclideanImmersionReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension reduction of the ordinary Whitney embedding to a smooth
immersion of a compact surface in four-dimensional Euclidean space. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def euclideanPad (n m : ℕ) : ProjectionTarget n →L[ℝ] ProjectionTarget m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin m =>
      if hi : i.val < n then
        (ContinuousLinearMap.proj (⟨i.val,hi⟩ : Fin n)).comp
          (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
      else 0)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ProjectionCrosscapJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nondegenerate second-jet condition at a singularity of a regular
three-dimensional projection. This concerns the original unweighted
coordinate representative, not merely the weighted atlas derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def projectedCrosscapJet (Φ : Base → ProjectionTarget 3 × ℝ)
    (a : ProjectionTarget 3) (b : Bool) (x : Base) (t : ℝ) :
    Base × ℝ →L[ℝ] ProjectionTarget 3 :=
  (graphProjection a).comp (directionJetLinearization (fderiv ℝ Φ) b (x,t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceDirectionJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-direction map of an actual three-dimensional surface,
and its relation to the unweighted projection jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def surfaceDirectionLinearization (f : Base → ProjectionTarget 3) (b : Bool)
    (z : Base × ℝ) : Base × ℝ →L[ℝ] ProjectionTarget 3 :=
  (fderiv ℝ f z.1).comp ((ContinuousLinearMap.snd ℝ Base ℝ).smulRight (tangentRayVelocity b)) +
    ((fderiv ℝ (fderiv ℝ f) z.1).comp (ContinuousLinearMap.fst ℝ Base ℝ)).flip
      (tangentRay b z.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingJetCutoff
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoffs rescaled into smaller coordinate balls, with derivative
bounds measured at their actual radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def flatJetCutoff : ContDiffBump (0 : Base) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def shrinkingJetCutoff (r : ℝ) (x : Base) : ℝ := flatJetCutoff (r⁻¹ • x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalQuadraticReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth surface map can be made equal to its actual quadratic jet
near the origin by an arbitrarily small supported C2 change. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance firstJetNormed : NormedAddCommGroup (Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance firstJetSpace : NormedSpace ℝ (Base →L[ℝ] ProjectionTarget 3) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceGermTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth supported translation families and their unchanged first jets
at points where the scalar separator is locally constant. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfaceTranslation (f : M → ProjectionTarget 3) (χ : M → ℝ)
    (a : ProjectionTarget 3) : M → ProjectionTarget 3 := fun p => f p + χ p • a

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfacePairDerivative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic double-point transversality and its actual coordinate
representatives. The derivative is defined on the two tangent planes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfacePairDerivative (f : M → ProjectionTarget 3) (x y : M) :
    (TangentSpace planeModel x × TangentSpace planeModel y) →L[ℝ] ProjectionTarget 3 :=
  (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x).comp (ContinuousLinearMap.fst ℝ _ _) -
    (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f y).comp (ContinuousLinearMap.snd ℝ _ _)

lemma chart_germ_mfderiv (p : M) {x : M} (hx : x ∈ (chart p).source)
    {f : M → ProjectionTarget 3} {F : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (he : f =ᶠ[𝓝 x] F ∘ chart p) :
    (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x :
      TangentSpace planeModel x →L[ℝ] ProjectionTarget 3) =
      (fderiv ℝ F (chart p x)).comp (mfderiv planeModel 𝓘(ℝ,Base) (chart p) x) := by
  have hFc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,ProjectionTarget 3) ∞ F := hF.contMDiff
  apply ContinuousLinearMap.ext
  intro v
  rw [he.mfderiv_eq,mfderiv_comp x (hFc.mdifferentiable (by simp)).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt hx),mfderiv_eq_fderiv]
  rfl

theorem surface_pair_coordinate_regular_iff (p q : M) {x y : M}
    (hx : x ∈ (chart p).source) (hy : y ∈ (chart q).source)
    {f : M → ProjectionTarget 3} {F G : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (heF : f =ᶠ[𝓝 x] F ∘ chart p) (heG : f =ᶠ[𝓝 y] G ∘ chart q) :
    Function.Surjective (surfacePairDerivative f x y) ↔
      Function.Surjective (fderiv ℝ (fun z : Base × Base => F z.1-G z.2)
        (chart p x,chart q y)) := by
  let C₁ : TangentSpace planeModel x →L[ℝ] Base := mfderiv planeModel 𝓘(ℝ,Base) (chart p) x
  let C₂ : TangentSpace planeModel y →L[ℝ] Base := mfderiv planeModel 𝓘(ℝ,Base) (chart q) y
  let C : (TangentSpace planeModel x × TangentSpace planeModel y) →L[ℝ] (Base × Base) := C₁.prodMap C₂
  have hC : Function.Surjective C := by
    rintro ⟨a,b⟩
    obtain ⟨v,hv⟩ := (chart_mdifferentiable p).mfderiv_surjective hx a
    obtain ⟨w,hw⟩ := (chart_mdifferentiable q).mfderiv_surjective hy b
    exact ⟨(v,w),Prod.ext hv hw⟩
  have hd := (((hF.differentiable (by simp) (chart p x)).hasFDerivAt.comp
      (chart p x,chart q y) ((ContinuousLinearMap.fst ℝ Base Base).hasFDerivAt)).sub
    ((hG.differentiable (by simp) (chart q y)).hasFDerivAt.comp
      (chart p x,chart q y) ((ContinuousLinearMap.snd ℝ Base Base).hasFDerivAt))).fderiv
  change fderiv ℝ (fun z : Base × Base => F z.1-G z.2) (chart p x,chart q y) = _ at hd
  have he : surfacePairDerivative f x y =
      (fderiv ℝ (fun z : Base × Base => F z.1-G z.2) (chart p x,chart q y)).comp C := by
    rw [hd]
    apply ContinuousLinearMap.ext
    intro v
    simp only [surfacePairDerivative,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    rw [chart_germ_mfderiv p hx hF heF,chart_germ_mfderiv q hy hG heG]
    rfl
  rw [he]
  constructor
  · intro h z
    obtain ⟨v,hv⟩ := h z
    exact ⟨C v,hv⟩
  · exact fun h => h.comp hC

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceChartRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every smooth surface map has a globally smooth Euclidean
representative on an actual smaller neighborhood of any chosen point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_chart_representative {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) (p : M) :
    ∃ (U : Set M) (F : Base → ProjectionTarget 3), IsOpen U ∧ p ∈ U ∧
      U ⊆ (chart p).source ∧ ContDiff ℝ ∞ F ∧ EqOn f (F ∘ chart p) U := by
  have hp : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨W,hW,hpW,hWT,F,hF,hFF⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := chart p p)) (chart p).open_target
    (singleton_subset_iff.mpr ((chart p).map_source hp)) hlocal
  let U := (chart p).source ∩ (chart p) ⁻¹' W
  refine ⟨U,F,(chart p).isOpen_inter_preimage hW,⟨hp,hpW (mem_singleton _)⟩,
    inter_subset_left,hF,?_⟩
  intro x hx
  change f x = F (chart p x)
  rw [hFF hx.2]
  change f x = f ((chart p).symm (chart p x))
  rw [(chart p).left_inv hx.1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapKernelLine
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinates for the kernel line of a regular crosscap. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def tangentRayCoefficient (b : Bool) (x : Base) : ℝ := if b then x 1 else x 0

def tangentTransverseCoefficient (b : Bool) (t : ℝ) (x : Base) : ℝ :=
  if b then x 0-t*x 1 else x 1-t*x 0

lemma tangentRay_decomposition (b : Bool) (t : ℝ) (x : Base) :
    x = tangentTransverseCoefficient b t x • tangentRayVelocity b +
      tangentRayCoefficient b x • tangentRay b t := by
  cases b <;> ext i <;> fin_cases i <;>
    simp [tangentTransverseCoefficient,tangentRayCoefficient,tangentRayVelocity,tangentRay] <;> ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleLocusAugmentation
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A three-dimensional submersion on the four-dimensional pair chart
admits one additional linear coordinate with invertible derivative. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem double_locus_linear_augmentation (K : (Base × Base) →L[ℝ] ProjectionTarget 3)
    (hK : Function.Surjective K) :
    ∃ ℓ : (Base × Base) →L[ℝ] ℝ, Function.Bijective (K.prod ℓ) := by
  have hdim : Module.finrank ℝ K.ker = 1 := by
    have h := K.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hK,finrank_top] at h
    have hE : Module.finrank ℝ (Base × Base) = 4 := by simp [Base]
    have hF : Module.finrank ℝ (ProjectionTarget 3) = 3 := by simp [ProjectionTarget]
    rw [hE,hF] at h
    omega
  let e : K.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨P,hP⟩ := K.ker.exists_isCompl
  let π : (Base × Base) →L[ℝ] K.ker := (K.ker.projectionOnto P hP).toContinuousLinearMap
  let ℓ : (Base × Base) →L[ℝ] ℝ := e.toContinuousLinearMap.comp π
  have hzero (x : Base × Base) (hx : K x = 0) (hℓ : ℓ x = 0) : x = 0 := by
    have hmem : x ∈ K.ker := hx
    have hπ : π x = ⟨x,hmem⟩ := by
      exact Submodule.projectionOnto_apply_of_mem_left hP hmem
    have he : e (⟨x,hmem⟩ : K.ker) = e 0 := by
      simpa only [ℓ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hπ,map_zero] using hℓ
    exact congrArg Subtype.val (e.injective he)
  have hi : Function.Injective (K.prod ℓ) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    · rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  refine ⟨ℓ,hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (K.prod ℓ).toLinearMap) _).mp hi
  simp [Base,ProjectionTarget]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleLocusChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth submersion coordinates for the three-component difference
map on a pair of surface charts. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem double_locus_submersion_chart {f : Base × Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base × Base)
    (hsurj : Function.Surjective (fderiv ℝ f p)) :
    ∃ e : OpenPartialHomeomorph (Base × Base) (ProjectionTarget 3 × ℝ), p ∈ e.source ∧
      (∀ x, (e x).1 = f x) ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨ℓ,hℓ⟩ := double_locus_linear_augmentation (fderiv ℝ f p) hsurj
  let L := ContinuousLinearEquiv.ofBijective ((fderiv ℝ f p).prod ℓ)
    (LinearMap.ker_eq_bot.mpr hℓ.1) (LinearMap.range_eq_top.mpr hℓ.2)
  let g : Base × Base → ProjectionTarget 3 × ℝ := fun x => (f x,ℓ x)
  have hg : ContDiff ℝ ∞ g := hf.prodMk ℓ.contDiff
  have hd : HasFDerivAt g L.toContinuousLinearMap p :=
    (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.prodMk ℓ.hasFDerivAt
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W : Set (Base × Base) := {x | IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g x))}
  have hcont : Continuous (fun x => L.symm.toContinuousLinearMap.comp (fderiv ℝ g x)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have hpW : p ∈ W := by
    change IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g p))
    rw [hd.fderiv]
    have heq : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (Base × Base) := by
      apply ContinuousLinearMap.ext
      intro v
      exact L.symm_apply_apply v
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : Base × Base → ProjectionTarget 3 × ℝ) = g := rfl
  refine ⟨e,⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hpW⟩,
    (fun _ => rfl),?_,?_⟩
  · simpa only [he] using hg
  · intro y hy
    have hunit : IsUnit (L.symm.toContinuousLinearMap.comp (fderiv ℝ g (e.symm y))) :=
      (e.map_target hy).2
    obtain ⟨u,hu⟩ := hunit
    let D := (ContinuousLinearEquiv.ofUnit u).trans L
    have heq : D.toContinuousLinearMap = fderiv ℝ g (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro v
      change L ((u : (Base × Base) →L[ℝ] (Base × Base)) v) = _
      rw [hu]
      exact L.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,heq]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarFlatTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cubic remainder estimate at a scalar flat second jet. This is the
low-dimensional flat-stratum estimate needed for double-locus regularity. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance scalarFirstNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance scalarFirstSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
local instance scalarSecondNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance scalarSecondSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarFlatHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flat second-jet stratum of a smooth scalar surface function has
locally cubic Hölder control. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance holderFirstNormed : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance holderFirstSpace : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
local instance holderSecondNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance holderSecondSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance

local instance holderThirdNormed_ra07c31_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
local instance holderThirdSpace_ra07c31_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] Base →L[ℝ] ℝ) := inferInstance
def scalarFlatTwo (f : Base → ℝ) : Set Base :=
  {x | fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveNormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit invertible three-dimensional frame along a regular curve. -/
noncomputable section
open Set Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def curveNormalLinear (v a : Fin 3 → ℝ) : (Base × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.snd ℝ Base ℝ).smulRight v +
    ((ContinuousLinearMap.proj (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ Base ℝ)).smulRight a +
    ((ContinuousLinearMap.proj (1 : Fin 2)).comp (ContinuousLinearMap.fst ℝ Base ℝ)).smulRight (v ⨯₃ a)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapLinearCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit invertible linear coordinates adapted to the kernel of a crosscap. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crosscapSourceLinear (b : Bool) (t : ℝ) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj (0 : Fin 2)).smulRight (tangentRayVelocity b) +
    (ContinuousLinearMap.proj (1 : Fin 2)).smulRight (tangentRay b t)

lemma crosscapSourceLinear_apply (b : Bool) (t : ℝ) (x : Base) :
    crosscapSourceLinear b t x = x 0 • tangentRayVelocity b + x 1 • tangentRay b t := rfl

lemma crosscapSourceLinear_coordinates (b : Bool) (t : ℝ) (x : Base) :
    tangentTransverseCoefficient b t (crosscapSourceLinear b t x) = x 0 ∧
      tangentRayCoefficient b (crosscapSourceLinear b t x) = x 1 := by
  cases b <;> simp [crosscapSourceLinear_apply,tangentTransverseCoefficient,
    tangentRayCoefficient,tangentRayVelocity,tangentRay] <;> ring

lemma crosscapSourceLinear_bijective (b : Bool) (t : ℝ) :
    Function.Bijective (crosscapSourceLinear b t) := by
  constructor
  · intro x y h
    have h0 := congrArg (tangentTransverseCoefficient b t) h
    have h1 := congrArg (tangentRayCoefficient b) h
    rw [(crosscapSourceLinear_coordinates b t x).1,
      (crosscapSourceLinear_coordinates b t y).1] at h0
    rw [(crosscapSourceLinear_coordinates b t x).2,
      (crosscapSourceLinear_coordinates b t y).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  · intro x
    refine ⟨![tangentTransverseCoefficient b t x,tangentRayCoefficient b x],?_⟩
    simpa only [crosscapSourceLinear_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using
      (tangentRay_decomposition b t x).symm

def crosscapSourceEquiv (b : Bool) (t : ℝ) : Base ≃L[ℝ] Base :=
  ContinuousLinearEquiv.ofBijective (crosscapSourceLinear b t)
    (LinearMap.ker_eq_bot.mpr (crosscapSourceLinear_bijective b t).1)
    (LinearMap.range_eq_top.mpr (crosscapSourceLinear_bijective b t).2)

/-- Reorder the linearized direction variables into the standard crosscap target coordinates. -/
def crosscapParameterLinear (b : Bool) (t : ℝ) :
    (Base × ℝ) →L[ℝ] (Base × ℝ) :=
  (((ContinuousLinearMap.proj (0 : Fin 2)).comp (ContinuousLinearMap.fst ℝ Base ℝ)).smulRight
      (tangentRayVelocity b) +
    ((1/2 : ℝ) • ((ContinuousLinearMap.proj (1 : Fin 2)).comp
      (ContinuousLinearMap.fst ℝ Base ℝ))).smulRight (tangentRay b t)).prod
    (ContinuousLinearMap.snd ℝ Base ℝ)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneCurveFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A transverse linear coordinate for a regular curve in the surface plane. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeCurveLinear (v w : Base) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj (0 : Fin 2)).smulRight v +
    (ContinuousLinearMap.proj (1 : Fin 2)).smulRight w

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PlaneCurveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local coordinates straightening a regular curve in the surface plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeCurveTube (c : ℝ → Base) (v : Base) (x : Base) : Base := c (x 1)+x 0 • v

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nondegenerate quadratic crosscap is a standard umbrella followed
by a target map whose derivative at the origin is invertible. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance tripleNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance tripleSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

/-- A quadratic target shear with identity differential at the origin. -/
def crosscapTargetShear (β : Base × ℝ) (z : Base × ℝ) : Base × ℝ :=
  z + z.2^2 • β

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardCrosscapDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard umbrella has one singular point and a transverse double ray. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance standardBaseNormed : NormedAddCommGroup Base := inferInstance
local instance standardBaseSpace : NormedSpace ℝ Base := inferInstance
local instance standardTripleNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance standardTripleSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

def standardCrosscapDerivative (x : Base) : Base →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.pi ![
    x 1 • ContinuousLinearMap.proj (0 : Fin 2) + x 0 • ContinuousLinearMap.proj (1 : Fin 2),
    (2*x 1) • ContinuousLinearMap.proj (1 : Fin 2)]).prod (ContinuousLinearMap.proj (0 : Fin 2))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceRegularPairLocus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularity of a surface coincidence is an open first-jet condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def regularSurfacePairs (f : M → ProjectionTarget 3) : Set (M × M) :=
  {z | f z.1 ≠ f z.2 ∨ Function.Surjective (surfacePairDerivative f z.1 z.2)}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CleanSurfacePairs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular pairs which additionally have no coincidence involving the
prescribed finite singular set form an open, stable condition. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def cleanSurfacePairs (f : M → ProjectionTarget 3) (S : Set M) : Set (M × M) :=
  regularSurfacePairs f ∩ {z | f z.1 ≠ f z.2 ∨ (z.1 ∉ S ∧ z.2 ∉ S)}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapNormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth target coordinates identifying a prepared quadratic jet
with the standard Whitney umbrella. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance normalSourceNormed : NormedAddCommGroup (Base × ℝ) := inferInstance
local instance normalSourceSpace : NormedSpace ℝ (Base × ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TriangularTimeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing the longitudinal coordinate by a smooth function with
unit axial derivative is an actual local plane diffeomorphism. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def timeCoordinateMap (φ : Base → ℝ) (x : Base) : Base := ![x 0,φ x]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TimeCoordinateBlend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonlinear blend of two agreeing time coordinates has
an invertible derivative when their transverse transition is positive. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def timeCoordinateBlend (g : Base → Base) (χ : Base → ℝ) (x : Base) : Base :=
  (1-χ x) • x + χ x • g x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PairCurveChartDerivative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injectivity of the paired curve velocity is invariant under the
actual two surface charts. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem paired_curve_derivative_injective
    {A B : ℝ → M} {θ : ℝ → Base × Base} (x y : M) (t : ℝ)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A t)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B t)
    (hAx : A t ∈ (chart x).source) (hBy : B t ∈ (chart y).source)
    (hθ : ContDiffAt ℝ ∞ θ t)
    (he : θ =ᶠ[𝓝 t] fun s => (chart x (A s),chart y (B s)))
    (hinj : Function.Injective (fderiv ℝ θ t)) :
    Function.Injective ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)) := by
  have hx := ((chart_smooth x) (A t) hAx).contMDiffAt ((chart x).open_source.mem_nhds hAx)
  have hy := ((chart_smooth y) (B t) hBy).contMDiffAt ((chart y).open_source.mem_nhds hBy)
  have heA : (fun s => (θ s).1) =ᶠ[𝓝 t] (chart x) ∘ A := he.mono fun _ hs => congrArg Prod.fst hs
  have heB : (fun s => (θ s).2) =ᶠ[𝓝 t] (chart y) ∘ B := he.mono fun _ hs => congrArg Prod.snd hs
  have hdA : fderiv ℝ (fun s => (θ s).1) t =
      (mfderiv planeModel 𝓘(ℝ,Base) (chart x) (A t)).comp (mfderiv 𝓘(ℝ) planeModel A t) := by
    have h : mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (fun s => (θ s).1) t =
        mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) ((chart x) ∘ A) t := heA.mfderiv_eq
    rw [mfderiv_eq_fderiv,mfderiv_comp t (hx.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp))] at h
    exact h
  have hdB : fderiv ℝ (fun s => (θ s).2) t =
      (mfderiv planeModel 𝓘(ℝ,Base) (chart y) (B t)).comp (mfderiv 𝓘(ℝ) planeModel B t) := by
    have h : mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (fun s => (θ s).2) t =
        mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) ((chart y) ∘ B) t := heB.mfderiv_eq
    rw [mfderiv_eq_fderiv,mfderiv_comp t (hy.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp))] at h
    exact h
  have hfst : fderiv ℝ (fun s => (θ s).1) t = ((ContinuousLinearMap.fst ℝ Base Base).comp (fderiv ℝ θ t)) :=
    (hθ.differentiableAt (by simp)).hasFDerivAt.fst.fderiv
  have hsnd : fderiv ℝ (fun s => (θ s).2) t = ((ContinuousLinearMap.snd ℝ Base Base).comp (fderiv ℝ θ t)) :=
    (hθ.differentiableAt (by simp)).hasFDerivAt.snd.fderiv
  intro a b hab
  apply hinj
  apply Prod.ext
  · change ((ContinuousLinearMap.fst ℝ Base Base).comp (fderiv ℝ θ t)) a = ((ContinuousLinearMap.fst ℝ Base Base).comp (fderiv ℝ θ t)) b
    rw [← hfst,hdA]
    exact congrArg (mfderiv planeModel 𝓘(ℝ,Base) (chart x) (A t)) (congrArg Prod.fst hab)
  · change ((ContinuousLinearMap.snd ℝ Base Base).comp (fderiv ℝ θ t)) a = ((ContinuousLinearMap.snd ℝ Base Base).comp (fderiv ℝ θ t)) b
    rw [← hsnd,hdB]
    exact congrArg (mfderiv planeModel 𝓘(ℝ,Base) (chart y) (B t)) (congrArg Prod.snd hab)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnorderedLinePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two sides of a line become a half-line after forgetting their
ordering. This is the endpoint coordinate for a prepared crosscap. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def unorderedLinePair (a w : Base) (t : ℝ) : UnorderedSurfacePairs Base :=
  unorderedPair (a+t • w,a-t • w)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PlaneCommonCoordinate
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common linear plane coordinate is regular on either of two nonzero
curve velocities, including the case of collinear opposite velocities. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeShearLinear (a : ℝ) : Base →L[ℝ] Base :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj (0 : Fin 2) +
    a • ContinuousLinearMap.proj (1 : Fin 2),ContinuousLinearMap.proj (1 : Fin 2)]

lemma planeShearLinear_apply (a : ℝ) (v : Base) :
    planeShearLinear a v = ![v 0+a*v 1,v 1] := by
  ext i
  fin_cases i <;> rfl

lemma planeShearLinear_bijective (a : ℝ) : Function.Bijective (planeShearLinear a) := by
  constructor
  · intro v w he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    change v 0+a*v 1 = w 0+a*w 1 at h0
    change v 1 = w 1 at h1
    ext i
    fin_cases i
    · change v 0 = w 0
      rw [h1] at h0
      exact add_right_cancel h0
    · exact h1
  · intro w
    refine ⟨![w 0-a*w 1,w 1],?_⟩
    rw [planeShearLinear_apply]
    ext i
    fin_cases i <;> simp

def planeShearEquiv (a : ℝ) : Base ≃L[ℝ] Base :=
  ContinuousLinearEquiv.ofBijective (planeShearLinear a)
    (LinearMap.ker_eq_bot.mpr (planeShearLinear_bijective a).1)
    (LinearMap.range_eq_top.mpr (planeShearLinear_bijective a).2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RoundedReturnCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit embedded U-turn between disjoint graph branches. It is
flatly equal to the lower and upper graphs at the two ends. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def roundedReturnCurve (f g : ℝ → ℝ) (a b t : ℝ) : Base :=
  ![a+b*t^2,(1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SmallGraphBlends
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All convex interpolations between two graphs remain in a prescribed
neighborhood when their common base point is approached. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def graphPoint (f : ℝ → ℝ) (x : ℝ) : Base := ![x,f x]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledGraphJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A graph corner can be rounded at an arbitrarily small horizontal scale. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def scaledGraphJoin (f g : ℝ → ℝ) (a b t : ℝ) : Base :=
  ![a+b*t,(1-centeredSmoothStep t)*f (a+b*t)+centeredSmoothStep t*g (a+b*t)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NormalDefectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine two-component normal defect for the derivative of a surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def coordinateDifferential (φ : Base → ProjectionTarget 3) (x : Base) : Base →L[ℝ] (Fin 3 → ℝ) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.comp (fderiv ℝ φ x)

def transverseDerivative (φ : Base → ProjectionTarget 3) (x : Base) : Fin 3 → ℝ :=
  coordinateDifferential φ x (![1,0] : Base)

def normalDefect (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) (x : Base) : Base :=
  ((curveNormalLinear (transverseDerivative φ x) a).inverse
    (coordinateDifferential φ x (![0,1] : Base))).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth normalized primitives on the open admissible parameter domain. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The primitive is jointly smooth wherever the parameter family is smooth. -/
theorem contDiffOn_primitive_joint {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => primitive (fun t => F (z.1, t)) z.2) (S ×ˢ univ) := by
  apply (hS.prod isOpen_univ).contDiffOn_iff.mpr
  intro z hz
  obtain ⟨G, hG, he⟩ := SmoothParameterIntegral.exists_smooth_extension_near hS hF hz.1
  apply (contDiff_primitive_joint hG).contDiffAt.congr_of_eventuallyEq
  have he' := (continuous_fst.continuousAt :
    Tendsto Prod.fst (𝓝 z) (𝓝 z.1)).eventually he
  filter_upwards [he'] with w hw
  have hf : (fun t => F (w.1, t)) = fun t => G (w.1, t) := funext (fun t => (hw t).symm)
  rw [hf]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomials in actual coordinate jets, with coefficients smooth in
position, the second jet, and the periodic variable. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

def mul : Expression → Expression → Expression
  | .coeff c, f => mapCoeff (fun d z => c z * d z) f
  | .atom w a e, f => .atom w a (mul e f)
  | .add e g, f => .add (mul e f) (mul g f)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual differentiation of mixed jet polynomials in the base-map slot. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

def varyBase (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ) : Fin 4 → Base → Space :=
  fun i p => if i = 0 then G 0 p + s • H p else G i p

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ParameterTaylorRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic Taylor remainders retain all weighted spatial derivative bounds
under integration in the variation parameter. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.ParameterTaylor
open SmoothPeriodicCalculus SmoothParameterIntegral WeightedEstimates

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def parameterJet : ℕ → (A × ℝ → E) → A × ℝ → E
  | 0, F => F
  | j + 1, F => angleDerivative (parameterJet j F)

def cubicRemainder (F : A × ℝ → E) (p : A) : E :=
  F (p, 1) - F (p, 0) - parameterJet 1 F (p, 0) - (1 / 2 : ℝ) • parameterJet 2 F (p, 0)

end ClosedSurfaceR4.ParameterTaylor

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multilinear scaling of the three actual polynomial variations. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

namespace MixedExpression

def rescale (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) : Fin 4 → Base → Space :=
  ![G 0, fun p => c 0 • G 1 p, fun p => c 1 • G 2 p, fun p => c 2 • G 3 p]

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexJetDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and imaginary parts commute with all actual ordered jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def realField (H : Base → Fin 4 → ℂ) : Base → Space := fun p a => (H p a).re
def imagField (H : Base → Fin 4 → ℂ) : Base → Space := fun p a => (H p a).im

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ConjugatedPolynomialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The oscillatory estimates apply to the actual conjugated polynomial
linearization on supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

def singlePhase (φ : Base → ℝ) : Fin 3 → Base → ℝ := ![φ, 0, 0]
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FinitePolynomialPhases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite expansion of the polynomial quadratic term before
separating its zero phases. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets


def oscillatorySum {ι : Type*} [Fintype ι] (τ : ℝ) (φ : ι → Base → ℝ)
    (H : ι → Base → Fin 4 → ℂ) : Base → Fin 4 → ℂ :=
  fun p => ∑ i, phase τ (φ i) p • H i p

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

def sumList {ι : Type*} : List ι → (ι → Expression) → Expression
  | [], _ => .coeff (fun _ => 0)
  | i :: l, f => .add (f i) (sumList l f)

def lowFactor (v : Fin 2) : LowIndex → Expression
  | .inl i => .coeff (fun _ => coordinateVector v i)
  | .inr (w, a) => .atom (v :: lowWord w) a (.coeff (fun _ => 1))

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetPullbackExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate derivatives in a second chart, expressed by finite jet
polynomials in the first chart. Only the surface and four-space dimensions
used in the primitive construction are considered. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial

def inverseCoordinateCoefficient (T S : Base → Base) (i k : Fin 2) : LowJet × ℝ → ℝ :=
  fun z => (fderiv ℝ S (T (lowPosition z.1)) (coordinateVector i)) k

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate pullback of a finite jet polynomial, with the low-jet
substitution and inverse differential proved from the actual local inverse.
No compatibility of the polynomial values is assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

def coordinateLowJetSubstitution (T S : Base → Base) (J : LowJet) : LowJet :=
  lowJetCoordinateChange S (T (lowPosition J),J)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPeriodicCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The periodic corrector constructed smoothly over finite-dimensional
families of geometric data. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.PeriodicCorrector

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def correctorFamily (V : A → C(Period, E)) (r : A → C(Period, ℝ)) (q : A → ℝ) :
    A → C(Period, E) := fun p =>
  ⟨parameterCorrector V r q p, by
    unfold parameterCorrector correctedVector correctedScalar
    exact continuous_const.smul ((((r p).continuous.add
      ((((V p).continuous.sub continuous_const).inner continuous_const).div_const _)).smul
        (V p).continuous).sub continuous_const)⟩

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PeriodicCorrectorFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit formulas for the canonical angular correction. -/
noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The right-hand side of the normal covariance equation. -/
def angularSourceFunction (Y C X₀ : E) (V : C(Period, E))
    (h K e : ℝ → ℝ) (t : ℝ) : ℝ :=
  let a := fun s : ℝ => inner ℝ (X₀ + V (s : Period)) (spanSolve Y C (h s, deriv K s))
  e t - (a t - ∫ s in 0..1, a s)

def angularCorrectionFunction (Y C X₀ : E) (V : C(Period, E)) (q : ℝ)
    (h K e : ℝ → ℝ) (t : ℝ) : E :=
  spanSolve Y C (PeriodicPrimitive.primitive h t, K t) +
    PeriodicPrimitive.primitive (realCorrector V q (angularSourceFunction Y C X₀ V h K e)) t

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalFullPeriodicCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete periodic corrector with all hypotheses restricted to an open chart domain. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PeriodicCorrector
open CovarianceCorrector LocalPeriodicCalculus
open SmoothPeriodicCalculus (slowDerivative)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The concrete full correction uses the genuine slow derivative of the
normalized primitive in its transverse datum. -/
def fullSolutionFormula (v : A) (Y C X₀ : A → E) (V : A → C(Period, E))
    (q : A → ℝ) (h j e : A → C(Period, ℝ)) (z : A × ℝ) : E :=
  JetPolynomial.angularCorrectionFunction (Y z.1) (C z.1) (X₀ z.1) (V z.1) (q z.1)
    (fun t => h z.1 (t : Period))
    (fun t => fderiv ℝ (fun p => PeriodicPrimitive.primitive
      (fun s : ℝ => h p (s : Period)) t) z.1 v - j z.1 (t : Period))
    (fun t => e z.1 (t : Period)) z.2

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialFullCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial construction for every component of the complete periodic
corrector. Only the transverse derivative increases the highest jet order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def spanCoefficient (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (b : ℝ × ℝ) : LowJet × ℝ → ℝ :=
  fun z => L (spanSolve (Y z.1) (C z.1) b)

def metricCoefficient (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (b : ℝ × ℝ) : LowJet × ℝ → ℝ :=
  fun z => inner ℝ (X₀ z.1 + V z.1 (z.2 : Period)) (spanSolve (Y z.1) (C z.1) b)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorCoordinatePullbackBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed nonlinear coordinate changes preserve weighted tensor error
bounds with a constant independent of the fast scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def tensorCoordinateMatrixUnit (k l : Fin 3) : PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
  (ContinuousLinearMap.proj l).smulRight (Pi.single k 1)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorReadReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction from tensor readings and the squared atlas partition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base planeCoordinateIsometry)
local instance readReconstructFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance readReconstructFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalDefectDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal-defect coordinates exist on a genuine open neighborhood
of the entire compact crosscap strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalFrameDomain (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) : Set Base :=
  {x | transverseDerivative φ x ⨯₃ a ≠ 0}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalFrameJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular three-dimensional direction jet induces a regular
normal-defect jet in the transverse two-plane. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def directionBlock (K : Base →L[ℝ] (Fin 3 → ℝ)) (u : Fin 3 → ℝ) :
    (Base × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  K.comp (ContinuousLinearMap.fst ℝ Base ℝ) + (ContinuousLinearMap.snd ℝ Base ℝ).smulRight u

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisDirectionJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-direction jet with the longitudinal vector in the kernel. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def axisDirectionJet (f : Base → V) (p : Base) : (Base × ℝ) →L[ℝ] V :=
  (fderiv ℝ f p).comp ((ContinuousLinearMap.snd ℝ Base ℝ).smulRight (![1,0] : Base)) +
    ((fderiv ℝ (fderiv ℝ f) p).comp (ContinuousLinearMap.fst ℝ Base ℝ)).flip (![0,1] : Base)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedLinearModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first-order transverse model in normalized coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalizedAxisPolynomial (p q : ℝ) (x : Base) : Base :=
  ![(x 1-p)*(x 1-q),0]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseJetConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common vertical column and matching transverse signs preserve rank
under convex interpolation of the endpoint jets. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def triangularPlaneJet (a b c : ℝ) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj 0).smulRight (![a,b] : Base)+
    (ContinuousLinearMap.proj 1).smulRight (![c,0] : Base)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_DiagonalDefectModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal transverse models retain the two prescribed axial zeros. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def diagonalDefectModel (b : ℝ → ℝ) (p q : ℝ) (x : Base) : Base :=
  normalizedAxisPolynomial p q x+(x 0*b (x 1)) • (![0,1] : Base)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneDefectInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex interpolation with matching transverse signs retains the simple
axial zeros on one common rectangle. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeDefectInterpolation (F G : Base → Base) (s : ℝ) (x : Base) : Base :=
  (1-s) • F x+s • G x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRotationFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial rotation columns from a three-coordinate quaternion.
They fill a twice-winding planar frame by allowing its first column to move. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def polynomialRotationFrame (a b c : ℝ) : Base →L[ℝ] FrameTarget :=
  (ContinuousLinearMap.proj 0).smulRight (rotationFirst a b c) +
    (ContinuousLinearMap.proj 1).smulRight (rotationSecond a b c)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ShiftedRotationFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation columns with an exterior constant shift. This allows the
twice-winding frame to have two separated simple zeros before filling. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def shiftedRotationFrame (a b c e : ℝ) : Base →L[ℝ] FrameTarget :=
  polynomialRotationFrame a b c-
    (ContinuousLinearMap.proj 1).smulRight (![0,e,0] : FrameTarget)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalizeFrameColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive normalization of the first column of a smooth rank-two frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def scaleFirstInput (r : ℝ) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj 0).smulRight (![r,0] : Base)+
    (ContinuousLinearMap.proj 1).smulRight (![0,1] : Base)

def firstColumnLength (L : Base →L[ℝ] FrameTarget) : ℝ :=
  Real.sqrt ((L (![1,0] : Base) 0)^2+(L (![1,0] : Base) 1)^2+(L (![1,0] : Base) 2)^2)

def normalizeFrameColumn (L : Base →L[ℝ] FrameTarget) : Base →L[ℝ] FrameTarget :=
  L.comp (scaleFirstInput (firstColumnLength L)⁻¹)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleRotationFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit relative filling of the twice-winding planar frame.
The third quaternion coordinate is a compact bump; no square-root choice
or topological extension assumption is needed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def filledDoubleRotation (χ : Base → ℝ) (x : Base) : Base →L[ℝ] FrameTarget :=
  polynomialRotationFrame (x 0) (x 1) (χ x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ShiftedRotationFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact explicit filling of the frame for two equal-index zeros. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def shiftedDoubleFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  shiftedRotationFrame (x 0) (x 1) 0 1

def filledShiftedRotation (χ ψ : Base → ℝ) (x : Base) : Base →L[ℝ] FrameTarget :=
  filledDoubleRotation χ x-
    (ContinuousLinearMap.proj 1).smulRight (![0,1-ψ x,0] : FrameTarget)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PairModelCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine coordinates and invertible normal rescalings for the model pair. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def pairCoordinateMap (c h k : ℝ) (x : Base) : Base := ![(x 1-c)/h,k*x 0]
def pairCoordinateInverse (c h k : ℝ) (y : Base) : Base := ![y 1/k,c+h*y 0]

lemma pairCoordinateMap_smooth (c h k : ℝ) : ContDiff ℝ ∞ (pairCoordinateMap c h k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [pairCoordinateMap] <;> fun_prop
lemma pairCoordinateInverse_smooth (c h k : ℝ) : ContDiff ℝ ∞ (pairCoordinateInverse c h k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [pairCoordinateInverse] <;> fun_prop

def pairCoordinates (c h k : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) : Base ≃ₜ Base where
  toFun := pairCoordinateMap c h k
  invFun := pairCoordinateInverse c h k
  left_inv := by
    intro x
    ext i
    fin_cases i
    · change (k*x 0)/k = x 0
      field_simp
    · change c+h*((x 1-c)/h) = x 1
      field_simp
      ring
  right_inv := by
    intro x
    ext i
    fin_cases i
    · change (c+h*x 0-c)/h = x 0
      field_simp
      ring
    · change k*(x 1/k) = x 1
      field_simp
  continuous_toFun := (pairCoordinateMap_smooth c h k).continuous
  continuous_invFun := (pairCoordinateInverse_smooth c h k).continuous

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CenteredPairModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed canonical normal fields and their scaled frame fillings. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def centeredOppositeNormal (c h s : ℝ) (x : Base) : Base :=
  ![(x 1-c)^2-h^2,s*x 0]

def centeredEqualNormal (c h k s : ℝ) (x : Base) : Base :=
  ![(x 1-c)^2-h^2-(h*k*x 0)^2,s*((x 1-c)/h)*x 0]

def centeredEqualHomotopy (c h k s v : ℝ) (x : Base) : Base :=
  ![(x 1-c)^2-h^2-v*(h*k*x 0)^2,s*((x 1-c)/h)*x 0]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasMeanIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual quadratic zero-phase terms of the charted free oscillations
restore to the input global tensor plus the global nonlinear mean. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance chartedAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance chartedAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance chartedAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance chartedAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance quadraticAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance quadraticAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance quadraticAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance quadraticAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance quadraticAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoupledSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint map/tensor input bound and its actual two-scale smoothing tail. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

local instance coupledModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coupledModelSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section

namespace ClosedSurfaceR4.PhaseMean
open RealModes FiniteMean

def polynomialMeanSize (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (j m : ℕ) (x : ℝ) : ℝ :=
  sizeBound L (fun r => H r x) (polynomialMeanProfile p C (fun r => G r x)) j m

def polynomialMeanDifference (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (j m : ℕ) (x : ℝ) : ℝ :=
  differenceBound L (fun r => H r x)
    (polynomialMeanProfile p C (fun r => G r x)) (polynomialMeanProfile p C (fun r => G r x)) j m

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMeanExplicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas mean estimate with its read and restore constants exposed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance explicitAtlasMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance explicitAtlasMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance explicitAtlasMeanDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance explicitAtlasMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas mean estimate with its read and restore constants exposed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance polynomialAtlasMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAtlasMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAtlasMeanDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAtlasMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCoefficientExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients can be extended smoothly off the permitted compact low-jet
set without changing the operator there or changing its jet order/loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def cutoffCoeffs (e : Expression) (χ : LowJet → ℝ) : Expression :=
  e.mapCoeff (fun c z => χ z.1 * c z)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAtlasMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual atlas mean bounds with polynomial dependence on all local budgets
and on the number of cells in each chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates FiniteMean
local instance polynomialFiniteMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFiniteMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFiniteMeanDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFiniteMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorFiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite derivative-losing mean substitution on global surface tensors.
The actual section iterates are recovered exactly from their atlas encoding. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance finiteMeanModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteMeanModelSpace : NormedSpace ℝ TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTensorMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial threshold for the actual global tensor iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean RealModes WeightedEstimates FiniteMean
open JetPolynomial (Base)
local instance polynomialTensorMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialTensorMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAtlasTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialFiniteTrialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFiniteTrialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFiniteTrialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFiniteTrialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perturbation operators and their actual first variations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {n : ℕ}

def eval (P : Fin n → Expression) (ε : ℝ) (G : Base → Space) (z : Base × ℝ) : ℝ :=
  ∑ l, ε ^ (l.val + 1) * (P l).eval G z

def variation (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space) (z : Base × ℝ) : ℝ :=
  ∑ l, ε ^ (l.val + 1) * (P l).variation G H z

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the finite input norm and the small residual power from the
geometric solver constants. The input order is explicit. -/
noncomputable section
open scoped NNReal ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ}
  {P : Fin 3 → Fin n → Expression}
  {ε τ : ℝ}
  {G : Base → Space}
  {hG : ContDiff ℝ ∞ G}
  {φ : Base → ℝ}
  {K : TopologicalSpace.Compacts Base}
  {s : ℝ≥0}

def inputOrder (q m : ℕ) : ℕ := m + (q + 1) * (tensorOrder P + 1)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialProfileTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The size and residual factors depend only on numeric coefficient profiles,
not on the map, phase, chart, target or scale in a solver record.  The pure
profiles let a family use those factors without introducing a reference
solver at unit scale.
-/

noncomputable section

open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ}

def κProfile (P : Fin 3 → Fin n → Expression) (C D : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (SmallModes.errorConstant m (C m))
    (D m * SmallModes.initialConstant 4 (m + tensorOrder P) (C (m + tensorOrder P)))

def sizeProfile (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ) * 2 ^ m *
    SmallModes.forcedModeBudget 4 (tensorOrder P) C D q m * J m ^ m

def residualProfile (P : Fin 3 → Fin n → Expression) (C D J : ℕ → ℝ) (q m : ℕ) : ℝ :=
  tensorChartBudget m (J m) (J (m + 1)) * 2 ^ m *
    FiniteParametrix.boundProfile (tensorOrder P + 1)
      (κProfile P C D) (κProfile P C D) q m

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSmoothingProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for smoothed inputs with a polynomial finite input budget. -/
noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates RealModes
local instance polySmoothingProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polySmoothingProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTensorReadBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseMean RealModes
local instance polynomialTensorReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialTensorReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialTensorReadDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialTensorReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PrimitiveInitialMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar contraction starts the primitive mean iteration.
Its normalized defect is only the polynomial perturbation divided by δ². -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PhaseMean

def primitiveSeed (δ : ℝ) (F : JetPolynomial.Base → JetPolynomial.Space) :
    JetPolynomial.Base → JetPolynomial.Space := fun x => Real.sqrt (1-δ^2) • F x

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformAtlasMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform global majorants for the actual charted polynomial means.
Constants precede both scales, all coordinate maps and all local solvers. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

local instance uniformAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformAtlasDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ProfiledAtlasAdjustedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite mean adjustment from profiles, including varying base maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation
local instance profiledMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance profiledMeanDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothedInputCloseness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed low input bound controls the map's C2 smoothing error and
the encoded tensor smoothing error with the same positive scale power. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

local instance inputClosenessFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputClosenessFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SpecialPointCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small affine bumps prescribe the vertical derivative near an isolated special point. -/
noncomputable section
open Filter Set Metric
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

def pointCorrection (p : Base) (φ : ContDiffBump p) (B : ℝ) (x : Base) : ℝ :=
  B * (x.2 - p.2) * φ x

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth orthonormal frames obtained by interpolating non-antipodal plane directions. -/
noncomputable section
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

def blend (u v : Vec) (t : ℝ) : Vec := (1 - t) • u + t • v

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactNormalTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normal nondegeneracy from the three bounded derivatives of a
primitive ansatz. No bound on its rapidly oscillating xx derivative is used. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

abbrev NormalTriple := Fin 3 → Vec

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricCalculus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric identities for actual smooth maps on the surface. The
finite-sum identity retains every cross term between distinct chart modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def linearMetricForm (F U : M → V) (p : M) (v w : TangentSpace planeModel p) : ℝ :=
  inner ℝ (surfaceDifferential F p v) (surfaceDifferential U p w) +
  inner ℝ (surfaceDifferential U p v) (surfaceDifferential F p w)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalFrameTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact algebra transporting a filled normalized frame to the derivative
of the original surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def longitudinalShear (c : ℝ) : Base →L[ℝ] Base :=
  ContinuousLinearMap.id ℝ Base+(ContinuousLinearMap.proj 1).smulRight (![c,0] : Base)

def longitudinalCoefficient (φ : Base → ProjectionTarget 3) (a : FrameTarget) (x : Base) : ℝ :=
  ((curveNormalLinear (transverseDerivative φ x) a).inverse
    (coordinateDifferential φ x (![0,1] : Base))).2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive density's circle diffeomorphism has a jointly smooth inverse. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

def equation (ρ : B × ℝ → ℝ) (z : (B × ℝ) × ℝ) : ℝ :=
  clock ρ z.1.1 z.2 - z.1.2

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuantitativeMetricExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pullback metric, after subtracting its finite mean expansion,
has the fast-scale remainder bound used by the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

namespace MetricPolynomial

def metricDirection (dx dy : Base) (b : Bool) : Base := if b then dx else dy

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SafeNormalizationStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed smooth extension acts uniformly continuously on bounded
first jets. This gives the C1 stability used in finite-point preparation. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets
open WeightedEstimates
abbrev SafeFirstJet := Space × (JetPolynomial.Base →L[ℝ] Space)

def safeNormalizeFirstJet (J : SafeFirstJet) : SafeFirstJet :=
  (safeRadialNormalize J.1,(fderiv ℝ safeRadialNormalize J.1).comp J.2)

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarJetTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite jet-polynomial transport under multiplication by a fixed
smooth scalar function. This accounts for the atlas outer cutoffs before
coordinate transport. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

def scalarJetFirst (a : Base → ℝ) (x : Base) (J : LowJet) (v : Fin 2) (k : Fin 4) : ℝ :=
  a x * J (.inr (firstJetSlot v,k)) + J (.inr (0,k)) * coordinatePartial a v x

def scalarJetSecond (a : Base → ℝ) (x : Base) (J : LowJet)
    (v w : Fin 2) (k : Fin 4) : ℝ :=
  a x * J (.inr (secondJetSlot v w,k)) +
    J (.inr (firstJetSlot w,k)) * coordinatePartial a v x +
    coordinatePartial a w x * J (.inr (firstJetSlot v,k)) +
    J (.inr (0,k)) * coordinatePartial (coordinatePartial a w) v x

/-- Multiplication preserves the position slots and transforms the value,
first derivatives, and ordered second derivatives by the product rule. -/
def lowJetScalarProduct (a : Base → ℝ) (p : Base × LowJet) : LowJet
  | .inl i => p.1 i
  | .inr (w,k) => ![a p.1 * p.2 (.inr (0,k)),
      scalarJetFirst a p.1 p.2 0 k,
      scalarJetFirst a p.1 p.2 1 k,
      scalarJetSecond a p.1 p.2 0 0 k,
      scalarJetSecond a p.1 p.2 0 1 k,
      scalarJetSecond a p.1 p.2 1 0 k,
      scalarJetSecond a p.1 p.2 1 1 k] w

/-- The smooth coefficient substitution needs no separate position input
because an actual low jet already stores its base point. -/
def scalarLowJetSubstitution (a : Base → ℝ) (J : LowJet) : LowJet :=
  lowJetScalarProduct a (lowPosition J,J)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SingleTensorRestoreBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed atlas estimate for the single tensor patch of a primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
local instance singleTensorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance singleTensorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance singleTensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorBundleInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth pointwise inversion for the actual tensor bundle. This is the
local analytic operation used to correct a finite perturbed primitive sum. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance inverseTensorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inverseTensorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance inverseTensorFiberComplete_ra07c31_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inverseTensorDualSmul
local instance inverseTensorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)

local instance inverseTensorSectionSpace_ra07c31_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorEndomorphismCoordinates
    (A : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p) (p x : M) :
    TensorFiber →L[ℝ] TensorFiber :=
  ContinuousLinearMap.inCoordinates TensorFiber (CovariantTwoTensor (M := M))
    TensorFiber (CovariantTwoTensor (M := M)) p x p x (A x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorExpressionLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth changes of tensor trivialization act on finite jet
polynomials by finite linear combinations with positional coefficients. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial

def tensorLinearCoefficient (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (k l : Fin 3) : LowJet × ℝ → ℝ :=
  fun z => L (lowPosition z.1) (Pi.single l 1) k

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation of the finite primitive operator by tensor coordinates. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance conjugateFiberNormed : NormedAddCommGroup TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate conjugation of the actual primitive operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance frameAlgebraFiberNormed_ra07c31_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance frameAlgebraFiberSpace_ra07c31_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance frameAlgebraDualAdd_ra07c31_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameAlgebraDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameAlgebraSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameAlgebraSectionSpace_ra07c31_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance frameAlgebraSectionGroup (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (frameAlgebraSectionNormed p).toAddCommGroup
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform stability of the finite primitive inverse when its coefficient
functionals, cutoffs and phase covectors all vary independently. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance dataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance dataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance dataFiberComplete_ra07c31_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd
local instance dataDualSmul_ra07c31_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance dataFiberGroup : AddCommGroup TensorFiber := dataFiberNormed.toAddCommGroup

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundedPrimitiveAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform inverse and amplitude bounds from the fixed reference size and
positive coefficient margin. Inactive chart coefficients need not vary continuously. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance boundedAmplitudeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance boundedAmplitudeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance boundedAmplitudeDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedAmplitudeDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedAmplitudeGroup : AddCommGroup TensorFiber := boundedAmplitudeFiberNormed.toAddCommGroup

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryParam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit regular parametrizations of the actual coordinate circles.
The compact parameter interval covers the whole boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def circularVelocity (r t : ℝ) : CurvePlane := (-r*Real.sin t,r*Real.cos t)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FinitePrimitiveOperatorTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform operator tolerance on bounded finite coefficient data. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance operatorToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three linear moment equations for a positive loop density. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LoopDensity

def augment (v : Plane) : Moments := ![1, v 0, v 1]

def background (p : ℝ → Plane) : Moments := ∫ t in 0..1, augment (p t)

def column (p : ℝ → Plane) (ψ : ℝ → ℝ) : Moments :=
  ∫ t in 0..1, ψ t • augment (p t)

def momentMap (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) : Moments →L[ℝ] Moments :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (column p (ψ i))

def weights (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) (ε : ℝ) (c : Plane) : Moments :=
  (momentMap p ψ).inverse (augment c - ε • background p)

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three circle directions strictly surrounding any radial target in the open disk. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.LoopDensity

def triangle (e : Plane) : Fin 3 → Plane :=
  ![e, ![-e 0 / 2 - Real.sqrt 3 / 2 * e 1, -e 1 / 2 + Real.sqrt 3 / 2 * e 0],
    ![-e 0 / 2 + Real.sqrt 3 / 2 * e 1, -e 1 / 2 - Real.sqrt 3 / 2 * e 0]]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_InteriorVelocityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interior oscillatory path covers the whole velocity circle. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

def interiorPath (A h t : ℝ) : Plane :=
  ![Real.cos (h + A * Real.cos (2 * Real.pi * t)),
    Real.sin (h + A * Real.cos (2 * Real.pi * t))]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular derivative contributes only to the complementary normal component. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def direction (e₁ e₂ : Vec) (α : ℝ) : Vec := Real.cos α • e₁ + Real.sin α • e₂
def angularDirection (e₁ e₂ : Vec) (α : ℝ) : Vec := -Real.sin α • e₁ + Real.cos α • e₂

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_LoopDensityArcTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nondegenerate three-point barycenter inside a symmetric circular arc. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.LoopDensity

def arcTriangle (q s : ℝ) : Fin 3 → Plane := ![![1, 0], ![q, s], ![q, -s]]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five leading profiles depend smoothly on the second jet, its first
transverse derivative, and the periodic parameter. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet}

abbrev LeadingProfileInput := (LowJet × ℝ) × LowJet

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveDataC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First derivatives of finite primitive data are bounded componentwise. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance finiteDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance finiteDataDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance finiteDataDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inactive primitive entries may be replaced before estimating the
finite operator; their cutoff is exactly zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance maskFiberNormed : NormedAddCommGroup TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocitySpatialDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spatial differentiation of the actual circular velocity, separating
all dependence on the angular derivative from the bounded remainder. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialError (Q : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (α : E → ℝ) (x v : E) : Vec :=
  fderiv ℝ Q x v + (fderiv ℝ R x v) • direction (e₁ x) (e₂ x) (α x) +
    R x • (Real.cos (α x) • fderiv ℝ e₁ x v + Real.sin (α x) • fderiv ℝ e₂ x v)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end


