-- Prove2me | Definitions.Def_OAIQ249SI002
-- name    : OAIQ249SI002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T19:54:48.785838+00:00
-- url     : https://prove2.me/theorems/4691181d-9be7-40b5-a189-f44cf37ea3e6
-- title:
--   Definitions bundle OAIQ249SI002 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 282 declarations of OpenAI's Lean: 199 definitions, 9 inductive types or structures, 8 instances, 64 theorems and 2 other declarations. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CompactCurveArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CompactCurveArc.closedSubarc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CompactCurveArc.openSubarc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ConsecutiveVertices`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CurveEdgeWitness`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CurveEdgeWitness.leftPoint`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CurveEdgeWitness.param`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CurveEdgeWitness.path`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CurveEdgeWitness.rightPoint`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FiniteRegularPath`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FrameTarget`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge.Plane`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge.Vec`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RealizedCurveWalk`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCover`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCover.cast`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCover.ofArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCover.subpath`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCover.trans`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothArcTail`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothCompactArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothCompactArc.path`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.UnorderedSurfacePairs`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainPlaneDualNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampChainPlaneDualSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.centeredSmoothStep`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.correctionInputOrder`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.correctionOrder`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.curveIncidenceGraph`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.degree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.endpointSignModel`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataCovectorNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataCovectorSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.flatFirstNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.flatFirstSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalQuadraticSupport`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.graphProjection`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementError`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridIncrementSize`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridInteractionCount` and 168 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_GradientBounds`, `Immersion_ClosedSurface_JetBounds`, `Immersion_ClosedSurface_MeanError`, `Immersion_ClosedSurface_ModeBounds`, `Immersion_ClosedSurface_QuadraticError`, `Immersion_ClosedSurface_QuadraticMean`, `Immersion_ClosedSurface_QuadraticSupport`, `Immersion_ClosedSurface_RootMean`, `Immersion_ClosedSurface_WeightedBounds`, `SurfaceImmersion_Atlas_CoordinateGauss`, `SurfaceImmersion_Atlas_CoordinateSardThree`, `SurfaceImmersion_Atlas_FixedChartNonlinearSolver`, `SurfaceImmersion_Atlas_GenericCoordinateLevels`, `SurfaceImmersion_Atlas_GridIncrementEnvelope`, `SurfaceImmersion_Atlas_LinearPhaseCutoffBounds`, `SurfaceImmersion_Atlas_LowJetCoordinateChange`, `SurfaceImmersion_Atlas_MatchedSubsetChart`, `SurfaceImmersion_Atlas_QuadraticCutoffBounds`, `SurfaceImmersion_Atlas_QuadraticJetCutoff`, `SurfaceImmersion_Atlas_ShrinkingWeightContinuity`, `SurfaceImmersion_Atlas_TensorChartBounds`, `SurfaceImmersion_Atlas_TensorFiberCoordinates`, `SurfaceImmersion_Atlas_UniformLinearPhaseBudgets`, `SurfaceImmersion_Atlas_WeightedComplexMixedJets`, `SurfaceImmersion_Atlas_WeightedInverseJacobian`, `SurfaceImmersion_Atlas_WeightedModulatedJets`, `SurfaceImmersion_Atlas_ZeroSliceLineChart`, `SurfaceImmersion_Correction_AdaptiveCorrectionSequence`, `SurfaceImmersion_Correction_AdaptiveCorrectionStep`, `SurfaceImmersion_Correction_CenteredSmoothStep`, `SurfaceImmersion_Correction_FiniteMetricPolynomial`, `SurfaceImmersion_Correction_GridMeanBudgets`, `SurfaceImmersion_Correction_JetPolynomialVector`, `SurfaceImmersion_Correction_NormalizedJetCorrection`, `SurfaceImmersion_Correction_PairModelCoordinates`, `SurfaceImmersion_Correction_PeriodicCorrector`, `SurfaceImmersion_Correction_PolynomialAmplitudeBounds`, `SurfaceImmersion_Correction_PolynomialBudgetMeanFamily`, `SurfaceImmersion_Correction_PolynomialDualBounds`, `SurfaceImmersion_Correction_PolynomialFiniteAssembly`, `SurfaceImmersion_Correction_PolynomialFreeNormal`, `SurfaceImmersion_Correction_PolynomialInverseChartJets`, `SurfaceImmersion_Correction_PolynomialLinearMeanBudgets`, `SurfaceImmersion_Correction_PolynomialLocalAmplitude`, `SurfaceImmersion_Correction_PolynomialLocalMeanProfile`, `SurfaceImmersion_Correction_PolynomialMeanTransport`, `SurfaceImmersion_Correction_PolynomialMetricForcedBudgets`, `SurfaceImmersion_Correction_PolynomialMetricFreeBudgets`, `SurfaceImmersion_Correction_PolynomialNormalBounds`, `SurfaceImmersion_Correction_PolynomialPerpBounds`, `SurfaceImmersion_Correction_PolynomialPhaseFrame`, `SurfaceImmersion_Correction_PolynomialQuadraticTargetBudget`, `SurfaceImmersion_Correction_PolynomialRealReconstruction`, `SurfaceImmersion_Correction_PolynomialRootBounds`, `SurfaceImmersion_Correction_PolynomialRotationFrame`, `SurfaceImmersion_Correction_PolynomialSmoothingProfiles`, `SurfaceImmersion_Correction_PolynomialTensorMean`, `SurfaceImmersion_Correction_PositivePolynomialBounds`, `SurfaceImmersion_Correction_PreparedCorrection`, `SurfaceImmersion_Correction_SmoothZeroFactor`, `SurfaceImmersion_Correction_SmoothedInputAdmissibility`, `SurfaceImmersion_Correction_SmoothedInputCloseness`, `SurfaceImmersion_Correction_SmoothingMoments`, `SurfaceImmersion_Correction_TensorFiniteMean`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_TensorMeanIteration`, `SurfaceImmersion_Correction_TensorSmoothing`, `SurfaceImmersion_Correction_TensorSmoothingSymmetry`, `SurfaceImmersion_Correction_UniformFreeModeConstants`, `SurfaceImmersion_Correction_UniformMetricMean`, `SurfaceImmersion_Correction_UniformNormalizedMean`, `SurfaceImmersion_Geometry_CompactAnsatzAsymptotics`, `SurfaceImmersion_Geometry_CompactRegularParameters`, `SurfaceImmersion_Geometry_CorrectedNormalSeed`, `SurfaceImmersion_Geometry_CurveEdgeParametrization`, `SurfaceImmersion_Geometry_CurveEdgePaths`, `SurfaceImmersion_Geometry_CurveEdgeWitness`, `SurfaceImmersion_Geometry_CurveIncidenceGraph`, `SurfaceImmersion_Geometry_EmbeddedCurveGraphPath`, `SurfaceImmersion_Geometry_EmbeddedOpenSubset`, `SurfaceImmersion_Geometry_FiniteDisjointAdjustment`, `SurfaceImmersion_Geometry_FiniteIntervalChopping`, `SurfaceImmersion_Geometry_FiniteParametrix`, `SurfaceImmersion_Geometry_FiniteParametrixLinearity`, `SurfaceImmersion_Geometry_FlatFirstHolder`, `SurfaceImmersion_Geometry_IndependentRadiusProjections`, `SurfaceImmersion_Geometry_InputSize`, `SurfaceImmersion_Geometry_MatchedZeroLineData`, `SurfaceImmersion_Geometry_ModulatedJetDataBounds`, `SurfaceImmersion_Geometry_OpenIntervalExtension`, `SurfaceImmersion_Geometry_ParameterIntegralDerivatives`, `SurfaceImmersion_Geometry_PerturbedForcedSize`, `SurfaceImmersion_Geometry_PositiveDensityPullback`, `SurfaceImmersion_Geometry_PreferredNormal`, `SurfaceImmersion_Geometry_ProjectionDirections`, `SurfaceImmersion_Geometry_PublishedInputs`, `SurfaceImmersion_Geometry_QuadraticOverlapSupports`, `SurfaceImmersion_Geometry_RegularZeroStability`, `SurfaceImmersion_Geometry_SafeRadialNormalization`, `SurfaceImmersion_Geometry_SphericalJets`, `SurfaceImmersion_Geometry_SphericalLift`, `SurfaceImmersion_Geometry_SphericalPointFlattening`, `SurfaceImmersion_Geometry_SupportJetEquality`, `SurfaceImmersion_Geometry_SurfaceBlendGerms`, `SurfaceImmersion_Geometry_TensorBundleInverse`, `SurfaceImmersion_Geometry_TransverseSmallFunction`, `SurfaceImmersion_Geometry_UnorderedPairCovering`, `SurfaceImmersion_Geometry_UnorderedPairMap`, `SurfaceImmersion_Primitive_CrossingComponents`, `SurfaceImmersion_Primitive_CrossingInvariantThreshold`, `SurfaceImmersion_Primitive_CrossingProjectionBounds`, `SurfaceImmersion_Primitive_LocalPeriodicCalculus`, `SurfaceImmersion_Primitive_LocalPeriodicGlobalization`, `SurfaceImmersion_Primitive_LoopDensityBumpSelection`, `SurfaceImmersion_Primitive_LoopDensityLinear`, `SurfaceImmersion_Primitive_LoopDensityTriangle`, `SurfaceImmersion_Primitive_PeriodicCalculus`, `SurfaceImmersion_Primitive_PeriodicLocalizedBump`, `SurfaceImmersion_Primitive_PrimitiveAmplitudeChain`, `SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds`, `SurfaceImmersion_Primitive_PrimitiveDataC1`, `SurfaceImmersion_Primitive_PrimitiveFiberInverse`, `SurfaceImmersion_Primitive_PrimitiveOperatorStability`, `SurfaceImmersion_Primitive_PrimitiveSlowScales`, `SurfaceImmersion_Primitive_SlowPeriodicDerivative`, `SurfaceImmersion_Whitney_CompactCurveArc`, `SurfaceImmersion_Whitney_EndpointSignModel`, `SurfaceImmersion_Whitney_LoopDensityArcTriangle`, `SurfaceImmersion_Whitney_RegularArcPaths`, `SurfaceImmersion_Whitney_RegularPathCover`, `SurfaceImmersion_Whitney_RegularPathCoverConcat`, `SurfaceImmersion_Whitney_RelativeImmersionHPrinciple`, `SurfaceImmersion_Whitney_SmoothArcJoin`, `SurfaceImmersion_Whitney_SmoothArcTail`, `SurfaceImmersion_Whitney_SmoothCompactArc`, `SurfaceImmersion_Whitney_UnorderedSurfacePairs`, `ToMathlib_Algebra_Ring_Periodic`, `ToMathlib_Analysis_Calculus`, `ToMathlib_Analysis_CutOff`, `ToMathlib_ExistsOfConvex`, `ToMathlib_MeasureTheory_BorelSpace`, `ToMathlib_Topology_Misc`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI003`, `OAIQ249SI004`, `OAIQ249SI005`, `OAIQ249SI006` and `OAIQ249SI007`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_quadratic_family_sum_le`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_finite_regular_path`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_isometric_immersion_conditional`, `OAI_ClosedSurfaceR4_FiniteParametrix_boundProfile_polynomial`, `OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput`, `OAI_ClosedSurfaceR4_SmallModes_errorConstant_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_forcedModeBudget_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_freeModeBudget_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_freeModeConstant_polynomial` and `OAI_ClosedSurfaceR4_SmallModes_initialConstant_polynomial`; the proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_quadratic_family_sum_le`, `OAI_ClosedSurfaceR4_FiniteParametrix_boundProfile_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_errorConstant_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_forcedModeBudget_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_freeModeBudget_polynomial`, `OAI_ClosedSurfaceR4_SmallModes_freeModeConstant_polynomial` and `OAI_ClosedSurfaceR4_SmallModes_initialConstant_polynomial`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.AddTorsor.Coord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.AffineSpace.Matrix
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Germ
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma sum_choose_real (j : ℕ) : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
  simpa only [one_pow, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using (add_pow (1 : ℝ) 1 j).symm


lemma weighted_binomial_bound {s C D : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (j : ℕ) (a b : ℕ → ℝ) (_ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (haB : ∀ i ≤ j, s ^ i * a i ≤ C) (hbB : ∀ i ≤ j, s ^ i * b i ≤ D) :
    s ^ j * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i)) ≤
      2 ^ j * C * D := by
  calc
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (s ^ i * a i) *
        (s ^ (j - i) * b (j - i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : s ^ j = s ^ i * s ^ (j - i) := by rw [← pow_add, Nat.add_sub_of_le hij]
      rw [he]
      ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hh := mul_le_mul (haB i hij) (hbB (j - i) (Nat.sub_le j i))
        (mul_nonneg (pow_nonneg hs _) (hb _)) hC
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (j.choose i))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, sum_choose_real]




lemma compact_coefficient_bound {V K : Set F} (hV : UniqueDiffOn ℝ V) (hK : IsCompact K)
    (hKV : K ⊆ V) {g : F → G} (hg : ContDiffOn ℝ ∞ g V) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ j ≤ m, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ j g V y‖ ≤ D := by
  have hb (j : ℕ) : ∃ C, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ j g V y‖ ≤ C :=
    hK.exists_bound_of_continuousOn ((hg.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) hV).mono hKV)
  induction m with
  | zero =>
    obtain ⟨C, hC⟩ := hb 0
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro j hj y hy
    have : j = 0 := by omega
    subst j
    exact (hC y hy).trans (le_max_right _ _)
  | succ m ih =>
    obtain ⟨D, hD, hd⟩ := ih
    obtain ⟨C, hC⟩ := hb (m + 1)
    refine ⟨max D C, hD.trans (le_max_left _ _), ?_⟩
    intro j hj y hy
    by_cases hjm : j ≤ m
    · exact (hd j hjm y hy).trans (le_max_left _ _)
    · have : j = m + 1 := by omega
      subst j
      exact (hC y hy).trans (le_max_right _ _)

lemma iteratedFDerivWithin_pi_smooth {ι : Type*} [Fintype ι] {U : Set E}
    (hU : UniqueDiffOn ℝ U) {f : ι → E → F} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    {x : E} (hx : x ∈ U) (j : ℕ) :
    iteratedFDerivWithin ℝ j (fun x i => f i x) U x =
      ContinuousMultilinearMap.pi (fun i => iteratedFDerivWithin ℝ j (f i) U x) := by
  have hp : ContDiffOn ℝ ∞ (fun x i => f i x) U := contDiffOn_pi.2 hf
  ext v i
  have he := (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).iteratedFDerivWithin_comp_left
    (hp.contDiffWithinAt hx) hU hx (i := j)
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    ContinuousMultilinearMap.pi_apply] using congrArg (fun T => T v) he.symm

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



def reducedConstant (m : ℕ) (K : ℝ) : ℝ :=
  (1 + 2 ^ (m + 1) * K) * (1 + 2 ^ m * K)


def errorConstant (m : ℕ) (K : ℝ) : ℝ :=
  2 * reducedConstant m K * (1 + 2 ^ (m + 1) * K)

def targetConstant (n m : ℕ) (K : ℝ) : ℝ := 1 + ((2 * n + 1 : ℕ) : ℝ) * 2 ^ m * K


def fullErrorConstant (n m : ℕ) (K : ℝ) : ℝ :=
  2 * reducedConstant m K * targetConstant n (m + 1) K


def amplitudeConstant (n m : ℕ) (K : ℝ) : ℝ :=
  (2 ^ (m + 1) * K + 2 ^ m * K * (1 + 2 ^ (m + 1) * K)) * targetConstant n (m + 1) K

def initialConstant (n m : ℕ) (K : ℝ) : ℝ := 1 + 2 ^ m * K + amplitudeConstant n m K

def freeModeConstant (n m : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => amplitudeConstant n m K
  | q + 1 => freeModeConstant n m K q +
      initialConstant n m K * fullErrorConstant n (m + 1 + q) K ^ (q + 1)

end Quantitative
end ClosedSurfaceR4.SmallModes

end

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

abbrev Base := ℝ × ℝ

def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * I)

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GradientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

def gradientErrorConstant (n m : ℕ) (K : ℝ) (q : ℕ) : ℝ :=
  1 + freeModeConstant n (m + 1) K q + freeModeConstant n m K q

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates




namespace LowJet
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_cdiv {a b : E → ℂ} {p : E}
    (ha : ContDiffAt ℝ ∞ a p) (hb : ContDiffAt ℝ ∞ b p) (hne : b p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => a q / b q) p := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.fun_inv hne)

abbrev CoeffIndex (n : ℕ) := Fin 8 ⊕ (Fin 5 × Fin n)

end LowJet

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.WeightedEstimates



def halfReCLM : ℂ →L[ℝ] ℝ := (2 : ℝ)⁻¹ • Complex.reCLM

lemma halfReCLM_apply (z : ℂ) : halfReCLM z = z.re / 2 := by
  simp [halfReCLM, div_eq_mul_inv, mul_comm]

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates



def meanErrorConstant (n m : ℕ) (K : ℝ) (q : ℕ) : ℝ :=
  (n : ℝ) * 2 ^ m * gradientErrorConstant n m K q * (2 + gradientErrorConstant n m K q)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RootMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def positivePair : Set (Fin 2 → ℝ) := {p | 0 < p 0 ∧ 0 < p 1}
def rootDifferenceCoefficient (p : Fin 2 → ℝ) : ℝ :=
  (Real.sqrt (p 0) + Real.sqrt (p 1))⁻¹

end ClosedSurfaceR4.RootMean

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def phaseAmplitude (ψ u : E → ℝ) : E → ℝ := fun p => ψ p * Real.sqrt (u p)

lemma contDiffOn_phaseAmplitude {U : Set E} {ψ u : E → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ U) (hu : ContDiffOn ℝ ∞ u U)
    (hpos : ∀ p ∈ U, 0 < u p) : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) U :=
  hψ.mul (hu.sqrt (fun p hp => ne_of_gt (hpos p hp)))



end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates



abbrev QuadraticLabel (ι : Type*) := ι ⊕ (Σ i : ι, {j : ι // j ≠ i} × Bool)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate Gauss identity, proved from Euclidean derivatives and the
explicit normal projection.  Its right side depends only on the metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

/-- Pairing of tangent covectors by the inverse first fundamental form. -/
def inverseMetricPair (E F G a b c d : ℝ) : ℝ :=
  (G*a*c-F*(a*d+b*c)+E*b*d)/(E*G-F^2)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Whitney immersion and Sard regular-value statements for surfaces

The compact surface specialization of Whitney's immersion theorem and
the equal-dimensional surface case of Sard's theorem provide the
initial immersion and the regular parameters of the construction.
-/

noncomputable section

namespace ClosedSurfaceR4.PublishedInputs

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

/-- Whitney, *The Singularities of a Smooth n-Manifold in (2n-1)-Space*,
Ann. Math. 45 (1944), Theorem 8, p.274, specialized to compact surfaces:
existence of a C1 immersion into Euclidean three-space. -/
def WhitneySurfaceInput (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace Plane M] [IsManifold 𝓘(ℝ, Plane) ∞ M] : Prop :=
  ∃ f : M → ThreeSpace, ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ThreeSpace) 1 f ∧
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ThreeSpace) f x)

/-- Critical values of a map between two-dimensional coordinate spaces. -/
def criticalValues (f : Plane → Plane) : Set Plane :=
  f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}

/-- Sard, *The measure of the critical values of differentiable maps*,
Bull. AMS 48 (1942), Theorem 4.1, p.885: the smooth equal-dimensional
surface case in coordinates. This is the sole critical-value input needed
for the manuscript's countable coordinate charts. -/
def SardSurfaceInput : Prop :=
  ∀ f : Plane → Plane, ContDiff ℝ ∞ f → volume (criticalValues f) = 0

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateSardThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact three-dimensional coordinate Sard and regular-fiber facts
needed for generic projections of a surface from four-space to three-space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PublishedInputs

abbrev SurfaceDirectionParameters := (Fin 2 → ℝ) × ℝ

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialNormalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the Gram determinant, tangential
coefficients and normal projection. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dotBudget (m : ℕ) (C : ℝ) : ℝ := 4*(2^m*C*C)
def quadraticBudget (m : ℕ) (C : ℝ) : ℝ := 1+2*(2^m*dotBudget m C*dotBudget m C)
def inverseGramBudget (m : ℕ) (C K : ℝ) : ℝ :=
  (m.factorial : ℝ)^2*K^(m+1)*(quadraticBudget m C)^m
def liftBudget (m : ℕ) (C K : ℝ) : ℝ := 2^m*quadraticBudget m C*inverseGramBudget m C K
def normalBudget (m : ℕ) (C K : ℝ) : ℝ := C+2*(2^m*liftBudget m C K*C)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerpBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial derivative bounds for the perpendicular product and its
unit normalization used by the free mode. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def crossBudget (m : ℕ) (C : ℝ) := 2*(2^m*C*C)
def minorTermBudget (m : ℕ) (C : ℝ) := 2^m*C*crossBudget m C
def perpBudget (m : ℕ) (C : ℝ) := 3*minorTermBudget m C

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFreeNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the rational and square-root estimates to the actual free normal
of an immersed surface, with explicit inverse geometric margins. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def freeNormalInputBudget (m : ℕ) (C K : ℝ) : ℝ := 1+C+normalBudget m C K

def freeNormalBudget (m : ℕ) (D C K : ℝ) : ℝ :=
  let A := freeNormalInputBudget m C K
  2^m*((m.factorial : ℝ)*D*(K^2)^(m+1)*(1+dotBudget m (perpBudget m A))^m)*perpBudget m A

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialDualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial estimates for the three vector columns of reconstruction. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangentDualBudget (m : ℕ) (C K : ℝ) :=
  2*(2^m*(2^m*dotBudget m C*inverseGramBudget m C K)*C)

def normalDualBudget (m : ℕ) (C K : ℝ) :=
  2^m*((m.factorial : ℝ)^2*K^(m+1)*(1+dotBudget m C)^m)*C

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRealReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common polynomial bound for every real reconstruction coefficient. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalRatioBudget (m : ℕ) (C K : ℝ) :=
  2^m*dotBudget m C*((m.factorial : ℝ)^2*K^(m+1)*(1+dotBudget m C)^m)

def reconstructionBudget (m : ℕ) (C K : ℝ) :=
  1+liftBudget m C K+normalBudget m C K+tangentDualBudget m C K+
    normalDualBudget m (normalBudget m C K) K+normalRatioBudget m (normalBudget m C K) K

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

/-- An explicit polynomial upper bound on the positive half-line. -/
def HasPolynomialBound (f : ℝ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → 0 ≤ f x ∧ f x ≤ C*x^d

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the inverse Jacobian field in dimension two. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def inverseJacobianBudget (m : ℕ) (C K : ℝ) : ℝ :=
  2^m*((m.factorial : ℝ)^2*K^(m+1)*(1+2^(m+1)*C^2)^m)*(2*C)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialInverseChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative derivatives of an inverse chart from its actual inverse
Jacobian field. The finite-order budget is polynomial in the field's jets. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def inverseChartJetBudget : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, B => inverseChartJetBudget n B +
      (n.factorial : ℝ)*B*(inverseChartJetBudget n B)^n

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite moment cancellation for smoothing kernels on the coordinate plane.
Distinct positive dilations give a kernel of mass one whose required low
moments vanish. This is the algebraic step in finite-order smoothing. -/
noncomputable section
open scoped BigOperators Matrix

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory

/-- The transpose Vandermonde system prescribes all moments through order `r`. -/
theorem exists_dilation_weights (r : ℕ) (b : Fin (r + 1) → ℝ)
    (hb : Function.Injective b) :
    ∃ c : Fin (r + 1) → ℝ, ∀ j : Fin (r + 1),
      ∑ i, c i * b i ^ j.val = if j = 0 then 1 else 0 := by
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := (Matrix.vandermonde b).transpose
  have hdet : A.det ≠ 0 := by
    simpa only [A, Matrix.det_transpose] using Matrix.det_vandermonde_ne_zero_iff.mpr hb
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) (Pi.single 0 1)
  refine ⟨c, ?_⟩
  intro j
  have h := congrFun hc j
  simpa only [A, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.vandermonde_apply, Pi.single_apply, mul_comm] using h

/-- Positive integral dilation factors suffice, so each dilation preserves
compact support and smoothness. -/
theorem exists_positive_dilation_weights (r : ℕ) :
    ∃ c : Fin (r + 1) → ℝ, ∀ j : Fin (r + 1),
      ∑ i, c i * ((i.val + 1 : ℕ) : ℝ) ^ j.val = if j = 0 then 1 else 0 := by
  apply exists_dilation_weights r
  intro i j hij
  apply Fin.ext
  exact Nat.add_right_cancel (Nat.cast_injective hij)

def degree (α : Fin 2 → ℕ) : ℕ := ∑ i, α i

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing on the actual covariant two-tensor bundle of the surface. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance tensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance coordinateDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance
local instance coordinateDualSmul : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encode global tensor sections by their finite atlas coordinates. This
retains the compact-surface partition identity while permitting the finite
mean iteration to run on a normed vector-valued function space. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance meanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance meanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

end ClosedSurfaceR4.FiniteOrderSmoothing

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance symmetryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance symmetryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def tensorChartBudget (m : ℕ) (J D : ℝ) : ℝ :=
  4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * J ^ m) * D) * D)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite parametrix improvement with derivative loss. This is a finite
algebraic iteration; no bounded inverse on one Banach space is assumed. -/
noncomputable section

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def improve (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) : ℕ → E
  | 0 => z
  | j + 1 => improve A S b z j - S (A (improve A S b z j) - b)

def residual (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (b : F) (z : E) (j : ℕ) : F :=
  A (improve A S b z j) - b

def defect (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) : F →ₗ[ℝ] F :=
  A.comp S - LinearMap.id

def boundProfile (L : ℕ) (K C : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => C m
  | j + 1, m => K m * boundProfile L K C j (m + L)

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation and normalized integration on the period circle. -/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma periodic_deriv {f : ℝ → E} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun t => f (t + 1)) = f := funext hp
  have hd := congrArg (fun g : ℝ → E => deriv g x) he
  simpa only [deriv_comp_add_const] using hd

end ClosedSurfaceR4.PeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SlowPeriodicDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slow differentiation commutes with the periodic mean. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def slowDerivative (F : A × ℝ → E) (v : A) (z : A × ℝ) : E :=
  fderiv ℝ F z (v, 0)

lemma contDiff_slowDerivative {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (v : A) :
    ContDiff ℝ ∞ (slowDerivative F v) :=
  (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end ClosedSurfaceR4.SmoothPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma smooth_slice [NormedSpace ℝ E] {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) {p : P} (hp : p ∈ S) :
    ContDiff ℝ ∞ (fun t => F (p, t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp t
    (contDiff_const.prodMk contDiff_id).contDiffAt

lemma slow_smooth {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) (v : P) :
    ContDiffOn ℝ ∞ (slowDerivative F v) (S ×ˢ Set.univ) :=
  (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const

lemma fderiv_slice {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) {p : P} (hp : p ∈ S) (v : P) (t : ℝ) :
    fderiv ℝ (fun q => F (q, t)) p v = slowDerivative F v (p, t) := by
  have hi : HasFDerivAt (fun q : P => (q, t)) (ContinuousLinearMap.inl ℝ P ℝ) p := by
    simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inl ℝ P ℝ).hasFDerivAt (x := p)).add_const (0, t)
  have hd := ((hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp p hi
  change fderiv ℝ (F ∘ fun q => (q, t)) p v = _
  rw [hd.fderiv]
  rfl

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedComplexMixedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-scale evaluation: the output is measured at the slow scale, while
only the explicit jet excess contributes short-scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

def slotLoss (i : Fin 4) (w : List (Fin 2)) : ℕ :=
  if i = 0 then w.length - 2 else w.length

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedModulatedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slow-scale bounds on the amplitudes of fast oscillatory jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

def jetConstant (P : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, r + 1 => (1 + 2 ^ m * P) * jetConstant P (m + 1) r

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetDataBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite-order budget for all demodulated jet slots. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

def amplitudeBudget (N m : ℕ) (B P : ℝ) : ℝ :=
  1 + B + ∑ r ∈ Finset.range (N + 1), jetConstant P m r

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteParametrixLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the finite homogeneous correction in its initial amplitude. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def homogeneousLM (A : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) : ℕ → E →ₗ[ℝ] E
  | 0 => LinearMap.id
  | j + 1 => (LinearMap.id - S.comp A).comp (homogeneousLM A S j)

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformFreeModeConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit free-mode constants, independent of both short scales and
of the perturbation size. These constants are used before selecting scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

def freeModeBudget (n L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range q, initialConstant n m (B m) *
    FiniteParametrix.boundProfile (L + 1)
      (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
      (fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
      i (m + (L + 1))) + amplitudeConstant n m (B m)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CorrectedNormalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit size and difference budgets for the actual corrected normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def correctedSeedBudget (L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) (N : ℝ) : ℝ :=
  (1 + freeModeBudget 4 L B D q m) *
    (Real.sqrt 2 * 2 ^ (m + (q + 1) * (L + 1)) * N)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedForcedSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite forced correction has a scale-independent amplitude
budget. Only the finite number of required input derivatives grows. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

def forcedModeBudget (n L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) : ℝ :=
  initialConstant n m (B m) +
    ∑ i ∈ Finset.range q, initialConstant n m (B m) *
      FiniteParametrix.boundProfile (L + 1)
        (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
        (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
        i (m + (L + 1))

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformMetricMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric mean budget is fixed before either scale is selected. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ}

def freeMeanBudget (n L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) : ℝ :=
  let A := freeModeBudget n L B D q (m + 1)
  (n : ℝ) * 2 ^ m * ((1 + 2 * A) * (2 + 2 * A) + (1 + 2 * A))

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformNormalizedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit constants for the normalized geometric metric mean, independent
of its oscillation and amplitude scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def normalizedMeanBudget (L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) (N : ℝ) : ℝ :=
  freeMeanBudget 4 L B D q m *
    (Real.sqrt 2 * 2 ^ (m + 1 + (q + 1) * (L + 1)) * N) ^ 2

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportJetEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality on the closed support of a smooth cutoff determines every
jet there, including at its boundary. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedFDeriv_eq_on_tsupport {χ : E → ℝ} (hχ : Continuous χ)
    {U : Set E} (hU : IsOpen U) (hK : tsupport χ ⊆ U)
    {f g : E → F} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (he : EqOn f g (tsupport χ)) (m : ℕ) :
    EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) (tsupport χ) := by
  have hfc : ContinuousOn (iteratedFDeriv ℝ m f) U := by
    apply (hf.continuousOn_iteratedFDerivWithin (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen m hU hx).symm
  have hgc : ContinuousOn (iteratedFDeriv ℝ m g) U := by
    apply (hg.continuousOn_iteratedFDerivWithin (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen m hU hx).symm
  have ho : EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) (Function.support χ) := by
    intro x hx
    have hh : f =ᶠ[𝓝 x] g := by
      filter_upwards [hχ.isOpen_support.mem_nhds hx] with y hy
      exact he (subset_tsupport χ hy)
    exact (hh.iteratedFDeriv ℝ m).self_of_nhds
  exact ho.of_subset_closure (hfc.mono hK) (hgc.mono hK) subset_closure Subset.rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FixedChartNonlinearSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual nonlinear solvers on a fixed phase chart. Only its open domain is
restricted when the immersed map changes; all coordinate budgets stay fixed. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseGeometry

def fixedChartSolverBudget (J B : ℕ → ℝ) (D : ℝ) (m : ℕ) : ℝ :=
  1+B m+J (m+3)+2*(J 1)^2+2*D

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactRegularParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact-chart regular-value conditions are open as well as dense.
This permits independent radius parameters in a finite product. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

def compactRegularValues (f : Plane → Plane) (K : Set Plane) : Set Plane :=
  {y | ∀ x ∈ K, f x = y → Function.Surjective (fderiv ℝ f x)}

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IndependentRadiusProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pair and triple projections used for independently perturbed disk
radii are actual surjective bounded linear maps. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PublishedInputs
variable {ι : Type*} [DecidableEq ι]

def radiusPairProjection (i j : ι) : (ι → ℝ) →L[ℝ] Plane :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun a : Fin 2 => ContinuousLinearMap.proj (if a = 0 then i else j)))

omit [DecidableEq ι] in
@[simp] lemma radiusPairProjection_apply_zero (i j : ι) (t : ι → ℝ) :
    radiusPairProjection i j t 0 = t i := by
  simp [radiusPairProjection]

omit [DecidableEq ι] in
@[simp] lemma radiusPairProjection_apply_one (i j : ι) (t : ι → ℝ) :
    radiusPairProjection i j t 1 = t j := by
  simp [radiusPairProjection]

def radiusTripleProjection (i j k : ι) : (ι → ℝ) →L[ℝ] (Plane × ℝ) :=
  (radiusPairProjection i j).prod (ContinuousLinearMap.proj k)

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GenericCoordinateLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic common levels for finitely many radius functions in countably
many surface charts. This is the radius-selection step of the global preparation. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Countable α]

abbrev DistinctRadiusPairs (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}
abbrev DistinctRadiusTriples (ι : Type*) :=
  {p : (ι × ι) × ι // p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2}

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridIncrementEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial envelopes for the full free/forced grid increment. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes

def gridInteractionCount (n : ℝ) : ℝ := n+2*n^2

def gridIncrementSize (α β : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  α m x*H x+β m x*gridInteractionCount (H x)

def gridIncrementError (α β γ ζ T : ℕ → ℝ → ℝ) (D : ℕ → ℝ) (H : ℝ → ℝ)
    (m : ℕ) (x : ℝ) : ℝ :=
  ζ m x*H x+γ m x*gridInteractionCount (H x)+T m x+
    D m*(2*(α (m+1) x*H x)*(β (m+1) x*gridInteractionCount (H x))+
      (β (m+1) x*gridInteractionCount (H x))^2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPhaseFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial reconstruction and free-normal bounds for the selected
linear phase charts. The exponent is fixed before the map and its bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

def phaseFrameInputBudget (m : ℕ) (B : ℝ) : ℝ :=
  1+B*B^(m+2)+4*B^5+16*B^10

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseCutoffBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative transport of the actual supported cutoff to a linear
phase chart, including the inverse frequency factor. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseGeometry RealModes

def phaseCutoffBudget (m : ℕ) (C J W : ℝ) : ℝ := W*((m.factorial : ℝ)*C*J^m)

end ClosedSurfaceR4.JetPolynomial

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

/-- Slots of the two first and four ordered second coordinate derivatives. -/
def firstJetSlot : Fin 2 → Fin 7 := ![1,2]
def secondJetSlot : Fin 2 → Fin 2 → Fin 7 := ![![3,4],![5,6]]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two affine charts for the tangent directions of a surface, and the
kernel criterion for a linear projection along a graph direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def graphProjection (a : V) : V × ℝ →L[ℝ] V :=
  ContinuousLinearMap.fst ℝ V ℝ -
    (ContinuousLinearMap.snd ℝ V ℝ).smulRight a

@[simp] lemma graphProjection_apply (a : V) (x : V × ℝ) :
    graphProjection a x = x.1 - x.2 • a := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MatchedSubsetChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict a local homeomorphism to matched subsets, with their induced
topologies. The subsets themselves need not be open. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem matched_subset_chart (e : OpenPartialHomeomorph X Y)
    (S : Set X) (T : Set Y) (p : X) (hp : p ∈ e.source) (hpS : p ∈ S)
    (hmatch : ∀ x ∈ e.source, x ∈ S ↔ e x ∈ T) :
    ∃ c : OpenPartialHomeomorph S T,
      (⟨p,hpS⟩ : S) ∈ c.source ∧ c.source = ((↑) ⁻¹' e.source) ∧
      c.target = ((↑) ⁻¹' e.target) ∧
      (∀ x ∈ c.source, (c x).val = e x.val) ∧
      (∀ y ∈ c.target, (c.symm y).val = e.symm y.val) := by
  classical
  have hpT : e p ∈ T := (hmatch p hp).mp hpS
  have hback (y : T) (hy : y.val ∈ e.target) : e.symm y.val ∈ S := by
    apply (hmatch _ (e.map_target hy)).mpr
    rw [e.right_inv hy]
    exact y.property
  let F : S → T := fun x => if hx : x.val ∈ e.source then
      ⟨e x.val,(hmatch x.val hx).mp x.property⟩ else ⟨e p,hpT⟩
  let G : T → S := fun y => if hy : y.val ∈ e.target then
      ⟨e.symm y.val,hback y hy⟩ else ⟨p,hpS⟩
  have hF (x : S) (hx : x.val ∈ e.source) : (F x).val = e x.val := by simp [F,hx]
  have hG (y : T) (hy : y.val ∈ e.target) : (G y).val = e.symm y.val := by simp [G,hy]
  let c : OpenPartialHomeomorph S T := {
    toFun := F
    invFun := G
    source := (↑) ⁻¹' e.source
    target := (↑) ⁻¹' e.target
    map_source' := by
      intro x hx
      change (F x).val ∈ e.target
      rw [hF x hx]
      exact e.map_source hx
    map_target' := by
      intro y hy
      change (G y).val ∈ e.source
      rw [hG y hy]
      exact e.map_target hy
    left_inv' := by
      intro x hx
      apply Subtype.ext
      have hy : (F x).val ∈ e.target := by rw [hF x hx]; exact e.map_source hx
      rw [hG _ hy,hF x hx,e.left_inv hx]
    right_inv' := by
      intro y hy
      apply Subtype.ext
      have hx : (G y).val ∈ e.source := by rw [hG y hy]; exact e.map_target hy
      rw [hF _ hx,hG y hy,e.right_inv hy]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage continuous_subtype_val
    continuousOn_toFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      exact (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr hF
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      exact (e.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ hy => hy)).congr hG }
  exact ⟨c,hp,rfl,rfl,hF,hG⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The radial normal of a spherical surface immersion.  The identities are for
actual Fréchet derivatives and the orthogonal projection defining the second
fundamental form, not an abstract second-jet model.
-/

noncomputable section

open scoped ContDiff

namespace ClosedSurfaceR4.SphericalJets

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)

/-- The actual normal plane of the immersed tangent plane. -/
def normalSpace (F : Plane → Space) (x : Plane) : Submodule ℝ Space :=
  (LinearMap.range (fderiv ℝ F x).toLinearMap)ᗮ

/-- The Euclidean second fundamental form obtained by normal projection. -/
def secondForm (F : Plane → Space) (x v w : Plane) : Space :=
  (normalSpace F x).starProjection (fderiv ℝ (fderiv ℝ F) x v w)

/-- Removing the radial component gives the second fundamental form within
the unit sphere. -/
def sphericalSecondForm (F : Plane → Space) (x v w : Plane) : Space :=
  secondForm F x v w +
    (inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w)) • F x

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedJetCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second jets of radial normalization, for the finite-point flattening
of the starting spherical immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

/-- Radial normalization is kept as an actual map of Euclidean four-space. -/
def radialNormalize (x : Space) : Space := ‖x‖⁻¹ • x

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QuadraticJetCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local quadratic correction in the finite-point spherical preparation.
The cutoff leaves its prescribed second jet unchanged. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

def quadraticCorrection (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p x : Plane) : Space :=
  (- (1 / 2 : ℝ)) • B (x-p) (x-p)

def cutoffQuadratic (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane)
    (χ : ContDiffBump p) (x : Plane) : Space := χ x • quadraticCorrection B p x

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QuadraticCutoffBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scale bounds for the local quadratic corrections.  The fixed
cutoff operator makes the constants independent of the tensor and radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

local instance linearNormed : NormedAddCommGroup (Plane →L[ℝ] Space) := inferInstance
local instance linearSpace : NormedSpace ℝ (Plane →L[ℝ] Space) := inferInstance
abbrev SecondTensor := Plane →L[ℝ] Plane →L[ℝ] Space
local instance evalNormed : NormedAddCommGroup ((Plane →L[ℝ] Space) →L[ℝ] Space) := inferInstance
local instance evalSpace : NormedSpace ℝ ((Plane →L[ℝ] Space) →L[ℝ] Space) := inferInstance
local instance evTensorNormed : NormedAddCommGroup (SecondTensor →L[ℝ] (Plane →L[ℝ] Space)) := inferInstance
local instance evTensorSpace : NormedSpace ℝ (SecondTensor →L[ℝ] (Plane →L[ℝ] Space)) := inferInstance
local instance tensorNormed : NormedAddCommGroup SecondTensor := inferInstance
local instance tensorSpace : NormedSpace ℝ SecondTensor := inferInstance
local instance operatorNormed : NormedAddCommGroup (SecondTensor →L[ℝ] Space) := inferInstance
local instance operatorSpace : NormedSpace ℝ (SecondTensor →L[ℝ] Space) := inferInstance

def unitJetCutoff : ContDiffBump (0 : Plane) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

def quadraticCutoffOperator (x : Plane) : SecondTensor →L[ℝ] Space :=
  ((- (1/2 : ℝ)) * unitJetCutoff x) •
    ((ContinuousLinearMap.apply ℝ Space x).comp
      (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Space) x))

def scaledQuadraticCutoff (B : SecondTensor) (p : Plane) (r : ℝ) (x : Plane) : Space :=
  r^2 • cutoffQuadratic B 0 unitJetCutoff (r⁻¹ • (x-p))

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingWeightContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform convergence of the actual ratio cutoffs from smaller radii.
The upper clamp permits an ordinary product-neighborhood argument at the
original radius, including the boundary where numerator and denominator vanish. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

def shrinkingRadius (r0 r : ℝ) : ℝ := max 0 (min r0 r)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformLinearPhaseBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed numerical mean budgets for nearby immersions in a linear phase chart.
The chart, cut-off, coefficient form, and weighted two-jet profile are fixed
before the nearby immersion and slow scale are supplied. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes

/-- The numerical part of the local mean budgets, without the map or scale. -/
structure BudgetProfiles where
  inv : ℕ → ℝ
  chi : ℕ → ℝ
  psi : ℕ → ℝ
  forms : ℕ → ℝ
  pull : ℕ → ℝ
  normal : ℕ → ℝ
  mode : ℕ → ℝ
  inv_pos : ∀ m, 1 ≤ inv m
  chi_pos : ∀ m, 1 ≤ chi m
  psi_pos : ∀ m, 1 ≤ psi m
  forms_pos : ∀ m, 1 ≤ forms m
  pull_pos : ∀ m, 1 ≤ pull m
  normal_pos : ∀ m, 1 ≤ normal m
  mode_pos : ∀ m, 1 ≤ mode m

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ZeroSliceLineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero slice in a product is a copy of the line; this converts
submersion coordinates into charts on matched zero subsets. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Zero E]

def zeroSliceLineHomeomorph : {z : E × ℝ // z.1 = 0} ≃ₜ ℝ where
  toFun := fun z => z.val.2
  invFun := fun t => ⟨(0,t),rfl⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact z.property.symm
    · rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ParameterIntegralDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every parameter derivative commutes with a compact interval integral.
This supplies the weighted bounds for periodic means and primitives. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def partialIterated (n : ℕ) (F : P × ℝ → E) (z : P × ℝ) : P [×n]→L[ℝ] E :=
  iteratedFDeriv ℝ n (fun p => F (p, z.2)) z.1

end ClosedSurfaceR4.SmoothParameterIntegral

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticOverlapSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance overlapTargetsDualAdd_r0be074_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_r0be074_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
def globalQuadraticSupport {ι : Type*} (S : ι → Set M) : RealModes.QuadraticLabel ι → Set M
  | .inl a => S a
  | .inr ⟨a,b,_⟩ => S a ∩ S b

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean substitution on actual global tensor sections, represented
by redundant atlas coordinates. Every iterate stays in the representation
range, so no leading-identity premise on arbitrary plane fields is needed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance iterationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
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
open Set Manifold Bundle WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance finiteMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance finiteMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InputSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joint input norms for the adaptive correction iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputSizeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputSizeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance inputClosenessDualAdd_r0be074_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputClosenessDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothedInputAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-norm bootstrap assumptions imply the actual smoothed inputs
remain inside the fixed map and tensor neighborhoods. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance admissibilityDualAdd_r0be074_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance admissibilityDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PreparedCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometry and numerical budgets for the adaptive iteration. All the
fields below are constructed from the proved small-increment theorem. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance preparedDualAdd_r0be074_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance preparedDualSmul_r0be074_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
/-- Construction starts at order ten, as required by the scale estimates. -/
def correctionOrder (k : ℕ) : ℕ := k+10

def correctionInputOrder (k : ℕ) : ℕ := 40*(correctionOrder k+1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveCorrectionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single adaptive transition, with all admissibility conditions preserved. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveCorrectionSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the correction sequence, and unbounded growth of the
finite derivative order despite the absence of uniform high-order input bounds. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance instDecidable_solutions_1 (p : Prop) : Decidable p := Classical.propDecidable p
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularZeroStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform first-jet stability of regular zero sets on compact domains.
This allows the finite pair-patch construction to preserve earlier patches. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
local instance zeroJetNormed : NormedAddCommGroup (E →L[ℝ] F) := inferInstance

def regularZeroJets : Set (F × (E →L[ℝ] F)) :=
  {z | z.1 ≠ 0 ∨ Function.Surjective z.2}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FlatFirstHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic control on the rank-zero stratum. In dimensions three to
 two and four to three it makes the critical image Hausdorff-null. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance flatFirstNormed : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance flatFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalPointFlattening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spherical second-jet cancellation by a supported quadratic map. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

def sphericalSecondFormCLM (F : Plane → Space) (p : Plane) :
    Plane →L[ℝ] Plane →L[ℝ] Space :=
  (ContinuousLinearMap.compL ℝ Plane Space Space (normalSpace F p).starProjection).comp
      (fderiv ℝ (fderiv ℝ F) p) +
    ((ContinuousLinearMap.smulRightL ℝ Plane Space).flip (F p)).comp
      (((innerSL ℝ).restrictScalars ℝ).bilinearComp (fderiv ℝ F p) (fderiv ℝ F p))

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CenteredSmoothStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A centered flat step with strict separation of opposite parameters,
used to round a tangential return between two disjoint curve branches. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def centeredSmoothStep (t : ℝ) : ℝ := Real.smoothTransition ((t+1)/2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteMetricPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite polynomial metric algebra for the periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def vectorPolynomialValue (n : ℕ) (a : ℕ → E) (z : ℝ) : E :=
  ∑ i ∈ Finset.range (n + 1), z ^ i • a i

def metricPolynomial (n : ℕ) (a b : ℕ → E) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial (i + j) (inner ℝ (a i) (b j))

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRootBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit square-root and square-root-difference bounds from a reciprocal
positivity margin, without a compact-set derivative constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqrtBudget (m : ℕ) (D B : ℝ) : ℝ :=
  2^m*B*((m.factorial : ℝ)*D*B^(m+1)*B^m)

def rootDifferenceBudget (m : ℕ) (D B : ℝ) : ℝ :=
  2^m*((m.factorial : ℝ)^2*B^(m+1)*(1+2*sqrtBudget m D B)^m)

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAmplitudeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the supported square-root amplitudes of the
metric decomposition, including their difference estimate. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RootMean
open WeightedEstimates RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def phaseAmplitudeBudget (m : ℕ) (D B : ℝ) : ℝ :=
  1+2^m*B*sqrtBudget m D B+2^m*B*rootDifferenceBudget m D B

end ClosedSurfaceR4.RootMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial square-root amplitudes for the actual local metric data. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates

def coefficientBudget (m : ℕ) (B : ℝ) : ℝ := 2^m*B*(m.factorial : ℝ)*B^m

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLocalMeanProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local mean operator has explicit polynomial majorants in the
geometric profile and the current tensor norm. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates

def polynomialMeanProfile (p : ℕ → ℕ) (C G : ℕ → ℝ) (m : ℕ) (A : ℝ) : ℝ :=
  C m*(G m+max 1 A)^(p m)

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearMeanBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct every numerical mean budget in a selected linear phase
chart with explicit polynomial dependence on the geometry. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes PhaseGeometry WeightedEstimates

def linearMeanGeometryBudget (p : ℕ → ℕ) (A B P : ℕ → ℝ) (m : ℕ) : ℝ :=
  1+3*B m+16*(B m)^2+P m+A m*(B m)^(p m)

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridMeanBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual grid mean budgets in the inverse grid scale. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes JetPolynomial

def gridMeanBudget (p : ℕ → ℕ) (A L : ℕ → ℝ) (B : ℕ → ℝ → ℝ)
    (m : ℕ) (x : ℝ) : ℝ :=
  linearMeanGeometryBudget p A (fun j => B j x)
    (fun j => 1+phaseCutoffBudget j (L j*x^(6*j)) (B j x) 1) m

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PeriodicCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The two components of the finite periodic corrector: the explicit solve in
span(Y,C), and integration of the covariance correction in its orthogonal
complement.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector

open PeriodicCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def gramDet (Y C : E) : ℝ :=
  inner ℝ Y Y * inner ℝ C C - (inner ℝ Y C) ^ 2

/-- The vector in span(Y,C) with prescribed pairings with Y and C. -/
def spanSolve (Y C : E) : (ℝ × ℝ) →L[ℝ] E :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a =>
      ((inner ℝ C C * a.1 - inner ℝ Y C * a.2) / gramDet Y C) • Y +
      ((inner ℝ Y Y * a.2 - inner ℝ Y C * a.1) / gramDet Y C) • C
    map_add' := by intros; dsimp; module
    map_smul' := by intros; dsimp; module }

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

abbrev R4 := EuclideanSpace ℝ (Fin 4)
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothZeroFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact smooth division by a real coordinate vanishing at one point. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def smoothZeroFactor (f : ℝ → V) (p t : ℝ) : V :=
  ∫ s in (0:ℝ)..1, deriv f (p+s*(t-p))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth joining at a common germ, with regularity and injectivity
retained on the two ordered pieces of the parameter interval. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

def joinedCurve (a : ℝ) (γ δ : ℝ → M) (t : ℝ) : M := if t ≤ a then γ t else δ t

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCompactArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact regular embedded smooth arcs, and the actual joining operation
for arcs meeting through an oriented smooth parameter germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (N : Type*) [TopologicalSpace N] [ChartedSpace H N]

structure SmoothCompactArc where
  curve : ℝ → N
  start : ℝ
  finish : ℝ
  start_lt_finish : start < finish
  domain : Set ℝ
  domain_open : IsOpen domain
  interval_subset : Icc start finish ⊆ domain
  smooth : ContMDiffOn 𝓘(ℝ) I ∞ curve domain
  regular : ∀ t ∈ domain, Function.Injective (mfderiv 𝓘(ℝ) I curve t)
  injective : (Icc start finish).InjOn curve

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceBlendGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior germs of the actual chart blend and an explicit time cutoff. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

def timeCutoff (l r : ℝ) (t : ℝ) : ℝ := Real.smoothTransition ((t-l)/(r-l))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MatchedZeroLineData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the coordinate formulas for the real chart on a matched zero set. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Zero E]

theorem matched_zero_subset_line_chart_data (e : OpenPartialHomeomorph X (E × ℝ))
    (S : Set X) (p : X) (hp : p ∈ e.source) (hpS : p ∈ S)
    (hmatch : ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = 0) :
    ∃ c : OpenPartialHomeomorph S ℝ,
      (⟨p,hpS⟩ : S) ∈ c.source ∧
      c.source = ((↑) ⁻¹' e.source) ∧
      c.target = {t | (0,t) ∈ e.target} ∧
      (∀ x ∈ c.source, c x = (e x.val).2) ∧
      (∀ t ∈ c.target, (c.symm t).val = e.symm (0,t)) := by
  obtain ⟨a,ha,has,hat,haf,hag⟩ :=
    matched_subset_chart e S {z | z.1 = 0} p hp hpS hmatch
  let h := (zeroSliceLineHomeomorph (E := E)).toOpenPartialHomeomorph
  let c := a.trans h
  have hcs : c.source = a.source := by
    ext x
    simp [c,h]
  have hct : c.target = {t | (0,t) ∈ e.target} := by
    ext t
    simp [c,h,hat,zeroSliceLineHomeomorph]
  refine ⟨c,?_,hcs.trans has,hct,?_,?_⟩
  · rw [hcs]
    exact ha
  · intro x hx
    change (a x).val.2 = (e x.val).2
    rw [haf x (hcs ▸ hx)]
  · intro t ht
    change (a.symm ⟨(0,t),rfl⟩).val = e.symm (0,t)
    apply hag
    rw [hat]
    change (0,t) ∈ e.target
    rw [hct] at ht
    exact ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OpenIntervalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a map on the open unit interval by prescribed endpoint
values. Continuity in the interior is independent of endpoint limits. -/
noncomputable section
open Set Topology unitInterval
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*}

def intervalInteriorPoint (t : I) (h0 : t ≠ 0) (h1 : t ≠ 1) : Ioo (0:ℝ) 1 :=
  ⟨t.val,by
    constructor
    · apply lt_of_le_of_ne t.property.1
      intro h
      exact h0 (Subtype.ext h.symm)
    · apply lt_of_le_of_ne t.property.2
      intro h
      exact h1 (Subtype.ext h)⟩

def openIntervalExtension (F : Ioo (0:ℝ) 1 → X) (x y : X) (t : I) : X :=
  if h0 : t = 0 then x else if h1 : t = 1 then y else F (intervalInteriorPoint t h0 h1)

@[simp] lemma openIntervalExtension_zero (F : Ioo (0:ℝ) 1 → X) (x y : X) :
    openIntervalExtension F x y 0 = x := by simp [openIntervalExtension]

@[simp] lemma openIntervalExtension_one (F : Ioo (0:ℝ) 1 → X) (x y : X) :
    openIntervalExtension F x y 1 = y := by simp [openIntervalExtension]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_UnorderedSurfacePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hausdorff space of unordered pairs. The quotient identifies only
interchanging the two source points of a double pair. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def surfacePairSetoid (M : Type*) : Setoid (M × M) where
  r x y := x = y ∨ x = y.swap
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h,Prod.swap_swap])
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (hxy.trans hyz)
      · exact Or.inr (hxy.trans (congrArg Prod.swap hyz))
      · exact Or.inl (by rw [hxy,hyz,Prod.swap_swap]) }

abbrev UnorderedSurfacePairs (M : Type*) := Quotient (surfacePairSetoid M)

def unorderedPair {M : Type*} (z : M × M) : UnorderedSurfacePairs M := @Quotient.mk' (M × M) (surfacePairSetoid M) z

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnorderedPairCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unordered-pair quotient is a two-sheeted covering away from
the diagonal. At a diagonal point its fiber is a singleton. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

def unorderedDistinctPairs (M : Type*) : Set (UnorderedSurfacePairs M) :=
  {z | ¬ ∃ p : M, unorderedPair (p,p) = z}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactCurveArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact embedded arcs with open interior, used to reduce the
compact one-dimensional curve to finitely many interval pieces. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable (X : Type*) [TopologicalSpace X]

structure CompactCurveArc where
  left : ℝ
  right : ℝ
  ordered : left < right
  map : Icc left right → X
  embedding : IsClosedEmbedding map
  interior_open : IsOpen (map '' {t | left < (t:ℝ) ∧ (t:ℝ) < right})

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EmbeddedOpenSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open subarcs remain open in the ambient curve. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {Z : Type*} [TopologicalSpace Z]

def CompactCurveArc.openSubarc (A : CompactCurveArc Z) (u v : ℝ) : Set Z :=
  A.map '' {t | u < (t:ℝ) ∧ (t:ℝ) < v}

def CompactCurveArc.closedSubarc (A : CompactCurveArc Z) (u v : ℝ) : Set Z :=
  A.map '' {t | u ≤ (t:ℝ) ∧ (t:ℝ) ≤ v}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgeWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each finite curve edge retains its actual compact interval
parametrization, two distinct endpoints, and exact frontier. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

structure CurveEdgeWitness (V E : Set X) where
  arc : CompactCurveArc X
  lo : ℝ
  hi : ℝ
  lower : arc.left ≤ lo
  upper : hi ≤ arc.right
  ordered : lo < hi
  piece_eq : E = arc.openSubarc lo hi
  left_mem : arc.map ⟨lo,lower,ordered.le.trans upper⟩ ∈ V
  right_mem : arc.map ⟨hi,lower.trans ordered.le,upper⟩ ∈ V

def CurveEdgeWitness.leftPoint {V E : Set X} (w : CurveEdgeWitness V E) : X :=
  w.arc.map ⟨w.lo,w.lower,w.ordered.le.trans w.upper⟩

def CurveEdgeWitness.rightPoint {V E : Set X} (w : CurveEdgeWitness V E) : X :=
  w.arc.map ⟨w.hi,w.lower.trans w.ordered.le,w.upper⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteIntervalChopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutting a real interval at a finite vertex set produces uniquely
determined consecutive open subintervals. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def ConsecutiveVertices (S : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ t ∈ S, ¬ (a < t ∧ t < b)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveIncidenceGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bipartite incidence graph remembers distinct parallel interval edges. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

def curveIncidenceGraph (V : Set X) (P : Finset (Set X)) : SimpleGraph (V ⊕ P) where
  Adj a b := match a,b with
    | Sum.inl v, Sum.inr E => v.val ∈ closure E.val
    | Sum.inr E, Sum.inl v => v.val ∈ closure E.val
    | _,_ => False
  symm := ⟨by rintro (v|E) (w|F) h <;> exact h⟩
  loopless := ⟨by rintro (v|E) h <;> exact h⟩

@[simp] lemma curveIncidenceGraph_left_right (V : Set X) (P : Finset (Set X)) (v : V) (E : P) :
    (curveIncidenceGraph V P).Adj (Sum.inl v) (Sum.inr E) ↔ v.val ∈ closure E.val := Iff.rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgeParametrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained edge witnesses give actual compact interval
parametrizations of their closures. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

def CurveEdgeWitness.param {V E : Set X} (w : CurveEdgeWitness V E) : Icc w.lo w.hi → X :=
  fun t => w.arc.map ⟨t.val,w.lower.trans t.property.1,t.property.2.trans w.upper⟩

lemma CurveEdgeWitness.param_closedEmbedding {V E : Set X} (w : CurveEdgeWitness V E) :
    IsClosedEmbedding w.param := by
  let j : Icc w.lo w.hi → Icc w.arc.left w.arc.right := fun t =>
    ⟨t.val,w.lower.trans t.property.1,t.property.2.trans w.upper⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hc : Continuous w.param := w.arc.embedding.continuous.comp hj
  apply hc.isClosedEmbedding
  intro s t hst
  have he := w.arc.embedding.injective hst
  exact Subtype.ext (congrArg (fun u : Icc w.arc.left w.arc.right => (u:ℝ)) he)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each retained compact interval edge is parametrized by an injective
path, in either orientation. -/
noncomputable section
open Set Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

def CurveEdgeWitness.path {V E : Set X} (w : CurveEdgeWitness V E) :
    Path w.leftPoint w.rightPoint where
  toFun t := w.param ((iccHomeoI w.lo w.hi w.ordered).symm t)
  continuous_toFun := w.param_closedEmbedding.continuous.comp (iccHomeoI w.lo w.hi w.ordered).symm.continuous
  source' := by
    change w.param _ = w.param ⟨w.lo,le_rfl,w.ordered.le⟩
    congr 1
    apply Subtype.ext
    simp
  target' := by
    change w.param _ = w.param ⟨w.hi,w.ordered.le,le_rfl⟩
    congr 1
    apply Subtype.ext
    simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EmbeddedCurveGraphPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simple path in the interval incidence graph has an actual
embedded realization in the compact curve. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

structure RealizedCurveWalk {V : Set X} {P : Finset (Set X)} {a b : V}
    (p : (curveIncidenceGraph V P).Walk (Sum.inl a) (Sum.inl b)) where
  path : Path a.val b.val
  injective : a ≠ b → Function.Injective path
  vertex : ∀ v : V, v.val ∈ range path → Sum.inl v ∈ p.support
  edge : ∀ E : P, (range path ∩ E.val).Nonempty → Sum.inr E ∈ p.support

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnorderedPairMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying a function to both entries of an unordered pair. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def unorderedPairMap {M N : Type*} (f : M → N) : UnorderedSurfacePairs M → UnorderedSurfacePairs N :=
  Quotient.map (Prod.map f f) (by
    intro x y h
    rcases h with h | h
    · exact Or.inl (congrArg (Prod.map f f) h)
    · right
      rw [h]
      rfl)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularArcPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paths generated by finitely many compact regular smooth arcs, with
explicit subdivision, concatenation and endpoint casts. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

namespace SmoothCompactArc

def path (P : SmoothCompactArc J N) : Path (P.curve P.start) (P.curve P.finish) where
  toFun t := P.curve ((iccHomeoI P.start P.finish P.start_lt_finish).symm t)
  continuous_toFun := (P.smooth.continuousOn.mono P.interval_subset).domRestrict.comp
    (iccHomeoI P.start P.finish P.start_lt_finish).symm.continuous
  source' := by
    congr 1
    simp
  target' := by
    congr 1
    simp

end SmoothCompactArc

/-- A finite expression made from actual compact regular smooth arcs.
This records the geometric pieces even when their concatenation has corners. -/
inductive FiniteRegularPath (J : ModelWithCorners ℝ E H) : {x y : N} → Path x y → Prop
  | arc (P : SmoothCompactArc J N) : FiniteRegularPath J P.path
  | subpath {x y : N} {γ : Path x y} (hγ : FiniteRegularPath J γ) (s t : I) :
      FiniteRegularPath J (γ.subpath s t)
  | trans {x y z : N} {γ : Path x y} {δ : Path y z}
      (hγ : FiniteRegularPath J γ) (hδ : FiniteRegularPath J δ) :
      FiniteRegularPath J (γ.trans δ)
  | cast {x y x' y' : N} {γ : Path x y} (hγ : FiniteRegularPath J γ)
      (hx : x' = x) (hy : y' = y) : FiniteRegularPath J (γ.cast hx hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite closed-interval cover records actual smooth arc formulas for
paths assembled by subdivision and concatenation. Slopes may be zero before
injectivity of the assembled path is imposed. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

structure RegularPathCover {x y : M} (γ : Path x y) where
  Index : Type
  finite : Fintype Index
  region : Index → Set ℝ
  closed : ∀ i, IsClosed (region i)
  convex : ∀ i, Convex ℝ (region i)
  subset : ∀ i, region i ⊆ Icc 0 1
  arc : Index → SmoothCompactArc J M
  slope : Index → ℝ
  offset : Index → ℝ
  cover : ∀ t : I, ∃ i, (t:ℝ) ∈ region i
  parameter : ∀ i t, t ∈ region i → slope i*t+offset i ∈ Icc (arc i).start (arc i).finish
  agree : ∀ i (t : I), (t:ℝ) ∈ region i → γ t = (arc i).curve (slope i*t+offset i)

namespace RegularPathCover

lemma affine_preimage_convex {S : Set ℝ} (hS : Convex ℝ S) (a b : ℝ) :
    Convex ℝ ((fun x => a*x+b) ⁻¹' S) := by
  intro x hx y hy u v hu hv huv
  have h := hS hx hy hu hv huv
  change a*(u*x+v*y)+b ∈ S
  have he : a*(u*x+v*y)+b = u*(a*x+b)+v*(a*y+b) := by
    calc
      a*(u*x+v*y)+b = a*(u*x+v*y)+(u+v)*b := by rw [huv,one_mul]
      _ = u*(a*x+b)+v*(a*y+b) := by ring
  rw [he]
  exact h

noncomputable def ofArc (P : SmoothCompactArc J M) : RegularPathCover (J := J) P.path where
  Index := Unit
  finite := inferInstance
  region := fun _ => Icc 0 1
  closed := fun _ => isClosed_Icc
  convex := fun _ => convex_Icc 0 1
  subset := fun _ => Subset.rfl
  arc := fun _ => P
  slope := fun _ => P.finish-P.start
  offset := fun _ => P.start
  cover := fun t => ⟨(),t.property⟩
  parameter := by
    intro _ t ht
    have h := ((iccHomeoI P.start P.finish P.start_lt_finish).symm ⟨t,ht⟩).property
    simpa only [iccHomeoI_symm_apply_coe] using h
  agree := by
    intro _ t _
    change P.curve (((iccHomeoI P.start P.finish P.start_lt_finish).symm t):ℝ) = _
    rw [iccHomeoI_symm_apply_coe]

variable {x y : M} {γ : Path x y}

noncomputable def cast (P : RegularPathCover (J := J) γ) {x' y' : M}
    (hx : x' = x) (hy : y' = y) : RegularPathCover (J := J) (γ.cast hx hy) where
  Index := P.Index
  finite := P.finite
  region := P.region
  closed := P.closed
  convex := P.convex
  subset := P.subset
  arc := P.arc
  slope := P.slope
  offset := P.offset
  cover := P.cover
  parameter := P.parameter
  agree := P.agree

noncomputable def subpath (P : RegularPathCover (J := J) γ) (s t : I) :
    RegularPathCover (J := J) (γ.subpath s t) := by
  let a : ℝ := (t:ℝ)-(s:ℝ)
  let b : ℝ := s
  have haff (u : I) : a*(u:ℝ)+b = (Icc.convexComb s t u : ℝ) := by
    rw [Icc.coe_convexComb]
    dsimp [a,b]
    ring
  refine {
    Index := P.Index
    finite := P.finite
    region := fun i => Icc 0 1 ∩ (fun u => a*u+b) ⁻¹' P.region i
    closed := fun i => isClosed_Icc.inter ((P.closed i).preimage (by fun_prop))
    convex := fun i => (convex_Icc 0 1).inter (affine_preimage_convex (P.convex i) a b)
    subset := fun _ => inter_subset_left
    arc := P.arc
    slope := fun i => P.slope i*a
    offset := fun i => P.slope i*b+P.offset i
    cover := ?_
    parameter := ?_
    agree := ?_ }
  · intro u
    obtain ⟨i,hi⟩ := P.cover (Icc.convexComb s t u)
    refine ⟨i,u.property,?_⟩
    change a*(u:ℝ)+b ∈ P.region i
    rw [haff u]
    exact hi
  · intro i u hu
    have h := P.parameter i (a*u+b) hu.2
    convert h using 1 <;> first | rfl | ring
  · intro i u hu
    have hmem : (Icc.convexComb s t u : ℝ) ∈ P.region i := by
      rw [← haff u]
      exact hu.2
    have h := P.agree i (Icc.convexComb s t u) hmem
    change γ (Icc.convexComb s t u) = _
    rw [h,← haff u]
    congr 1
    ring

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathCoverConcat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concatenation preserves the finite closed-interval smooth formulas. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y z : M} {γ : Path x y} {δ : Path y z}
namespace RegularPathCover

noncomputable def trans (P : RegularPathCover (J := J) γ) (Q : RegularPathCover (J := J) δ) :
    RegularPathCover (J := J) (γ.trans δ) := by
  haveI := P.finite
  haveI := Q.finite
  let L : P.Index → Set ℝ := fun i => Icc 0 (1/2) ∩ (fun t => 2*t) ⁻¹' P.region i
  let R : Q.Index → Set ℝ := fun i => Icc (1/2) 1 ∩ (fun t => 2*t-1) ⁻¹' Q.region i
  refine {
    Index := P.Index ⊕ Q.Index
    finite := inferInstance
    region := Sum.elim L R
    closed := ?_
    convex := ?_
    subset := ?_
    arc := Sum.elim P.arc Q.arc
    slope := Sum.elim (fun i => 2*P.slope i) (fun i => 2*Q.slope i)
    offset := Sum.elim P.offset (fun i => Q.offset i-Q.slope i)
    cover := ?_
    parameter := ?_
    agree := ?_ }
  · intro i
    cases i with
    | inl i => exact isClosed_Icc.inter ((P.closed i).preimage (by fun_prop))
    | inr i => exact isClosed_Icc.inter ((Q.closed i).preimage (by fun_prop))
  · intro i
    cases i with
    | inl i =>
      exact (convex_Icc 0 (1/2)).inter (by
        simpa only [add_zero] using affine_preimage_convex (P.convex i) 2 0)
    | inr i =>
      exact (convex_Icc (1/2) 1).inter (by
        simpa only [sub_eq_add_neg] using affine_preimage_convex (Q.convex i) 2 (-1))
  · intro i t ht
    cases i with
    | inl i => exact ⟨ht.1.1,ht.1.2.trans (by norm_num)⟩
    | inr i => exact ⟨(by norm_num : (0:ℝ) ≤ 1/2).trans ht.1.1,ht.1.2⟩
  · intro t
    by_cases ht : (t:ℝ) ≤ 1/2
    · let u : I := ⟨2*t,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨i,hi⟩ := P.cover u
      exact ⟨Sum.inl i,⟨t.property.1,ht⟩,hi⟩
    · let u : I := ⟨2*t-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨i,hi⟩ := Q.cover u
      exact ⟨Sum.inr i,⟨(not_le.mp ht).le,t.property.2⟩,hi⟩
  · intro i t ht
    cases i with
    | inl i =>
      have h := P.parameter i (2*t) ht.2
      change 2*P.slope i*t+P.offset i ∈ Icc (P.arc i).start (P.arc i).finish
      convert h using 1 <;> first | rfl | ring
    | inr i =>
      have h := Q.parameter i (2*t-1) ht.2
      change 2*Q.slope i*t+(Q.offset i-Q.slope i) ∈ Icc (Q.arc i).start (Q.arc i).finish
      convert h using 1 <;> first | rfl | ring
  · intro i t ht
    cases i with
    | inl i =>
      let u : I := ⟨2*t,P.subset i ht.2⟩
      have hp : (γ.trans δ) t = γ u := by
        calc
          (γ.trans δ) t = (γ.trans δ).extend (t:ℝ) := ((γ.trans δ).extend_extends' t).symm
          _ = γ.extend (2*t) := Path.extend_trans_of_le_half γ δ ht.1.2
          _ = γ u := γ.extend_apply u.property
      rw [hp,P.agree i u ht.2]
      congr 1
      dsimp [u]
      ring
    | inr i =>
      let u : I := ⟨2*t-1,Q.subset i ht.2⟩
      have hp : (γ.trans δ) t = δ u := by
        calc
          (γ.trans δ) t = (γ.trans δ).extend (t:ℝ) := ((γ.trans δ).extend_extends' t).symm
          _ = δ.extend (2*t-1) := Path.extend_trans_of_half_le γ δ ht.1.1
          _ = δ u := δ.extend_apply u.property
      rw [hp,Q.agree i u ht.2]
      congr 1
      dsimp [u]
      ring

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth arc tails retain the exact forward germ needed by the next
piece in the finite source-arc assembly. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure SmoothArcTail (f : ℝ → M) (a : ℝ) where
  arc : SmoothCompactArc planeModel M
  parameter : ℝ → ℝ
  smooth : ContDiff ℝ ∞ parameter
  forward : 0 < deriv parameter arc.finish
  value : parameter arc.finish = a
  germ : arc.curve =ᶠ[𝓝 arc.finish] f ∘ parameter

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EndpointSignModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simplest affine coefficient with the two prescribed endpoint signs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def nonzeroSign (r : ℝ) : ℝ := if 0 < r then 1 else -1

def endpointSignModel (p q a b t : ℝ) : ℝ :=
  ((q-t)/(q-p))*nonzeroSign a+((t-p)/(q-p))*nonzeroSign b

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

abbrev FrameTarget := Fin 3 → ℝ

def rotationFirst (a b c : ℝ) : FrameTarget :=
  ![a^2+b^2-c^2,2*b*c,-2*a*c]
def rotationSecond (a b c : ℝ) : FrameTarget :=
  ![2*b*c,a^2-b^2+c^2,2*a*b]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PairModelCoordinates
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

def normalPairScale (a b : ℝ) : FrameTarget →L[ℝ] FrameTarget :=
  (ContinuousLinearMap.proj 0).smulRight (![1,0,0] : FrameTarget)+
  (ContinuousLinearMap.proj 1).smulRight (![0,a,0] : FrameTarget)+
  (ContinuousLinearMap.proj 2).smulRight (![0,0,b] : FrameTarget)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetMeanFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual finite metric mean from one common bound on its
seven local budgets. The envelope records the derivative shift explicitly. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

def meanGeometryEnvelope (q : ℕ) (H B : ℕ → ℝ) (m : ℕ) : ℝ :=
  1+H m+B (m+q+2)+B m

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial families can be padded to a common degree and added
without changing their values or their smooth-coefficient property. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

namespace Perturbation

/-- The largest number of powers in a finite dependent family. -/
def polynomialFamilyDegree {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℕ :=
  Finset.univ.sup n

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial majorants survive the read/restore operations in
an atlas. All dependence on transport constants stays in the profile. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes

def transportedMeanGeometry (L : ℕ) (G D E : ℕ → ℝ) (m : ℕ) : ℝ :=
  1+G m+D (m+L)+E m

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricForcedBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial constants for the actual supported forced metric solver.
The scale factor in its residual is separated from its geometric budget. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

def metricForcedSizeBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ)*(2^m*(forcedModeBudget 4 0 C (fun _ => 0) q m*N (m+q+1)))*J m^m

def metricForcedResidualBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  tensorChartBudget m (J m) (J (m+1)) * (2^m *
    FiniteParametrix.boundProfile 1 (fun r => errorConstant r (C r))
      (fun r => errorConstant r (C r)*N (r+1)) q m)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricFreeBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial budgets for the actual unperturbed free metric modes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

def metricFreeSizeBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ)*2^m*correctedSeedBudget 0 C (fun _ => 0) q m (N (m+q+1))*J m^m

def metricFreeResidualBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  tensorChartBudget m (J m) (J (m+1))*2^m*
    (FiniteParametrix.boundProfile 1 (fun r => errorConstant r (C r))
      (fun r => fullErrorConstant 4 r (C r)) q m * (Real.sqrt 2*2^(m+q+1)*N (m+q+1)))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticTargetBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quadratic target constant is polynomial in the amplitude and phase
budgets, with the fixed cutoff constant kept explicit. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def quadraticTargetBudget (m : ℕ) (D A P : ℝ) : ℝ :=
  2^m*D*(4*2^m*((1+2^m*P)*A)^2)

end ClosedSurfaceR4.JetPolynomial

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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polySmoothingProfileDualAdd_r0be074_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polySmoothingProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
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
open PhaseMean RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialTensorMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialTensorMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicGlobalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported local periodic coefficients extend smoothly by zero. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Closed support lying inside the admissible domain suffices for smooth
extension; there is no regularity requirement on the domain boundary. -/
lemma contDiff_of_zero_off_closed {F : A × ℝ → E} {O K : Set A}
    (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F (O ×ˢ Set.univ))
    (hK : IsClosed K) (hKO : K ⊆ O) (hz : ∀ p ∉ K, ∀ t, F (p, t) = 0) :
    ContDiff ℝ ∞ F := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hp : z.1 ∈ O
  · exact hF.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ z.2⟩)
  · have hpK : z.1 ∉ K := fun hk => hp (hKO hk)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.continuousAt :
      Filter.Tendsto Prod.fst (𝓝 z) (𝓝 z.1)).eventually (hK.isOpen_compl.mem_nhds hpK)] with w hw
    exact hz w.1 hw w.2

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAnsatzAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact, fixed-coefficient asymptotics of the finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion
open WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def directionalMap (F : A → E) (v : A) : A → E := fun p => fderiv ℝ F p v

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteDisjointAdjustment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combine the finitely many crossing adjustments on pairwise disjoint
neighborhoods. The patched field agrees exactly with the selected local field. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.VelocityFrame
variable {E F ι : Type*}

def finiteDisjointAdjustment [AddCommGroup F] (s : Finset ι) (n : E → F) (g : ι → E → F) : E → F :=
  fun x => n x + ∑ i ∈ s, (g i x - n x)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reparametrization commutes exactly with pulling back the parameter family. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PositiveDensity

variable {B E F : Type}

def pullbackDensity (ρ : B × ℝ → ℝ) (σ : E → B) : E × ℝ → ℝ :=
  fun z => ρ (σ z.1, z.2)

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global object carried by the primitive induction is a smooth unit
section of the normal bundle. A spherical starting immersion supplies one. -/
noncomputable section
open Manifold Filter
open scoped Topology
open scoped ContDiff
namespace ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure PreferredNormal (F : M → Space) where
  vector : M → Space
  smooth : ContMDiff planeModel spaceModel ∞ vector
  unit : ∀ p, ‖vector p‖ = 1
  normal : ∀ p (v : TangentSpace planeModel p),
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (vector p) = 0

lemma spherical_inward_normal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (p : M) (v : TangentSpace planeModel p) :
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (-F p) = 0 := by
  let q : Space → ℝ := fun y => inner ℝ y y
  have hq : ContDiff ℝ ∞ q := contDiff_id.inner ℝ contDiff_id
  have he : q ∘ F = fun _ => (1 : ℝ) := by
    funext x
    change inner ℝ (F x) (F x) = 1
    rw [real_inner_self_eq_norm_sq,hunit]
    norm_num
  have heq : q ∘ F =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := Filter.Eventually.of_forall (congrFun he)
  have hd := heq.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  rw [mfderiv_comp p (hq.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt,mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun L : TangentSpace planeModel p →L[ℝ] ℝ => L v) hd
  let w : Space := mfderiv planeModel spaceModel F p v
  simp only [mfderiv_const] at hv
  change fderiv ℝ q (F p) w = 0 at hv
  have hderiv : fderiv ℝ q (F p) w = 2 * inner ℝ w (F p) := by
    change fderiv ℝ (fun y : Space => inner ℝ y y) (F p) w = _
    rw [fderiv_inner_apply ℝ (f := fun y : Space => y) (g := fun y : Space => y)
      differentiableAt_id differentiableAt_id]
    simp only [fderiv_fun_id,ContinuousLinearMap.id_apply]
    change inner ℝ (F p) w + inner ℝ w (F p) = _
    rw [real_inner_comm (F p) w]
    ring
  change inner ℝ w (-F p) = 0
  rw [inner_neg_right]
  linarith

/-- The inward radial section is a global preferred normal, without an
orientation or a global choice of a second normal vector. -/
def sphericalPreferredNormal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    PreferredNormal F where
  vector p := -F p
  smooth := hF.neg
  unit p := by simpa only [norm_neg] using hunit p
  normal := spherical_inward_normal hF hunit

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SafeRadialNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A globally smooth extension of radial normalization that agrees with it
outside the half-unit ball. Only this fixed extension is used in atlas bounds. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

def normalizationCutoff : ContDiffBump (0 : Space) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def safeRadialNormalize (x : Space) : Space :=
  (1-normalizationCutoff x) • radialNormalize x

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The spherical lift of an ordinary surface immersion

Inverse stereographic projection lifts a smooth immersion into three-space
to a smooth spherical immersion in four-space, as in Section 8.1 of paper 094-01.
-/

noncomputable section

namespace ClosedSurfaceR4.SphericalStart

open Set Manifold
open scoped ContDiff Topology InnerProductSpace

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)
abbrev Hyperplane (v : Space) := (ℝ ∙ v)ᗮ

/-- Inverse stereographic projection, regarded as an ambient R4-valued map. -/
def lift (v : Space) (w : Hyperplane v) : Space := stereoInvFunAux v w

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M]

/-- The hyperplane perpendicular to a nonzero vector in four-space is
isometrically three-dimensional. -/
def threeSpaceToHyperplane {v : Space} (hv : v ≠ 0) :
    ThreeSpace ≃ₗᵢ[ℝ] Hyperplane v := by
  letI : Fact (Module.finrank ℝ Space = 3 + 1) := ⟨by simp [Space]⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton 3 hv).repr.symm

end ClosedSurfaceR4.SphericalStart

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance inverseTensorDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inverseTensorDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseSmallFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A narrow transverse correction with arbitrarily small values and a fixed first jet. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace ClosedSurfaceR4.TransverseSmallFunction

def cutoff : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def correction (f g : E → ℝ) (δ : ℝ) (x : E) : ℝ :=
  f x * g x * cutoff (f x / δ)

end ClosedSurfaceR4.TransverseSmallFunction

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

abbrev Moments := Fin 3 → ℝ

def density (ε : ℝ) (ψ : Fin 3 → ℝ → ℝ) (w : Moments) (t : ℝ) : ℝ :=
  ε + ∑ i, w i * ψ i t

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar identities used in the later-curve crossing calculation. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

/-- The normal components forced by the Gauss identity when the transverse
second-form component is `(S,0)`. -/
def frameXX (S D N L k : ℝ) : ℝ × ℝ := ((k+D^2+N^2)/S,L)
def frameXY (D N : ℝ) : ℝ × ℝ := (D,N)
def frameYY (S : ℝ) : ℝ × ℝ := (S,0)

def pureComponents (S D N L k b c : ℝ) : ℝ × ℝ :=
  b^2 • frameXX S D N L k + (2*b*c) • frameXY D N + c^2 • frameYY S

def slopePure (S D N L k t : ℝ) : ℝ × ℝ :=
  ((N^2+k+(D+S*t)^2)/S,L+2*N*t)

def slopeMixed (S D N L k t u : ℝ) : ℝ × ℝ :=
  ((N^2+k+(D+S*t)*(D+S*u))/S,L+N*(t+u))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered mixed projection is bounded independently of the unbounded
longitudinal second-form component. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def frameVector (n m : E) (v : ℝ × ℝ) : E := v.1 • n+v.2 • m

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingInvariantThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite threshold gives both ordered crossing inequalities. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def modelOrderedCrossing (n m : E) (S D N L k t u : ℝ) : ℝ :=
  (inner ℝ (frameVector n m (slopeMixed S D N L k t u))
    (‖frameVector n m (slopePure S D N L k t)‖⁻¹ •
      frameVector n m (slopePure S D N L k t)))^2+k*(t-u)^2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicLocalizedBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth positive-mass bumps on the unit circle, localized inside one period. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

def circleBump (φ : ContDiffBump (0 : ℝ)) (c t : ℝ) : ℝ :=
  φ (Real.sin (Real.pi * (t - c)))

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LoopDensityBumpSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace three nondegenerate point masses by smooth positive-density data. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.LoopDensity

abbrev Columns := Fin 3 → Moments

def columnOperator (C : Columns) : Moments →L[ℝ] Moments :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (C i)

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

def triangleWeights (r : ℝ) : Moments := ![(1 + 2 * r) / 3, (1 - r) / 3, (1 - r) / 3]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFiberInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite rank-one correction acts on symmetric tensors. Adding the
identity on the antisymmetric summand gives an honest invertible operator
on the full four-dimensional tensor fiber, without an orientation choice. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance primitiveInverseDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance
local instance primitiveInverseDualSmul : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance

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

local instance dataDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 control of the actual inverse and square-root amplitude map.
The parameter bounds are fixed before a later family is composed with it. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance amplitudeDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary chain-rule estimate used for each actual amplitude chart. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance ampChainPlaneDualNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance ampChainPlaneDualSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance finiteDataCovectorNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance finiteDataCovectorSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveSlowScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slow scales in the high-accuracy primitive realization.
These choices precede every accuracy order in its mean iteration. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

def amplitudeExponent (j : ℕ) : ℝ := (1/4)*(6/5 : ℝ)^j
def scaleExponent (σ : ℝ) (steps j : ℕ) : ℝ := (j : ℝ)*σ/(steps : ℝ)

end ClosedSurfaceR4.PrimitiveRealization

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

def arcWeights (q m : ℝ) : Moments :=
  ![(m - q) / (1 - q), (1 - m) / (2 * (1 - q)), (1 - m) / (2 * (1 - q))]

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Topology_Misc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter TopologicalSpace
open scoped unitInterval Topology uniformity

section

@[to_additive]
theorem hasCompactMulSupport_of_subset {α β : Type*} [TopologicalSpace α] [T2Space α] [One β]
    {f : α → β} {K : Set α} (hK : IsCompact K) (hf : mulSupport f ⊆ K) : HasCompactMulSupport f :=
  hK.of_isClosed_subset (isClosed_mulTSupport f) (closure_minimal hf hK.isClosed)

end

section

open Encodable Option

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]

-- can we restate this nicely?
/-- Given a locally finite sequence of sets indexed by an encodable type, we can naturally reindex
  this sequence to get a sequence indexed by `ℕ` (by adding some `∅` values).
  This new sequence is still locally finite. -/
theorem decode₂_locallyFinite {ι} [Encodable ι] {s : ι → Set α} (hs : LocallyFinite s) :
    LocallyFinite fun i ↦ (s <$> decode₂ ι i).getD ∅ := fun x ↦ by
  obtain ⟨U, hxU, hU⟩ := hs x
  refine ⟨U, hxU, ?_⟩
  have :
      encode ⁻¹' {i : ℕ | ((s <$> decode₂ ι i).getD ∅ ∩ U).Nonempty} =
      {i : ι | (s i ∩ U).Nonempty} := by
    simp_rw [preimage_ofPred_eq, decode₂_encode, map_eq_map, map_some, getD_some]
  rw [← this] at hU
  refine finite_of_finite_preimage hU ?_
  intro n hn
  rw [← decode₂_ne_none_iff]
  intro h
  simp_rw [mem_ofPred_eq, h, map_eq_map, map_none, getD_none, empty_inter] at hn
  exact (not_nonempty_empty hn).elim

variable {X : Type*} [EMetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]

set_option linter.style.cases false in
theorem exists_locallyFinite_subcover_of_locally {C : Set X} (hC : IsClosed C) {P : Set X → Prop}
    (hP : Antitone P) (h0 : P ∅) (hX : ∀ x ∈ C, ∃ V ∈ 𝓝 (x : X), P V) :
    ∃ (K : ℕ → Set X) (W : ℕ → Set X), (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧
      (∀ n, P (W n)) ∧ (∀ n, K n ⊆ W n) ∧ LocallyFinite W ∧ C ⊆ ⋃ n, K n := by
  choose V' hV' hPV' using SetCoe.forall'.mp hX
  choose V hV hVV' hcV using fun x : C ↦ LocallyCompactSpace.local_compact_nhds (↑x) (V' x) (hV' x)
  simp_rw [← mem_interior_iff_mem_nhds] at hV
  have : C ⊆ ⋃ x : C, interior (V x) := fun x hx ↦ by rw [mem_iUnion]; exact ⟨⟨x, hx⟩, hV _⟩
  obtain ⟨s, hs, hsW₂⟩ := isOpen_iUnion_countable (fun x ↦ interior (V x)) fun x ↦ isOpen_interior
  rw [← hsW₂, biUnion_eq_iUnion] at this; clear hsW₂
  obtain ⟨W, hW, hUW, hlW, hWV⟩ :=
    precise_refinement_set hC (fun x : s ↦ interior (V x)) (fun x ↦ isOpen_interior) this
  obtain ⟨K, hCK, hK, hKW⟩ :=
    exists_subset_iUnion_closed_subset hC (fun x : s ↦ hW x) (fun x _ ↦ hlW.point_finite x) hUW
  have : Encodable s := hs.toEncodable
  let K' : ℕ → Set X := fun n ↦ (K <$> decode₂ s n).getD ∅
  let W' : ℕ → Set X := fun n ↦ (W <$> decode₂ s n).getD ∅
  refine ⟨K', W', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; cases' h : decode₂ s n with i
    · simp_rw [K', h, map_eq_map, map_none, getD_none, isCompact_empty]
    · simp_rw [K', h, map_eq_map, map_some, getD_some]
      exact (hcV i).of_isClosed_subset (hK i) ((hKW i).trans <| (hWV i).trans interior_subset)
  · intro n; cases h : decode₂ s n
    · simp_rw [W', h, map_eq_map, map_none, getD_none, isOpen_empty]
    · simp_rw [W', h, map_eq_map, map_some, getD_some, hW]
  · intro n; cases' h : decode₂ s n with i
    · simp_rw [W', h, map_eq_map, map_none, getD_none, h0]
    · simp_rw [W', h, map_eq_map, map_some, getD_some]; refine hP ?_ (hPV' i)
      exact (hWV i).trans (interior_subset.trans <| hVV' i)
  · intro n; cases h : decode₂ s n
    · simp_rw [K', W', h, map_eq_map, map_none]; rfl
    · simp_rw [K', W', h, map_eq_map, map_some, getD_some, hKW]
  · exact decode₂_locallyFinite hlW
  · intro x hx; obtain ⟨i, hi⟩ := mem_iUnion.mp (hCK hx)
    refine mem_iUnion.mpr ⟨encode i, ?_⟩
    simp_rw [K', decode₂_encode, map_eq_map, map_some, getD_some, hi]

end

section

open Metric

attribute [fun_prop] continuous_infDist_pt

end

open Subtype
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter

open scoped Topology ContDiff

section Calculus

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {E₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

variable (𝕜)

variable {𝕜}

@[to_additive]
nonrec theorem WithTop.le_mul_self {α : Type*} [CommMonoid α] [PartialOrder α]
    [CanonicallyOrderedMul α] (n m : α) :
    (n : WithTop α) ≤ (m * n : α) :=
  WithTop.coe_le_coe.mpr le_mul_self

@[to_additive]
nonrec theorem WithTop.le_self_mul {α : Type*} [CommMonoid α] [PartialOrder α]
    [CanonicallyOrderedMul α] (n m : α) :
    (n : WithTop α) ≤ (n * m : α) :=
  WithTop.coe_le_coe.mpr le_self_mul

end Calculus

open Filter
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Algebra_Ring_Periodic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

-- TODO: the file this references doesn't exist in mathlib any more; rename this one appropriately!

/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma Continuous.bounded_of_onePeriodic_of_isCompact {f : X → ℝ → E} (cont : Continuous ↿f)
  (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C
```

This is done by introducing the quotient 𝕊₁ = ℝ/ℤ as a compact topological space.
Patrick is not sure this is the optimal version.

In the first part, generalize many lemmas to any period and add to `Algebra.Ring.Periodic.lean`?
-/

section


noncomputable section

open Set Function Filter TopologicalSpace Int

open scoped Topology

section OnePeriodic

variable {α : Type*}

/-- The integers as an additive subgroup of the reals. -/
def ℤSubℝ : AddSubgroup ℝ := AddMonoidHom.range (Int.castAddHom ℝ)

/-- The equivalence relation on `ℝ` corresponding to its partition as cosets of `ℤ`. -/
@[implicit_reducible]
def transOne : Setoid ℝ := QuotientAddGroup.leftRel ℤSubℝ

/-- The circle `𝕊₁ := ℝ/ℤ`.

TODO [Yury]: use `AddCircle`. -/
def 𝕊₁ :=
  Quotient transOne
deriving TopologicalSpace, Inhabited

theorem transOne_rel_iff {a b : ℝ} : transOne.r a b ↔ ∃ k : ℤ, b = a + k := by
  refine QuotientAddGroup.leftRel_apply.trans (exists_congr fun k ↦ ?_)
  rw [coe_castAddHom, eq_neg_add_iff_add_eq, eq_comm]

section

attribute [local instance] transOne

/-- The quotient map from the reals to the circle `ℝ ⧸ ℤ`. -/
def proj𝕊₁ : ℝ → 𝕊₁ :=
  Quotient.mk'

@[simp]
theorem proj𝕊₁_add_int (t : ℝ) (k : ℤ) : proj𝕊₁ (t + k) = proj𝕊₁ t :=
  (Quotient.sound (transOne_rel_iff.mpr ⟨k, rfl⟩)).symm

/-- The unique representative in the half-open interval `[0, 1)` for each coset of `ℤ` in `ℝ`,
regarded as a map from the circle `𝕊₁ → ℝ`. -/
def 𝕊₁.repr (x : 𝕊₁) : ℝ :=
  let t := Quotient.out x
  fract t

end

end OnePeriodic
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_MeasureTheory_BorelSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

variable (X : Type*) [TopologicalSpace X]

scoped[Borelize] attribute [instance] borel

theorem borelSpace_borel : @BorelSpace X _ (borel X) :=
  letI := borel X; ⟨rfl⟩

scoped[Borelize] attribute [instance] borelSpace_borel
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_ExistsOfConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open scoped Topology Manifold ContDiff

open Set Function Filter

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

open TopologicalSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem convex_setOf_imp_eq (P : Prop) (y : F) : Convex ℝ {x : F | P → x = y} := by
  by_cases hP : P <;> simp [hP, convex_singleton, convex_univ]

end
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_CutOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open Set Filter

open scoped Manifold Topology ContDiff

-- The bundled versions of this lemma has been merged to mathlib.
-- TODO: add the unbundled version, or (better) re-write sphere-eversion accordingly.
theorem exists_contDiff_one_nhds_of_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hs hd
  ⟨f, f.contMDiff.contDiff, hfs, hft, hf01⟩
end
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RelativeImmersionHPrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge
abbrev Plane := Fin 2 → ℝ
abbrev Vec := EuclideanSpace ℝ (Fin 3)

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
end


