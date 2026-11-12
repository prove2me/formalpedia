-- Prove2me | Definitions.Def_OAIQ249SI003
-- name    : OAIQ249SI003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:04:46.852211+00:00
-- url     : https://prove2.me/theorems/6ceab71c-b97b-4751-bcfa-5589306dc2d3
-- title:
--   Definitions bundle OAIQ249SI003 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 255 declarations of OpenAI's Lean: 136 definitions, 9 inductive types or structures, 2 instances and 108 theorems. The definitions and types are `OAI.ClosedSurfaceR4.CollarVelocity.JetBase`, `OAI.ClosedSurfaceR4.CollarVelocity.jetAngle`, `OAI.ClosedSurfaceR4.CollarVelocity.jetSection`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.coordinate`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.cycleTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.term`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleComponent`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseDifferentialSquare`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedChartWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorChartRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryCrossingSet`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularBoundary`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularBoundaryParam`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularCoordinateDisk`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularCoordinateRegion`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularDiskClosure`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularPhaseDerivative`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularPhaseTangencies`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberFromThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricPairTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseDifferentialFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseDifferentialFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeFirst`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed` and 105 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_AtlasPhases`, `Immersion_ClosedSurface_AtlasWeights`, `Immersion_ClosedSurface_ChartModel`, `Immersion_ClosedSurface_ChartTransition`, `Immersion_ClosedSurface_ComplexPullback`, `Immersion_ClosedSurface_ForcedModes`, `Immersion_ClosedSurface_GoodDirections`, `Immersion_ClosedSurface_GradientBounds`, `Immersion_ClosedSurface_GridBumps`, `Immersion_ClosedSurface_MetricPatches`, `Immersion_ClosedSurface_MetricPullback`, `Immersion_ClosedSurface_MetricTensors`, `Immersion_ClosedSurface_ModeBounds`, `Immersion_ClosedSurface_NormalJets`, `Immersion_ClosedSurface_OscillatoryModel`, `Immersion_ClosedSurface_PhaseCoordinates`, `Immersion_ClosedSurface_PhaseGrid`, `Immersion_ClosedSurface_PhaseMean`, `Immersion_ClosedSurface_PullbackBounds`, `Immersion_ClosedSurface_RealModes`, `Immersion_ClosedSurface_SecondForms`, `Immersion_ClosedSurface_TensorBounds`, `Immersion_ClosedSurface_TensorCoordinates`, `SurfaceImmersion_Atlas_AtlasMetricBounds`, `SurfaceImmersion_Atlas_AtlasSupportedWeights`, `SurfaceImmersion_Atlas_CenteredConvexPhase`, `SurfaceImmersion_Atlas_ChartReadSupport`, `SurfaceImmersion_Atlas_CompactPhasePartition`, `SurfaceImmersion_Atlas_ConvexQuadraticPhase`, `SurfaceImmersion_Atlas_CoordinateQuadraticExpansion`, `SurfaceImmersion_Atlas_GenericAtlasPhases`, `SurfaceImmersion_Atlas_GoodPhaseStability`, `SurfaceImmersion_Atlas_LinearPhaseChart`, `SurfaceImmersion_Atlas_MetricChartReconstruction`, `SurfaceImmersion_Atlas_PhaseBoundaryCurve`, `SurfaceImmersion_Atlas_PhaseChartRealization`, `SurfaceImmersion_Atlas_PhaseSupportCoordinates`, `SurfaceImmersion_Atlas_RealTensorChart`, `SurfaceImmersion_Atlas_SupportedAtlasMetric`, `SurfaceImmersion_Atlas_SupportedTensorChart`, `SurfaceImmersion_Atlas_SurfaceJetCoordinates`, `SurfaceImmersion_Atlas_TensorChartBounds`, `SurfaceImmersion_Atlas_TensorFiberCoordinates`, `SurfaceImmersion_Atlas_TensorPhaseDifferential`, `SurfaceImmersion_Atlas_TensorPlaneCoordinates`, `SurfaceImmersion_Atlas_TensorPlaneWeight`, `SurfaceImmersion_Atlas_VectorChartRead`, `SurfaceImmersion_Correction_ArbitraryPhasePolynomial`, `SurfaceImmersion_Correction_BundleSmoothing`, `SurfaceImmersion_Correction_CircularSmoothingAtlas`, `SurfaceImmersion_Correction_CompactMeanBudgets`, `SurfaceImmersion_Correction_PolynomialModeResidual`, `SurfaceImmersion_Correction_PolynomialSolveData`, `SurfaceImmersion_Correction_SmoothPrimitiveFamily`, `SurfaceImmersion_Correction_SmoothingLocalization`, `SurfaceImmersion_Correction_TensorOperatorSmooth`, `SurfaceImmersion_Correction_TensorSmoothing`, `SurfaceImmersion_Geometry_ManifoldMetricTensor`, `SurfaceImmersion_Geometry_RestoredMetricTensor`, `SurfaceImmersion_Geometry_SplitSupportedBounds`, `SurfaceImmersion_Geometry_SplitSupportedTarget`, `SurfaceImmersion_Geometry_UnperturbedSolverScale`, `SurfaceImmersion_Geometry_VectorReadDifferential`, `SurfaceImmersion_Primitive_CircularBoundaryParam`, `SurfaceImmersion_Primitive_CircularBoundaryTangencies`, `SurfaceImmersion_Primitive_CircularFlatBump`, `SurfaceImmersion_Primitive_CircularPhaseBoundaryCurve`, `SurfaceImmersion_Primitive_CircularPhaseDependence`, `SurfaceImmersion_Primitive_FiniteBoundaryCrossingSets`, `SurfaceImmersion_Primitive_JetVelocityCoordinates`, `SurfaceImmersion_Primitive_JetVelocityLoop`, `SurfaceImmersion_Primitive_SpatialLoopAmplitude`, `SurfaceImmersion_Primitive_SurfaceVelocityFamily`, `SurfaceImmersion_Primitive_VelocityFrame`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI001` and `OAIQ249SI002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI006`, `OAIQ249SI007`, `OAIQ249SI008` and `OAIQ249SI009`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_circularPhase_frame_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_convex_circular_atlas`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_phaseCoordinatePolynomialOperator_bounds` and `OAI_ClosedSurfaceR4_PhaseGeometry_positive_good_phase_data`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_regular_crosscap_map` and `OAI_ClosedSurfaceR4_PhaseGeometry_positive_good_phase_data`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
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
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set
abbrev Base := ℝ × ℝ

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

abbrev Base := ℝ × ℝ
abbrev Ambient (n : ℕ) := Fin n → ℂ
abbrev Field (n : ℕ) := Base → Ambient n

def dx : Base := (1, 0)
def dy : Base := (0, 1)

def coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Base) (F : Base → E) (p : Base) : E := fderiv ℝ F p v

section Gram
variable {n : ℕ}

def gramDet (X Y : Ambient n) : ℂ := (X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) ^ 2

def liftX (X Y : Ambient n) (ux uy : ℂ) : ℂ :=
  ((Y ⬝ᵥ Y) * ux - (X ⬝ᵥ Y) * uy) / gramDet X Y

def liftY (X Y : Ambient n) (ux uy : ℂ) : ℂ :=
  ((X ⬝ᵥ X) * uy - (X ⬝ᵥ Y) * ux) / gramDet X Y


def tangentLift (X Y : Ambient n) (ux uy : ℂ) : Ambient n :=
  liftX X Y ux uy • X + liftY X Y ux uy • Y


def normalPart (X Y W : Ambient n) : Ambient n :=
  W - tangentLift X Y (X ⬝ᵥ W) (Y ⬝ᵥ W)

end Gram

section CoordinateCalculus
variable {n : ℕ}



def secondForm (G : Field n) (v w : Base) (p : Base) : Ambient n :=
  normalPart (coordDeriv dx G p) (coordDeriv dy G p) (coordDeriv v (coordDeriv w G) p)

def connectionX (G : Field n) (v w : Base) (p : Base) : ℂ :=
  liftX (coordDeriv dx G p) (coordDeriv dy G p)
    (coordDeriv dx G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)
    (coordDeriv dy G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)

def connectionY (G : Field n) (v w : Base) (p : Base) : ℂ :=
  liftY (coordDeriv dx G p) (coordDeriv dy G p)
    (coordDeriv dx G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)
    (coordDeriv dy G p ⬝ᵥ coordDeriv v (coordDeriv w G) p)

end CoordinateCalculus

section Elimination
variable {n : ℕ}


def goodSecond (G : Field n) : Field n := secondForm G dy dy

def secondRatio (G : Field n) (v w : Base) (p : Base) : ℂ :=
  (secondForm G v w p ⬝ᵥ goodSecond G p) / (goodSecond G p ⬝ᵥ goodSecond G p)


end Elimination

section SmoothFormulas
variable {n : ℕ}

lemma contDiffAt_coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Base → E} {p : Base} (hG : ContDiffAt ℝ ∞ G p) (v : Base) :
    ContDiffAt ℝ ∞ (coordDeriv v G) p :=
  (hG.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const

end SmoothFormulas

end ClosedSurfaceR4.SmallModes

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



structure ModeDomain (G : Field n) (U : Set Base) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ G U
  determinant : ∀ p ∈ U, gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0
  good : ∀ p ∈ U, goodSecond G p ⬝ᵥ goodSecond G p ≠ 0


structure ModeCoefficientBound (G : Field n) (U : Set Base) (s : ℝ) (m : ℕ) (K : ℝ) : Prop where
  xxX : WeightedBound U s m K (connectionX G dx dx)
  xxY : WeightedBound U s m K (connectionY G dx dx)
  xyX : WeightedBound U s m K (connectionX G dx dy)
  xyY : WeightedBound U s m K (connectionY G dx dy)
  yyX : WeightedBound U s m K (connectionX G dy dy)
  yyY : WeightedBound U s m K (connectionY G dy dy)
  ratioxx : WeightedBound U s m K (secondRatio G dx dx)
  ratioxy : WeightedBound U s m K (secondRatio G dx dy)



structure FullModeCoefficientBound (G : Field n) (U : Set Base) (s : ℝ) (m : ℕ) (K : ℝ) :
    Prop extends ModeCoefficientBound G U s m K where
  secondxx : WeightedBound U s m K (secondForm G dx dx)
  secondxy : WeightedBound U s m K (secondForm G dx dy)


def tangentDualX (G : Field n) : Field n := fun p =>
  tangentLift (coordDeriv dx G p) (coordDeriv dy G p) 1 0

def tangentDualY (G : Field n) : Field n := fun p =>
  tangentLift (coordDeriv dx G p) (coordDeriv dy G p) 0 1

def normalDual (G : Field n) : Field n := fun p =>
  (goodSecond G p ⬝ᵥ goodSecond G p)⁻¹ • goodSecond G p



structure ReconstructionCoefficientBound (G : Field n) (U : Set Base) (s : ℝ) (m : ℕ) (K : ℝ) :
    Prop extends FullModeCoefficientBound G U s m K where
  dualx : WeightedBound U s m K (tangentDualX G)
  dualy : WeightedBound U s m K (tangentDualY G)
  dualn : WeightedBound U s m K (normalDual G)

end Quantitative
end ClosedSurfaceR4.SmallModes

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

lemma contDiffOn_coordDeriv_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Base} (hU : IsOpen U) {f : Base → E} (hf : ContDiffOn ℝ ∞ f U) (v : Base) :
    ContDiffOn ℝ ∞ (coordDeriv v f) U := by
  intro p hp
  exact (contDiffAt_coordDeriv ((hf p hp).contDiffAt (hU.mem_nhds hp)) v).contDiffWithinAt


end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates
abbrev RVec (n : ℕ) := Fin n → ℝ
abbrev RField (n : ℕ) := Base → RVec n

def complexifyCLM (n : ℕ) : RVec n →L[ℝ] Ambient n :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

def complexify {n : ℕ} (X : RVec n) : Ambient n := complexifyCLM n X

@[simp] lemma complexify_apply {n : ℕ} (X : RVec n) (i : Fin n) : complexify X i = (X i : ℂ) := rfl

def realNormalPart (X Y W : RVec 4) : RVec 4 :=
  W - (((Y ⬝ᵥ Y) * (X ⬝ᵥ W) - (X ⬝ᵥ Y) * (Y ⬝ᵥ W)) /
    NormalFrame.gramDet X Y) • X -
    (((X ⬝ᵥ X) * (Y ⬝ᵥ W) - (X ⬝ᵥ Y) * (X ⬝ᵥ W)) /
    NormalFrame.gramDet X Y) • Y

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



def secondQuadratic {n : ℕ} (B : Fin 3 → RVec n) (v : Base) : RVec n :=
  v.1 ^ 2 • B 0 + (2 * v.1 * v.2) • B 1 + v.2 ^ 2 • B 2


def Good {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) : Prop :=
  ξ ≠ 0 ∧ secondQuadratic B (-ξ.2, ξ.1) ≠ 0

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.RootMean ClosedSurfaceR4.WeightedEstimates
open Set



def firstDirection : Fin 3 → Base := ![dx, dx, dy]
def secondDirection : Fin 3 → Base := ![dx, dy, dy]

def evaluate (A : Tensor) (v w : Base) : ℝ :=
  A 0 * v.1 * w.1 + A 1 * (v.1 * w.2 + v.2 * w.1) + A 2 * v.2 * w.2


def pullback (J : Base →L[ℝ] Base) : Tensor →L[ℝ] Tensor :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A i => evaluate A (J (firstDirection i)) (J (secondDirection i))
    map_add' := by intro A B; ext i; simp only [evaluate, Pi.add_apply]; ring
    map_smul' := by intro c A; ext i; simp only [evaluate, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def pullbackField (χ : Base → Base) (p : Base) : Tensor →L[ℝ] Tensor :=
  pullback (fderiv ℝ χ p)


end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set


def realSecondForm (F : RField 4) (v w : Base) (p : Base) : RVec 4 :=
  realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v (coordDeriv w F) p)

def realSecondTensor (F : RField 4) (p : Base) : Fin 3 → RVec 4 :=
  ![realSecondForm F dx dx p, realSecondForm F dx dy p, realSecondForm F dy dy p]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


def planeCoordinates : Plane ≃L[ℝ] Base :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.piFinTwo ℝ (fun _ => ℝ))
def spaceCoordinates : Space ≃L[ℝ] RVec 4 := EuclideanSpace.equiv (Fin 4) ℝ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def coordinateDomain (p : M) : Set Base :=
  planeCoordinates.symm ⁻¹' (extChartAt planeModel p).target

def coordinateMap (F : M → Space) (p : M) : RField 4 :=
  spaceCoordinates ∘ F ∘ (extChartAt planeModel p).symm ∘ planeCoordinates.symm

lemma spaceCoordinates_dot (v w : Space) :
    spaceCoordinates v ⬝ᵥ spaceCoordinates w = inner ℝ v w := by
  simp [spaceCoordinates, dotProduct, PiLp.inner_apply, mul_comm]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPullback
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def coordinateInverse (p : M) : Base → M :=
  (extChartAt planeModel p).symm ∘ planeCoordinates.symm

lemma coordinateInverse_smoothOn (p : M) :
    ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ (coordinateInverse p) (coordinateDomain p) := by
  exact (contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p).comp
    planeCoordinates.symm.contDiff.contMDiff.contMDiffOn (fun x hx => hx)

def metricPullback (g : SmoothMetric M) (φ : Base → M) (x v w : Base) : ℝ :=
  g.inner (φ x) (mfderiv 𝓘(ℝ, Base) planeModel φ x v)
    (mfderiv 𝓘(ℝ, Base) planeModel φ x w)

def coordinateMetric (g : SmoothMetric M) (p : M) (x : Base) : PhaseMean.Tensor :=
  fun i => metricPullback g (coordinateInverse p) x
    (PhaseMean.firstDirection i) (PhaseMean.secondDirection i)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

abbrev RealTwoJet := Fin 5 → RVec 4

def realTwoJet (F : RField 4) (p : Base) : RealTwoJet :=
  ![coordDeriv dx F p, coordDeriv dy F p, coordDeriv dx (coordDeriv dx F) p,
    coordDeriv dx (coordDeriv dy F) p, coordDeriv dy (coordDeriv dy F) p]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPatches
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

def chartCoordinates (p : M) : M → Base := planeCoordinates ∘ chartAt Plane p

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def coordinateChart (p : M) : OpenPartialHomeomorph M SmallModes.Base :=
  (chartAt Plane p).trans planeCoordinates.toHomeomorph.toOpenPartialHomeomorph

lemma coordinateChart_source (p : M) :
    (coordinateChart p).source = (chartAt Plane p).source := by
  simp [coordinateChart]

lemma coordinateChart_symm_apply (p : M) (x : SmallModes.Base) :
    (coordinateChart p).symm x = coordinateInverse p x := by
  simp [coordinateChart,coordinateInverse,planeModel]

lemma coordinateChart_target (p : M) :
    (coordinateChart p).target = coordinateDomain p := by
  simp [coordinateChart,coordinateDomain,planeModel]

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_symm_smoothOn (p : M) :
    ContMDiffOn 𝓘(ℝ,SmallModes.Base) planeModel ∞ (coordinateChart p).symm (coordinateChart p).target := by
  have he : ((coordinateChart p).symm : SmallModes.Base → M) = coordinateInverse p := by
    funext x; exact coordinateChart_symm_apply p x
  rw [he,coordinateChart_target]
  exact coordinateInverse_smoothOn p



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


def phaseLinear (ξ : SmallModes.Base) : SmallModes.Base →L[ℝ] ℝ :=
  ξ.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ξ.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

def atlasPhase (p : M) (ξ : SmallModes.Base) : M → ℝ := phaseLinear ξ ∘ coordinateChart p


def phaseDerivative (f : SmallModes.Base → ℝ) (x : SmallModes.Base) : SmallModes.Base :=
  (fderiv ℝ f x dx,fderiv ℝ f x dy)



def atlasPhaseCovector (q p : M) (ξ : SmallModes.Base) (a : M) : SmallModes.Base :=
  phaseDerivative (atlasPhase q ξ ∘ (coordinateChart p).symm) (coordinateChart p a)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

def gridBump : ContDiffBump (0 : Base) := ⟨1, 2, by norm_num, by norm_num⟩

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasWeights
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]

def atlasSecondTensor (F : M → Space) (p a : M) : Fin 3 → RVec 4 :=
  realSecondTensor (coordinateMap F p) (coordinateChart p a)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedModes
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
open ClosedSurfaceR4.QuadraticMean (realPartCLM)


def realMetric {n : ℕ} (F : RField n) (v w p : Base) : ℝ :=
  coordDeriv v F p ⬝ᵥ coordDeriv w F p

def realMetricTensor {n : ℕ} (F : RField n) : Base → Fin 3 → ℝ :=
  fun p => ![realMetric F dx dx p, realMetric F dx dy p, realMetric F dy dy p]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realMetricTensor_apply {n : ℕ} (F : RField n) (p : Base) (i : Fin 3) :
    realMetricTensor F p i = realMetric F (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorCoordinates
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
open ClosedSurfaceR4.PhaseMean

lemma base_decomposition (v : Base) : v = v.1 • dx + v.2 • dy := by
  ext <;> simp [dx, dy]

lemma derivative_base_decomposition {n : ℕ} (F : RField n) (p v : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  unfold coordDeriv
  conv_lhs => rw [base_decomposition v]
  simp only [map_add, map_smul]

lemma evaluate_realMetricTensor {n : ℕ} (F : RField n) (p v w : Base) :
    evaluate (realMetricTensor F p) v w = realMetric F v w p := by
  rw [realMetric, derivative_base_decomposition F p v, derivative_base_decomposition F p w]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold evaluate
  simp only [realMetricTensor_apply, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, realMetric]
  rw [dotProduct_comm (coordDeriv dy F p) (coordDeriv dx F p)]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ComplexPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base dx dy)
open ClosedSurfaceR4.RealModes (base_decomposition)

def complexEvaluate (A : ComplexTensor) (v w : Base) : ℂ :=
  A 0 * (v.1 : ℂ) * (w.1 : ℂ) +
    A 1 * ((v.1 : ℂ) * (w.2 : ℂ) + (v.2 : ℂ) * (w.1 : ℂ)) +
    A 2 * (v.2 : ℂ) * (w.2 : ℂ)



def complexPullback (J : Base →L[ℝ] Base) : ComplexTensor →L[ℂ] ComplexTensor :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A i => complexEvaluate A (J (firstDirection i)) (J (secondDirection i))
    map_add' := by intro A B; ext i; simp only [complexEvaluate, Pi.add_apply]; ring
    map_smul' := by intro c A; ext i; simp only [complexEvaluate, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]; ring }

def complexPullbackField (χ : Base → Base) (p : Base) : ComplexTensor →L[ℂ] ComplexTensor :=
  complexPullback (fderiv ℝ χ p)

lemma complexPullback_apply (J : Base →L[ℝ] Base) (A : ComplexTensor) (i : Fin 3) :
    complexPullback J A i = complexEvaluate A (J (firstDirection i)) (J (secondDirection i)) := rfl

lemma complexEvaluate_pullback (J : Base →L[ℝ] Base) (A : ComplexTensor) (v w : Base) :
    complexEvaluate (complexPullback J A) v w = complexEvaluate A (J v) (J w) := by
  have hv : J v = v.1 • J dx + v.2 • J dy := by
    conv_lhs => rw [base_decomposition v]
    simp only [map_add, map_smul]
  have hw : J w = w.1 • J dx + w.2 • J dy := by
    conv_lhs => rw [base_decomposition w]
    simp only [map_add, map_smul]
  rw [hv, hw]
  simp only [complexEvaluate, complexPullback_apply, firstDirection, secondDirection,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

lemma complexPullback_comp (J K : Base →L[ℝ] Base) (A : ComplexTensor) :
    complexPullback J (complexPullback K A) = complexPullback (K.comp J) A := by
  ext i
  rw [complexPullback_apply, complexEvaluate_pullback, complexPullback_apply]
  rfl

lemma complexPullback_id (A : ComplexTensor) :
    complexPullback (ContinuousLinearMap.id ℝ Base) A = A := by
  ext i
  fin_cases i <;> simp [complexPullback_apply, complexEvaluate, firstDirection,
    secondDirection, dx, dy]

lemma realPart_complexPullback (J : Base →L[ℝ] Base) (A : ComplexTensor) :
    ClosedSurfaceR4.QuadraticMean.realPart (complexPullback J A) = pullback J (ClosedSurfaceR4.QuadraticMean.realPart A) := by
  ext i
  change (complexEvaluate A _ _).re = evaluate (ClosedSurfaceR4.QuadraticMean.realPart A) _ _
  simp [complexEvaluate, evaluate, ClosedSurfaceR4.QuadraticMean.realPart, Complex.mul_re]

lemma complexPullbackField_inverse {χ e : Base → Base} {p : Base}
    (hχ : DifferentiableAt ℝ χ p) (he : DifferentiableAt ℝ e (χ p))
    (hinv : e ∘ χ =ᶠ[nhds p] id) (A : ComplexTensor) :
    complexPullbackField χ p (complexPullbackField e (χ p) A) = A := by
  unfold complexPullbackField
  rw [complexPullback_comp, ← fderiv_comp p he hχ,
    hinv.fderiv_eq, fderiv_id, complexPullback_id]



end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base Field coordDeriv)

lemma contDiffOn_complexEvaluate {U : Set Base} {A : Base → ComplexTensor}
    {v w : Base → Base} (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U)
    (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun p => complexEvaluate (A p) (v p) (w p)) U := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have h0 := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1 := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2 := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  exact (h0.add h1).add h2

lemma contDiffOn_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base}
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U) :
    ContDiffOn ℝ ∞ (fun p => complexPullbackField e p (A p)) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_complexEvaluate hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i))


def coordinateTarget (e : Base → Base) (A : Base → ComplexTensor) : Base → ComplexTensor :=
  fun p => complexPullbackField e p (A (e p))

lemma contDiffOn_coordinateTarget {U V : Set Base} (hV : IsOpen V)
    {A : Base → ComplexTensor} {e : Base → Base}
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e V) (heU : Set.MapsTo e V U) :
    ContDiffOn ℝ ∞ (coordinateTarget e A) V :=
  contDiffOn_complexPullbackField_apply hV (hA.comp he heU) he

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes Set


def phaseCoframe (ξ : Base) : Base →ₗ[ℝ] Base where
  toFun p := (ξ.1 * p.1 + ξ.2 * p.2, -ξ.2 * p.1 + ξ.1 * p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

def phaseCoframeInv (ξ : Base) : Base →ₗ[ℝ] Base where
  toFun p := ((ξ.1 * p.1 - ξ.2 * p.2) / (ξ.1^2 + ξ.2^2),
    (ξ.2 * p.1 + ξ.1 * p.2) / (ξ.1^2 + ξ.2^2))
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

lemma covector_length_sq_pos {ξ : Base} (hξ : ξ ≠ 0) : 0 < ξ.1^2 + ξ.2^2 := by
  by_contra h
  have ha : ξ.1 = 0 := by nlinarith [sq_nonneg ξ.1, sq_nonneg ξ.2]
  have hb : ξ.2 = 0 := by nlinarith [sq_nonneg ξ.1, sq_nonneg ξ.2]
  exact hξ (Prod.ext ha hb)

lemma phaseCoframe_left_inv {ξ : Base} (hξ : ξ ≠ 0) :
    Function.LeftInverse (phaseCoframeInv ξ) (phaseCoframe ξ) := by
  intro p
  have hd := (covector_length_sq_pos hξ).ne'
  ext <;> simp only [phaseCoframe, phaseCoframeInv, LinearMap.coe_mk, AddHom.coe_mk] <;>
    field_simp <;> ring

lemma phaseCoframe_right_inv {ξ : Base} (hξ : ξ ≠ 0) :
    Function.RightInverse (phaseCoframeInv ξ) (phaseCoframe ξ) := by
  intro p
  have hd := (covector_length_sq_pos hξ).ne'
  ext <;> simp only [phaseCoframe, phaseCoframeInv, LinearMap.coe_mk, AddHom.coe_mk] <;>
    field_simp <;> ring

def phaseEquiv (ξ : Base) (hξ : ξ ≠ 0) : Base ≃L[ℝ] Base :=
  (LinearEquiv.ofLinearMap (phaseCoframe ξ) (phaseCoframeInv ξ)
    (LinearMap.ext (phaseCoframe_right_inv hξ))
    (LinearMap.ext (phaseCoframe_left_inv hξ))).toContinuousLinearEquiv

@[simp] lemma phaseEquiv_apply (ξ : Base) (hξ : ξ ≠ 0) (p : Base) :
    phaseEquiv ξ hξ p = (ξ.1 * p.1 + ξ.2 * p.2, -ξ.2 * p.1 + ξ.1 * p.2) := rfl

@[simp] lemma phaseEquiv_symm_apply (ξ : Base) (hξ : ξ ≠ 0) (p : Base) :
    (phaseEquiv ξ hξ).symm p = ((ξ.1 * p.1 - ξ.2 * p.2) / (ξ.1^2 + ξ.2^2),
      (ξ.2 * p.1 + ξ.1 * p.2) / (ξ.1^2 + ξ.2^2)) := rfl


end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PullbackBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (complexify)

lemma contDiffOn_complexify {n : ℕ} {U : Set Base} {A : Base → Fin n → ℝ}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun p => complexify (A p)) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hA i)

lemma realPart_complexify {n : ℕ} (A : Fin n → ℝ) :
    QuadraticMean.realPart (complexify A) = A := by ext i; rfl

lemma contDiffOn_pullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → Tensor} {e : Base → Base}
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U) :
    ContDiffOn ℝ ∞ (fun p => pullbackField e p (A p)) U := by
  have hc := (QuadraticMean.realPartCLM 3).contDiff.comp_contDiffOn
    (contDiffOn_complexPullbackField_apply hU (contDiffOn_complexify hA) he)
  simpa only [Function.comp_def, QuadraticMean.realPartCLM_apply,
    complexPullbackField, realPart_complexPullback, realPart_complexify, pullbackField] using hc

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
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
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_realDot {n : ℕ} {U : Set Base} {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (fun p => X p ⬝ᵥ Y p) U := by
  exact ContDiffOn.sum fun i _ => (contDiffOn_pi.mp hX i).mul (contDiffOn_pi.mp hY i)

lemma contDiffOn_realMetricTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X : RField n}
    (hX : ContDiffOn ℝ ∞ X U) : ContDiffOn ℝ ∞ (realMetricTensor X) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realMetricTensor_apply, realMetric]
  exact contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hX _)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingLocalization
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported coordinate representatives for smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_chart (p : M) (ψ : M → ℝ) (f : M → V) {x : M}
    (hx : x ∈ (chart p).source) :
    localize p ψ f (chart p x) = (ψ x) ^ 2 • f x := by
  rw [localize, indicator_of_mem ((chart p).map_source hx), (chart p).left_inv hx]

lemma localize_zero_off_image (p : M) (ψ : M → ℝ) (f : M → V) {x : Base}
    (hx : x ∉ (chart p) '' tsupport ψ) : localize p ψ f x = 0 := by
  by_cases ht : x ∈ (chart p).target
  · have hψ : ψ ((chart p).symm x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact hx ⟨(chart p).symm x, hp, (chart p).right_inv ht⟩
    simp only [localize, indicator_of_mem ht, hψ, zero_pow (by decide : 2 ≠ 0), zero_smul]
  · exact indicator_of_notMem ht _

variable [CompactSpace M]

lemma localize_tsupport (p : M) {ψ : M → ℝ} (hψ : tsupport ψ ⊆ (chart p).source)
    (f : M → V) : tsupport (localize p ψ f) ⊆ (chart p) '' tsupport ψ := by
  have hK : IsCompact ((chart p) '' tsupport ψ) :=
    (isClosed_tsupport ψ).isCompact.image_of_continuousOn ((chart p).continuousOn.mono hψ)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (localize_zero_off_image p ψ f hn)

variable [IsManifold planeModel ∞ M]

/-- Extension by zero is smooth because the localization support lies in a
compact subset of the chart target. -/
lemma localize_smooth (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f) : ContDiff ℝ ∞ (localize p ψ f) := by
  have hlocal : ContDiffOn ℝ ∞
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target := by
    exact (((hψ.comp_contMDiffOn (chart_symm_smooth p)).pow 2).smul
      (hf.comp_contMDiffOn (chart_symm_smooth p))).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  case neg => exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)
  have hxI := localize_tsupport p hsupp f hx
  obtain ⟨y, hy, hxy⟩ := hxI
  have hxT : x ∈ (chart p).target := hxy ▸ (chart p).map_source (hsupp hy)
  apply (hlocal.contDiffAt ((chart p).open_target.mem_nhds hxT)).congr_of_eventuallyEq
  filter_upwards [(chart p).open_target.mem_nhds hxT] with z hz
  exact indicator_of_mem hz _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual finite-atlas smoothing operator on smooth vector-bundle sections. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

/-- Fiber coordinates, used only on the corresponding base chart. -/
def bundleComponent (i : A.centers) (u : ∀ x, E x) (x : M) : F :=
  (e i).continuousLinearMapAt ℝ x (u x)

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

variable [CompactSpace M]

omit [CompactSpace M] in
lemma bundleRestore_smooth (i : A.centers) {h : Base → F} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (A.bundleRestore e i h x)) := by
  have hsec : ContMDiffOn planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x ((e i).symmL ℝ x (h (chart (i : M) x))))
      (chart (i : M)).source := by
    apply ((e i).contMDiffOn_section_iff (chart (i : M)).open_source (hdomain i)).mpr
    apply (hh.contMDiff.comp_contMDiffOn (chart_smooth (i : M))).congr
    intro x hx
    rw [← (e i).continuousLinearMapAt_apply_of_mem ℝ (hdomain i hx),
      (e i).continuousLinearMapAt_symmL (hdomain i hx)]
    rfl
  exact (A.outer_smooth i).contMDiffOn.smul_section_of_tsupport
    (chart (i : M)).open_source (A.outer_support i) hsec

end SmoothingAtlas
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
open JetPolynomial (Base)

local instance tensorModelNormed_r043b26_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorModelSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorModelComplete_r043b26_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance tensorModelNormed_r043b26_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorModelSpace_r043b26_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorModelComplete_r043b26_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul
variable (A : SmoothingAtlas M)

lemma tensorTriv_domain (i : A.centers) :
    (chart (i : M)).source ⊆ (A.tensorTriv i).baseSet := by
  intro x hx
  unfold tensorTriv CovariantTwoTensor TensorFiber
  rw [hom_trivializationAt_baseSet, hom_trivializationAt_baseSet]
  simp only [TangentBundle.trivializationAt_baseSet, mem_inter_iff]
  exact ⟨by simpa only [chart_source] using hx,
    by simpa only [chart_source] using hx, mem_univ x⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

local instance coordinateFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordinateFiberSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
local instance coordinateFiberGroup : AddCommGroup (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
  coordinateFiberNormed.toAddCommGroup

def planeFirst : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp planeCoordinates.toContinuousLinearMap

def planeSecond : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp planeCoordinates.toContinuousLinearMap

def fiberFromThree : Tensor →L[ℝ] TensorFiber :=
  (ContinuousLinearMap.proj 0).smulRight (planeFirst.smulRight planeFirst) +
  (ContinuousLinearMap.proj 1).smulRight
    (planeFirst.smulRight planeSecond + planeSecond.smulRight planeFirst) +
  (ContinuousLinearMap.proj 2).smulRight (planeSecond.smulRight planeSecond)

lemma fiberFromThree_apply (H : Tensor) (v w : Plane) :
    fiberFromThree H v w = evaluate H (planeCoordinates v) (planeCoordinates w) := by
  simp [fiberFromThree, planeFirst, planeSecond, evaluate]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry )

local instance planeReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance planeReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance planeReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance planeReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

local instance planeReadSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance planeReadSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorPlaneRestore (f : A.centers → SmallModes.Base → Tensor) : ∀ x : M, CovariantTwoTensor x :=
  fun p => ∑ i : A.centers, A.bundleRestore A.tensorTriv i
    (fun y => fiberFromThree (f i (planeCoordinateIsometry y))) p

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart cutoff whose square converts an unweighted tensor
reading into its atlas coordinate component. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance weightPlaneFiberNormed_r043b26_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance weightPlaneDualAdd_r043b26_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul_r043b26_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance weightPlaneSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def planeWeight (i : A.centers) : SmallModes.Base → ℝ :=
  A.chartWeight i ∘ planeCoordinateIsometry.symm

variable [CompactSpace M]

lemma planeWeight_smooth (i : A.centers) : ContDiff ℝ ∞ (A.planeWeight i) :=
  (A.chartWeight_smooth i).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedTensorChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate transport of the symmetric complex tensors used as targets
in the perturbed phase equations. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartPush_zero (f : SupportedField (F := ComplexTensor) K) :
    ∀ y ∈ e.target, y ∉ (chartSupport e K hK : Set SmallModes.Base) →
      coordinateTarget e.symm f y = 0 := by
  intro y hy hn
  simp only [coordinateTarget, chartPush_zero e K hK f y hy hn, map_zero]

def tensorChartPush (f : SupportedField (F := ComplexTensor) K) :
    SupportedField (F := ComplexTensor) (chartSupport e K hK) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
      (chartSupport_subset e K hK)
      (contDiffOn_coordinateTarget e.open_target f.contDiff.contDiffOn hi (fun _ _ => Set.mem_univ _))
      (tensorChartPush_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset (chartSupport e K hK).isCompact.isClosed
      (tensorChartPush_zero e K hK f)))

@[simp] lemma tensorChartPush_apply (f : SupportedField (F := ComplexTensor) K) (y : SmallModes.Base) :
    tensorChartPush e hi K hK f y = e.target.indicator (coordinateTarget e.symm f) y := rfl

def tensorChartPushLM :
    SupportedField (F := ComplexTensor) K →ₗ[ℝ] SupportedField (F := ComplexTensor) (chartSupport e K hK) where
  toFun := tensorChartPush e hi K hK
  map_add' f g := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;>
      simp [tensorChartPush_apply, hy, coordinateTarget, map_add]
  map_smul' c f := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;>
      simp [tensorChartPush_apply, hy, coordinateTarget]

lemma tensorChartPull_zero (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    ∀ x ∈ e.source, x ∉ (K : Set SmallModes.Base) → coordinateTarget e f x = 0 := by
  intro x hx hn
  simp only [coordinateTarget, chartPull_zero e K hK f x hx hn, map_zero]

def tensorChartPull (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    SupportedField (F := ComplexTensor) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_source K.isCompact.isClosed hK
      (contDiffOn_coordinateTarget e.open_source f.contDiff.contDiffOn he (fun _ _ => Set.mem_univ _))
      (tensorChartPull_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset K.isCompact.isClosed
      (tensorChartPull_zero e K hK f)))

@[simp] lemma tensorChartPull_apply (f : SupportedField (F := ComplexTensor) (chartSupport e K hK))
    (x : SmallModes.Base) :
    tensorChartPull e he K hK f x = e.source.indicator (coordinateTarget e f) x := rfl

lemma tensorChartPull_push (f : SupportedField (F := ComplexTensor) K) :
    tensorChartPull e he K hK (tensorChartPush e hi K hK f) = f := by
  apply DFunLike.ext
  intro x
  by_cases hx : x ∈ e.source
  · rw [tensorChartPull_apply, Set.indicator_of_mem hx]
    change complexPullbackField e x (tensorChartPush e hi K hK f (e x)) = f x
    rw [tensorChartPush_apply, Set.indicator_of_mem (e.map_source hx)]
    change complexPullbackField e x (complexPullbackField e.symm (e x) (f (e.symm (e x)))) = f x
    rw [e.left_inv hx]
    apply complexPullbackField_inverse
    · exact (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · exact (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · filter_upwards [e.open_source.mem_nhds hx] with z hz using e.left_inv hz
  · rw [tensorChartPull_apply, Set.indicator_of_notMem hx]
    exact (f.zero_on_compl (fun hk => hx (hK hk))).symm

lemma tensorChartPush_pull (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    tensorChartPush e hi K hK (tensorChartPull e he K hK f) = f := by
  apply DFunLike.ext
  intro y
  by_cases hy : y ∈ e.target
  · rw [tensorChartPush_apply, Set.indicator_of_mem hy]
    change complexPullbackField e.symm y (tensorChartPull e he K hK f (e.symm y)) = f y
    rw [tensorChartPull_apply, Set.indicator_of_mem (e.map_target hy)]
    change complexPullbackField e.symm y (complexPullbackField e (e.symm y) (f (e (e.symm y)))) = f y
    rw [e.right_inv hy]
    apply complexPullbackField_inverse
    · exact (hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · exact (he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · filter_upwards [e.open_target.mem_nhds hy] with z hz using e.right_inv hz
  · rw [tensorChartPush_apply, Set.indicator_of_notMem hy]
    exact (f.zero_on_compl (fun hk => hy (chartSupport_subset e K hK hk))).symm

def tensorChartEquiv :
    SupportedField (F := ComplexTensor) K ≃ₗ[ℝ] SupportedField (F := ComplexTensor) (chartSupport e K hK) where
  toFun := tensorChartPush e hi K hK
  invFun := tensorChartPull e he K hK
  left_inv := tensorChartPull_push e he hi K hK
  right_inv := tensorChartPush_pull e he hi K hK
  map_add' := (tensorChartPushLM e hi K hK).map_add
  map_smul' := (tensorChartPushLM e hi K hK).map_smul

end ClosedSurfaceR4.JetPolynomial

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
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

def chartTensorTransportLM (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (R : SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ComplexTensor) K) :
    SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK) →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (chartSupport e K hK) :=
  (tensorChartEquiv e he hi K hK).toLinearMap.comp
    (R.comp (chartEquiv e he hi K hK).symm.toLinearMap)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RealTensorChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported pullback of real symmetric two-tensors. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open PhaseMean WeightedEstimates
variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts SmallModes.Base)
    (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma realTensorChartPull_zero (f : SupportedField (F := Tensor) (chartSupport e K hK)) :
    ∀ x ∈ e.source, x ∉ (K : Set SmallModes.Base) → pullbackField e x (f (e x)) = 0 := by
  intro x hx hn
  rw [chartPull_zero e K hK f x hx hn, map_zero]

def realTensorChartPull (f : SupportedField (F := Tensor) (chartSupport e K hK)) :
    SupportedField (F := Tensor) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_source K.isCompact.isClosed hK
      (contDiffOn_pullbackField_apply e.open_source (f.contDiff.comp_contDiffOn he) he)
      (realTensorChartPull_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset K.isCompact.isClosed
      (realTensorChartPull_zero e K hK f)))

@[simp] lemma realTensorChartPull_apply
    (f : SupportedField (F := Tensor) (chartSupport e K hK)) (x : SmallModes.Base) :
    realTensorChartPull e he K hK f x =
      e.source.indicator (fun x => pullbackField e x (f (e x))) x := rfl

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialModeResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The forced linear modes for the polynomially perturbed metric operator
are solved to every fixed finite power of the small parameter. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet} {G : Base → Space}

abbrev modeSupport (K : Compacts Base) : Compacts SmallModes.Base :=
  K.map planeCoordinateIsometry planeCoordinateIsometry.continuous

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateQuadraticExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the polynomial quadratic expansion into the same coordinates
and phase labels as the metric quadratic expansion. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ModulatedJets

abbrev coordinatePhase (φ : Base → ℝ) : SmallModes.Base → ℝ := φ ∘ planeCoordinateIsometry.symm

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ArbitraryPhasePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial conjugation estimate and its real realization for an
arbitrary smooth phase, before changing to a first-coordinate chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def phaseCoordinatePolynomialOperator (hO : IsOpen O) (hU : IsOpen U)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ) :
    SupportedField (F := Fin 4 → ℂ) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K) :=
  transportSupportedLM planeCoordinateIsometry K
    (tensorConjugatedLM hO hU P hP hG hQ K hKU hφ τ ε 0)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local-coordinate realization of the polynomial phase operator.
The operator is transported, so no transformed-polynomial assumption is used. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def phaseChartPolynomialOperator (hO : IsOpen O) (hU : IsOpen U)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source) :
    SupportedField (F := Fin 4 → ℂ) (chartSupport e (modeSupport K) hKe) →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (chartSupport e (modeSupport K) hKe) :=
  chartTensorTransportLM e (modeSupport K) hKe he hi
    (phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric and quantitative data for the already constructed finite
polynomial phase solver. The operator bound here is supplied by
`phaseChartPolynomialOperator_bounds`; it concerns the actual transported
polynomial derivative. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

structure PolynomialSolveData {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) (G : Base → Space) (hG : ContDiff ℝ ∞ G)
    (φ : Base → ℝ) (K : Compacts Base) (τ : ℝ) (s : ℝ≥0) where
  U : Set Base
  O : Set LowJet
  openU : IsOpen U
  openO : IsOpen O
  smoothP : ∀ k l, (P k l).SmoothCoeffs O
  mapsG : Set.MapsTo (lowJet G) U O
  supportU : (K : Set Base) ⊆ U
  smoothPhase : ContDiff ℝ ∞ φ
  e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base
  smoothForward : ContDiffOn ℝ ∞ e e.source
  smoothInverse : ContDiffOn ℝ ∞ e.symm e.target
  supportChart : (modeSupport K : Set SmallModes.Base) ⊆ e.source
  phase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x
  smoothMap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm)
  domain : SmallModes.ModeDomain (fun p => RealModes.complexify
    (G (planeCoordinateIsometry.symm (e.symm p)))) e.target
  C : ℕ → ℝ
  D : ℕ → ℝ
  J : ℕ → ℝ
  nonnegC : ∀ m, 0 ≤ C m
  nonnegD : ∀ m, 0 ≤ D m
  oneLEJ : ∀ m, 1 ≤ J m
  coordinates : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
    ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m
  coefficients : ∀ m, SmallModes.ReconstructionCoefficientBound
    (fun p => RealModes.complexify (G (planeCoordinateIsometry.symm (e.symm p))))
    e.target s (m + 1) (C m)
  polynomial : ∀ m Z, supportedWeightedSeminorm (chartSupport e (modeSupport K) supportChart) s m
    (phaseChartPolynomialOperator openO openU P smoothP hG mapsG K supportU smoothPhase
      τ ε e smoothForward smoothInverse supportChart Z) ≤
    ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
      (chartSupport e (modeSupport K) supportChart) s (m + tensorOrder P) Z

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSupportedWeights
attribute [-simp] _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas cutoffs as actual compactly supported fields, and their
transport to a phase chart with the required inverse-frequency factor. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def supportedChartWeight (i : A.centers) : SupportedField (F := ℝ) (A.chartWeightCompact i) :=
  ⟨A.chartWeight i,A.chartWeight_smooth i,by
    intro x hx
    by_cases hxt : x ∈ (chart (i : M)).target
    · change (chart (i : M)).target.indicator
        (fun y => A.weight i ((chart (i : M)).symm y)) x = 0
      rw [indicator_of_mem hxt]
      by_contra hn
      exact hx ⟨(chart (i : M)).symm x,subset_tsupport (A.weight i) hn,(chart (i : M)).right_inv hxt⟩
    · exact indicator_of_notMem hxt _⟩

def supportedPlaneWeight (i : A.centers) :
    SupportedField (F := ℝ) (modeSupport (A.chartWeightCompact i)) :=
  pushSupported planeCoordinateIsometry (A.chartWeightCompact i) (A.supportedChartWeight i)

@[simp] lemma supportedPlaneWeight_apply (i : A.centers) (x : SmallModes.Base) :
    A.supportedPlaneWeight i x = A.planeWeight i x := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPhaseDifferential
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restored rank-one tensor coordinates are the actual differentials of
atlas phases. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry

local instance phaseDifferentialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseDifferentialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance phaseDifferentialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance phaseDifferentialDualSmul_r043b26_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseDifferentialSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseDifferentialSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorComponent_apply (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : Plane) :
    A.bundleComponent A.tensorTriv i u p v w =
      u p ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symm p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symm p w) := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  unfold bundleComponent
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp)]
  unfold tensorTriv
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ ht ht (mem_univ p)]
  simp

lemma tensorComponent_tangentCoordinates (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : TangentSpace planeModel p) :
    A.bundleComponent A.tensorTriv i u p
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
      u p v w := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  rw [A.tensorComponent_apply i u hp]
  rw [← Trivialization.symmL_apply (R := ℝ) _ ht, ← Trivialization.symmL_apply (R := ℝ) _ ht,
    Trivialization.symmL_continuousLinearMapAt _ ht, Trivialization.symmL_continuousLinearMapAt _ ht]

lemma tensorRestore_apply (i : A.centers) (f : JetPolynomial.Base → TensorFiber)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : TangentSpace planeModel p) :
    A.bundleRestore A.tensorTriv i f p v w = A.outer i p *
      f (chart (i : M) p)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) := by
  rw [← A.tensorComponent_tangentCoordinates i (A.bundleRestore A.tensorTriv i f) hp]
  have hc : A.bundleComponent A.tensorTriv i (A.bundleRestore A.tensorTriv i f) p =
      A.outer i p • f (chart (i : M) p) := by
    change (A.tensorTriv i).continuousLinearMapAt ℝ p
      (A.outer i p • (A.tensorTriv i).symmL ℝ p (f (chart (i : M) p))) = _
    rw [map_smul, (A.tensorTriv i).continuousLinearMapAt_symmL (A.tensorTriv_domain i hp)]
  rw [hc]
  rfl

lemma coordinateChart_tangentCoordinates (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ, SmallModes.Base) (coordinateChart (i : M)) p =
      planeCoordinates.toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hp' : p ∈ (chartAt Plane (i : M)).source := by simpa only [chart_source] using hp
  have hcs : ContMDiffOn planeModel planeModel ∞ (chartAt Plane (i : M))
      (chartAt Plane (i : M)).source := contMDiffOn_chart
  have hc := (hcs p hp').contMDiffAt ((chartAt Plane (i : M)).open_source.mem_nhds hp')
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp']
  change mfderiv planeModel 𝓘(ℝ, SmallModes.Base) (planeCoordinates ∘ chartAt Plane (i : M)) p =
    planeCoordinates.toContinuousLinearMap.comp (mfderiv planeModel planeModel (chartAt Plane (i : M)) p)
  rw [mfderiv_comp p
    (((planeCoordinates.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt)
    (hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)), mfderiv_eq_fderiv, planeCoordinates.fderiv]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metric and linearized metric of supported restored displacements
in the original atlas coordinates. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4
open FiniteOrderSmoothing JetPolynomial

lemma euclidean_metric_coordinate_value (f : SmallModes.Base → Space)
    {y : SmallModes.Base} (hf : DifferentiableAt ℝ f y) (v w : SmallModes.Base) :
    PhaseMean.evaluate (RealModes.realMetricTensor (spaceCoordinates ∘ f) y) v w =
      inner ℝ (fderiv ℝ f y v) (fderiv ℝ f y w) := by
  rw [RealModes.evaluate_realMetricTensor]
  simp only [RealModes.realMetric, SmallModes.coordDeriv]
  rw [(spaceCoordinates.hasFDerivAt.comp y hf.hasFDerivAt).fderiv]
  exact spaceCoordinates_dot _ _

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance metricTensorFiberNormed_r043b26_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricTangentNormed (p : M) : NormedAddCommGroup (TangentSpace planeModel p) :=
  inferInstanceAs (NormedAddCommGroup Plane)
local instance metricTangentSpace (p : M) : NormedSpace ℝ (TangentSpace planeModel p) :=
  inferInstanceAs (NormedSpace ℝ Plane)

local instance metricTensorDualAdd_r043b26_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricTensorDualSmul_r043b26_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def metricPairTensor (F U : M → Space) (p : M) : CovariantTwoTensor p :=
  (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).bilinearComp
    (E' := TangentSpace planeModel p) (F' := TangentSpace planeModel p)
    (σ₁' := RingHom.id ℝ) (σ₂' := RingHom.id ℝ)
    (σ₁₃' := RingHom.id ℝ) (σ₂₃' := RingHom.id ℝ)
    (surfaceDifferential F p) (surfaceDifferential U p)

def inducedTensor (F : M → Space) (p : M) : CovariantTwoTensor p := metricPairTensor F F p

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RestoredMetricTensor
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring a compactly supported Euclidean displacement restores its
actual metric tensor, with no extra terms from the outer atlas cutoff. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance restoredMetricFiberNormed_r043b26_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredMetricFiberSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance restoredMetricDualAdd_r043b26_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredMetricDualSmul_r043b26_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance restoredMetricSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredMetricSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma plane_chart_differential (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (surfaceDifferential (chart (i : M)) p) =
      planeCoordinates.toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) ∘ chart (i : M) =
      coordinateChart (i : M) := by
    funext x
    rfl
  have hd := mfderiv_comp p
    ((planeCoordinateIsometry.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt
    (hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [he, mfderiv_eq_fderiv] at hd
  change surfaceDifferential (coordinateChart (i : M)) p =
    (fderiv ℝ planeCoordinateIsometry (chart (i : M) p)).comp
      (surfaceDifferential (chart (i : M)) p) at hd
  have hi : fderiv ℝ (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base)
      (chart (i : M) p) = planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap :=
    planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [hi] at hd
  exact hd.symm.trans (A.coordinateChart_tangentCoordinates i hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_VectorChartRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual global smooth chart representatives. On the original phase
support they preserve every derivative, including at the support boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma chartWeight_tsupport (i : A.centers) :
    tsupport (A.chartWeight i) = (A.chartWeightCompact i : Set JetPolynomial.Base) := by
  apply Subset.antisymm (A.supportedChartWeight i).tsupport_subset
  rintro x ⟨p,hp,rfl⟩
  have hc : ContinuousAt (chart (i : M)) p :=
    ((chart (i : M)).continuousOn p (A.weight_support i hp)).continuousAt
      ((chart (i : M)).open_source.mem_nhds (A.weight_support i hp))
  have hh := mem_closure_image hc hp
  apply closure_mono _ hh
  rintro y ⟨q,hq,rfl⟩
  change A.weight i q ≠ 0 at hq
  have hs := A.weight_support i (subset_tsupport (A.weight i) hq)
  change A.chartWeight i (chart (i : M) q) ≠ 0
  simpa only [chartWeight,indicator_of_mem ((chart (i : M)).map_source hs),
    (chart (i : M)).left_inv hs] using hq

def vectorChartRead (i : A.centers) (F : M → V) : JetPolynomial.Base → V :=
  localize (i : M) (A.outer i) F

def vectorPlaneRead (i : A.centers) (F : M → V) : SmallModes.Base → V :=
  A.vectorChartRead i F ∘ planeCoordinateIsometry.symm

lemma vectorChartRead_smooth (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) : ContDiff ℝ ∞ (A.vectorChartRead i F) :=
  localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) hF

lemma vectorPlaneRead_smooth (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) : ContDiff ℝ ∞ (A.vectorPlaneRead i F) :=
  (A.vectorChartRead_smooth i hF).comp planeCoordinateIsometry.symm.contDiff

lemma vectorChartRead_on_support (i : A.centers) (F : M → V)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i F x = F ((chart (i : M)).symm x) := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [vectorChartRead,localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp,
    (chart (i : M)).left_inv (A.weight_support i hp),one_pow,one_smul]

lemma vectorChartRead_jets (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) (m : ℕ)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (A.vectorChartRead i F) x =
      iteratedFDeriv ℝ m (F ∘ (chart (i : M)).symm) x := by
  have hk : tsupport (A.chartWeight i) ⊆ (chart (i : M)).target := by
    rw [A.chartWeight_tsupport]
    rintro y ⟨p,hp,rfl⟩
    exact (chart (i : M)).map_source (A.weight_support i hp)
  have hg : ContDiffOn ℝ ∞ (F ∘ (chart (i : M)).symm) (chart (i : M)).target :=
    (hF.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  apply iteratedFDeriv_eq_on_tsupport (A.chartWeight_smooth i).continuous
    (chart (i : M)).open_target hk (A.vectorChartRead_smooth i hF).contDiffOn hg
    (fun y hy => A.vectorChartRead_on_support i F (A.chartWeight_tsupport i ▸ hy)) m
  rwa [A.chartWeight_tsupport]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadDifferential
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate representatives recover the actual manifold differential
on each original phase support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_fderiv (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    fderiv ℝ (A.vectorChartRead i F) x = fderiv ℝ (F ∘ (chart (i : M)).symm) x := by
  ext v
  have hh := congrArg (fun T => T (fun _ : Fin 1 => v)) (A.vectorChartRead_jets i hF 1 hx)
  simpa only [iteratedFDeriv_one_apply] using hh

lemma vectorChartRead_differential (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    surfaceDifferential F p = (fderiv ℝ (A.vectorChartRead i F) (chart (i : M) p)).comp
      (surfaceDifferential (chart (i : M)) p) := by
  have hs := A.weight_support i hp
  have hx := (chart (i : M)).map_source hs
  have hc := ((chart_smooth (i : M)) p hs).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hs)
  have hi : DifferentiableAt ℝ (F ∘ (chart (i : M)).symm) (chart (i : M) p) :=
    (((hF.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn).contDiffAt
      ((chart (i : M)).open_target.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [A.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩]
  have he : F =ᶠ[𝓝 p] (F ∘ (chart (i : M)).symm) ∘ chart (i : M) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hs] with q hq
    simp only [Function.comp_apply,(chart (i : M)).left_inv hq]
  unfold surfaceDifferential
  rw [he.mfderiv_eq]
  change surfaceDifferential ((F ∘ (chart (i : M)).symm) ∘ chart (i : M)) p = _
  have hm := mfderiv_comp p hi.mdifferentiableAt (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hm
  exact hm

lemma vectorPlaneRead_chain (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) (x : JetPolynomial.Base) :
    (fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry x)).comp
      planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap =
        fderiv ℝ (A.vectorChartRead i F) x := by
  have hh := (((A.vectorChartRead_smooth i hF).differentiable (by simp)
    (planeCoordinateIsometry.symm (planeCoordinateIsometry x))).hasFDerivAt.comp (planeCoordinateIsometry x)
      planeCoordinateIsometry.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  simp only [LinearIsometryEquiv.symm_apply_apply] at hh
  change fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry x) = _ at hh
  rw [hh]
  ext v
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply]

lemma vectorPlaneRead_differential (i : A.centers) {F : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    surfaceDifferential F p =
      (fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p))).comp
        (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (surfaceDifferential (chart (i : M)) p)) := by
  rw [← ContinuousLinearMap.comp_assoc,A.vectorPlaneRead_chain i hF]
  exact A.vectorChartRead_differential i hF hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricChartReconstruction
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the actual global metric from unweighted chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance metricReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance metricReadDualSmul_r043b26_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricReadSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem metric_from_chart_reads {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    A.tensorPlaneRestore (fun i y => (A.planeWeight i y)^2 •
      RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y) = inducedTensor F := by
  funext p
  have he (i : A.centers) :
      A.bundleRestore A.tensorTriv i (fun y =>
        fiberFromThree ((A.planeWeight i (planeCoordinateIsometry y))^2 •
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
            (planeCoordinateIsometry y))) p = (A.weight i p)^2 • inducedTensor F p := by
    ext v w
    by_cases hp : p ∈ (chart (i : M)).source
    · rw [A.tensorRestore_apply i _ hp]
      have hwgt : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = A.weight i p := by
        simp only [planeWeight,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply,
          chartWeight,indicator_of_mem ((chart (i : M)).map_source hp),
          (chart (i : M)).left_inv hp]
      rw [hwgt,map_smul]
      change A.outer i p * ((A.weight i p)^2 * _) = (A.weight i p)^2 * _
      by_cases hw : A.weight i p = 0
      · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero]
      · have hsp := subset_tsupport (A.weight i) hw
        rw [A.outer_one i p hsp,one_mul]
        congr 1
        change fiberFromThree
          (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
            (planeCoordinateIsometry (chart (i : M) p)))
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
          inducedForm F p v w
        rw [fiberFromThree_apply]
        have hd := A.vectorPlaneRead_differential i hF hsp
        rw [A.plane_chart_differential i hp] at hd
        have hv := congrArg (fun L => L v) hd
        have hw' := congrArg (fun L => L w) hd
        simp only [ContinuousLinearMap.comp_apply] at hv hw'
        rw [euclidean_metric_coordinate_value (A.vectorPlaneRead i F)
          ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _)]
        exact congrArg₂ (inner ℝ) hv.symm hw'.symm
    · have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (A.outer_support i h))
      have hw : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (A.weight_support i h))
      simp only [bundleRestore,ho,hw,zero_pow (by decide : 2 ≠ 0),zero_smul,zero_apply]
  change (∑ i : A.centers, A.bundleRestore A.tensorTriv i _ p) = _
  simp_rw [he]
  rw [← Finset.sum_smul,A.partition,one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

local instance metricBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit restricted linear chart used for a nonzero phase covector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def linearPhaseChart (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    OpenPartialHomeomorph Base Base where
  toFun := phaseEquiv ξ hξ
  invFun := (phaseEquiv ξ hξ).symm
  source := U
  target := (phaseEquiv ξ hξ) '' U
  map_source' := fun x hx => ⟨x,hx,rfl⟩
  map_target' := by
    rintro y ⟨x,hx,rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  left_inv' := fun x _ => (phaseEquiv ξ hξ).symm_apply_apply x
  right_inv' := fun x _ => (phaseEquiv ξ hξ).apply_symm_apply x
  open_source := hU
  open_target := (phaseEquiv ξ hξ).isOpenMap U hU
  continuousOn_toFun := (phaseEquiv ξ hξ).continuous.continuousOn
  continuousOn_invFun := (phaseEquiv ξ hξ).symm.continuous.continuousOn

@[simp] lemma linearPhaseChart_source (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    (linearPhaseChart ξ hξ U hU).source = U := rfl

@[simp] lemma linearPhaseChart_target (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    (linearPhaseChart ξ hξ U hU).target = (phaseEquiv ξ hξ) '' U := rfl

@[simp] lemma linearPhaseChart_apply (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U)
    (x : Base) : linearPhaseChart ξ hξ U hU x = phaseEquiv ξ hξ x := rfl

@[simp] lemma linearPhaseChart_symm_apply (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U)
    (x : Base) : (linearPhaseChart ξ hξ U hU).symm x = (phaseEquiv ξ hξ).symm x := rfl

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ConvexQuadraticPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual convex phases used in finite primitive preparation. Their
coordinate covariant Hessians are uniformly positive on a sufficiently
small disk when the metric connection has a fixed bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def convexQuadraticPhase (ell : Base) (L : ℝ) (p : Base) : ℝ :=
  phaseLinear ell p + (L / 2) * (p.1^2 + p.2^2)

/-- A metric value together with its first coordinate derivative. -/
abbrev MetricFirstJet := PhaseMean.Tensor × (Base →L[ℝ] PhaseMean.Tensor)

def metricJetDet (J : MetricFirstJet) : ℝ := J.1 0 * J.1 2 - (J.1 1)^2

/-- The three symmetric Christoffel slots, with values in the coordinate
tangent plane, computed from the metric and its first derivatives. -/
def metricConnectionAt (J : MetricFirstJet) : Fin 3 → Base :=
  let a : Fin 3 → ℝ := ![J.2 dx 0 / 2, J.2 dy 0 / 2, J.2 dy 1 - J.2 dx 2 / 2]
  let b : Fin 3 → ℝ := ![J.2 dx 1 - J.2 dy 0 / 2, J.2 dx 2 / 2, J.2 dy 2 / 2]
  fun i => ((J.1 2 * a i - J.1 1 * b i) / metricJetDet J,
    (J.1 0 * b i - J.1 1 * a i) / metricJetDet J)

def connectionContract (Gamma : Fin 3 → Base) (v w : Base) : Base :=
  (v.1*w.1) • Gamma 0 + (v.1*w.2 + v.2*w.1) • Gamma 1 + (v.2*w.2) • Gamma 2

def coordinateMetricHessian (h : Base → PhaseMean.Tensor) (phi : Base → ℝ)
    (p v w : Base) : ℝ :=
  coordDeriv v (coordDeriv w phi) p -
    phaseLinear (phaseDerivative phi p) (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredConvexPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex phases centered at the actual coordinate center of a circular
patch. The connection is evaluated at the original point, so translation
of the phase does not silently translate the metric. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def centeredConvexPhase (ell : Base) (L : ℝ) (c p : Base) : ℝ :=
  convexQuadraticPhase ell L (p-c)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartReadSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate readings retain the support of the global input. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorPlaneRead_support_on_weight (k : A.centers) (F : M → V)
    {x : SmallModes.Base} (hx : x ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base))
    (hF : x ∈ tsupport (A.vectorPlaneRead k F)) :
    (chart (k : M)).symm (planeCoordinateIsometry.symm x) ∈ tsupport F := by
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hx
  have hr := tsupport_comp_preimage (A.vectorChartRead k F) planeCoordinateIsometry.symm
    planeCoordinateIsometry.symm.continuous hF
  change planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (k : M) p)) ∈
    tsupport (localize (k : M) (A.outer k) F) at hr
  rw [LinearIsometryEquiv.symm_apply_apply] at hr
  obtain ⟨q,⟨hq,hqF⟩,he⟩ := localize_tsupport_inter (k : M) (A.outer_support k) F hr
  have hqp : q = p := (chart (k : M)).injOn (A.outer_support k hq) (A.weight_support k hp) he
  subst q
  simpa only [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv (A.weight_support k hp)]
    using hqF

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhasePartition
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite smooth partitions on the compact set on which a phase correction is
required.  The coefficients have compact support inside the supplied open
phase domains.  These are ordinary partition coefficients, so splitting a
tensor target does not require taking square roots.
-/

noncomputable section

open Set Manifold TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)

/-- A finite smooth partition on a compact target set, with compact supports
subordinate to the prescribed phase domains. -/
structure CompactPhasePartition (ι : Type*) [Fintype ι]
    (K : Set Base) (U : ι → Set Base) where
  weight : ι → Base → ℝ
  smooth : ∀ i, ContDiff ℝ ∞ (weight i)
  nonneg : ∀ i x, 0 ≤ weight i x
  le_one : ∀ i x, weight i x ≤ 1
  compact_support : ∀ i, HasCompactSupport (weight i)
  subordinate : ∀ i, tsupport (weight i) ⊆ U i
  sum_eq_one : ∀ x ∈ K, ∑ i, weight i x = 1

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Set Base} {U : ι → Set Base}

/-- The actual compact topological support of one partition coefficient. -/
def supportCompact (P : CompactPhasePartition ι K U) (i : ι) : Compacts Base :=
  ⟨tsupport (P.weight i), P.compact_support i⟩

@[simp] theorem coe_supportCompact (P : CompactPhasePartition ι K U) (i : ι) :
    (P.supportCompact i : Set Base) = tsupport (P.weight i) := rfl

end CompactPhasePartition

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GenericAtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic centered phases in different surface charts. At crossing points
both differentials are pulled to the same actual tangent chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Countable α] [Countable κ]

def centeredAtlasPhase (q : M) (ell : CurvePlane) (L : ℝ) : M → ℝ :=
  centeredConvexPhase ell L (coordinateChart q q) ∘ coordinateChart q

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact good-phase condition persists under a uniform two-jet perturbation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

def secondTensorFromJet (J : RealTwoJet) : Fin 3 → RVec 4 :=
  ![realNormalPart (J 0) (J 1) (J 2), realNormalPart (J 0) (J 1) (J 3),
    realNormalPart (J 0) (J 1) (J 4)]

@[simp] lemma secondTensorFromJet_realTwoJet (F : RField 4) (p : Base) :
    secondTensorFromJet (realTwoJet F p) = realSecondTensor F p := rfl

end ClosedSurfaceR4.RealModes

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

def normalize (v : Vec) : Vec := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A controlled loop on a neighborhood of the actual second-jet section.
Its translation depends on position alone, so the prescribed turn derivatives
along the original section persist under the joint density construction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

abbrev JetBase := Base × RealTwoJet

def jetSection (F : RField 4) (x : Base) : JetBase := (x, realTwoJet F x)

def jetAngle (ρ : JetBase × ℝ → ℝ) (a A s h : JetBase → ℝ) : JetBase × ℝ → ℝ :=
  PositiveDensity.reparametrize ρ
    (fun z => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceJetCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translate the geometric surface jets to the coordinates used by the
quantitative finite-polynomial construction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceJetCoordinates
open RealModes SmallModes WeightedEstimates

def baseEquiv : JetPolynomial.Base ≃L[ℝ] Base :=
  (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv

@[simp] lemma baseEquiv_apply (p : JetPolynomial.Base) : baseEquiv p = (p 0, p 1) := rfl

@[simp] lemma baseEquiv_zero : baseEquiv (JetPolynomial.coordinateVector 0) = dx := by
  simp [baseEquiv_apply, JetPolynomial.coordinateVector, dx]

@[simp] lemma baseEquiv_one : baseEquiv (JetPolynomial.coordinateVector 1) = dy := by
  simp [baseEquiv_apply, JetPolynomial.coordinateVector, dy]

end ClosedSurfaceR4.SurfaceJetCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Euclidean coordinates for the geometric velocity and the actual ordered
jets used in the finite periodic expansion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetVelocityCoordinates
open RealModes JetPolynomial

def slot (i : Fin 7) (J : LowJet) : RVec 4 := fun a => J (.inr (i, a))

end ClosedSurfaceR4.JetVelocityCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus

def normal (J : LowJet) : RVec 4 := realNormalPart (slot 2 J) (slot 6 J) (slot 1 J)

/-- The actual geometric hypotheses on the second-jet neighborhood. The
first and second derivatives are fixed coordinate projections of that jet. -/
structure Loop (O : TopologicalSpace.Opens LowJet) where
  amplitude : LowJet → ℝ
  smoothAmplitude : ContDiffOn ℝ ∞ amplitude O
  velocity : LowJet × ℝ → RVec 4
  smoothVelocity : ContDiffOn ℝ ∞ velocity (O ×ˢ univ)
  periodic : ∀ J ∈ O, Function.Periodic (fun t => velocity (J, t)) 1
  gram_ne : ∀ J ∈ O, NormalFrame.gramDet (slot 2 J) (slot 6 J) ≠ 0
  nonzero : ∀ J ∈ O, normal J ≠ 0 ∨ amplitude J ≠ 0
  perpY : ∀ J ∈ O, ∀ t, slot 2 J ⬝ᵥ velocity (J, t) = 0
  perpC : ∀ J ∈ O, ∀ t, slot 6 J ⬝ᵥ velocity (J, t) = 0
  length : ∀ J ∈ O, ∀ t, velocity (J, t) ⬝ᵥ velocity (J, t) =
    normal J ⬝ᵥ normal J + amplitude J ^ 2
  mean : ∀ J ∈ O, (∫ t in 0..1, velocity (J, t)) = normal J

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactMeanBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of all numerical mean budgets from compact geometric
margins. The same numerical profiles work at every smaller slow scale. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates

lemma reconstruction_shrink_scale {G : Field 4} {U : Set SmallModes.Base}
    {s t C : ℝ} {m : ℕ} (h : ReconstructionCoefficientBound G U s m C)
    (ht : 0 ≤ t) (hts : t ≤ s) : ReconstructionCoefficientBound G U t m C :=
  ⟨⟨⟨h.xxX.shrink_scale ht hts,h.xxY.shrink_scale ht hts,
    h.xyX.shrink_scale ht hts,h.xyY.shrink_scale ht hts,
    h.yyX.shrink_scale ht hts,h.yyY.shrink_scale ht hts,
    h.ratioxx.shrink_scale ht hts,h.ratioxy.shrink_scale ht hts⟩,
    h.secondxx.shrink_scale ht hts,h.secondxy.shrink_scale ht hts⟩,
    h.dualx.shrink_scale ht hts,h.dualy.shrink_scale ht hts,h.dualn.shrink_scale ht hts⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnperturbedSolverScale
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed geometric metric solver works at every smaller slow scale.
Its geometry and coefficient profiles do not depend on the frequency. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean SmallModes

lemma phaseChartPolynomialOperator_zero {n : ℕ} {U : Set Base} {O : Set LowJet}
    {G : Base → Space} (hO : IsOpen O) (hU : IsOpen U)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source) :
    phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ 0 e he hi hKe = 0 := by
  have hz : tensorConjugatedLM hO hU P hP hG hQ K hKU hφ τ 0 0 = 0 := by
    ext Z x k
    simp [tensorConjugatedLM,tupleSupportedLM,conjugatedLM]
    rfl
  simp only [phaseChartPolynomialOperator,phaseCoordinatePolynomialOperator,hz,
    transportSupportedLM,chartTensorTransportLM,LinearMap.zero_comp,LinearMap.comp_zero]

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ} {K : Compacts Base}

/-- Only the numerical scale changes; the actual chart and inverse are fixed. -/
def atUnperturbedScale (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : PolynomialSolveData P 0 G hG φ K τ s where
  U := c.U
  O := c.O
  openU := c.openU
  openO := c.openO
  smoothP := c.smoothP
  mapsG := c.mapsG
  supportU := c.supportU
  smoothPhase := c.smoothPhase
  e := c.e
  smoothForward := c.smoothForward
  smoothInverse := c.smoothInverse
  supportChart := c.supportChart
  phase := c.phase
  smoothMap := c.smoothMap
  domain := c.domain
  C := c.C
  D := fun _ => 0
  J := c.J
  nonnegC := c.nonnegC
  nonnegD := fun _ => le_rfl
  oneLEJ := c.oneLEJ
  coordinates := c.coordinates
  coefficients := fun m => reconstruction_shrink_scale (c.coefficients m) s.coe_nonneg hs
  polynomial := by
    intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp only [LinearMap.zero_apply,map_zero,zero_div,zero_mul,le_refl]

@[simp] lemma atUnperturbedScale_e (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : (c.atUnperturbedScale τ s hs).e = c.e := rfl

@[simp] lemma atUnperturbedScale_C (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : (c.atUnperturbedScale τ s hs).C = c.C := rfl

@[simp] lemma atUnperturbedScale_J (c : PolynomialSolveData P 0 G hG φ K 1 1)
    (τ : ℝ) (s : ℝ≥0) (hs : s ≤ 1) : (c.atUnperturbedScale τ s hs).J = c.J := rfl

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseSupportCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer compact phase supports between the two plane coordinate conventions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def jetSupport (K : Compacts SmallModes.Base) : Compacts Base :=
  K.map planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous

@[simp] lemma modeSupport_jetSupport (K : Compacts SmallModes.Base) :
    modeSupport (jetSupport K) = K := by
  apply SetLike.coe_injective
  change planeCoordinateIsometry '' (planeCoordinateIsometry.symm '' (K : Set SmallModes.Base)) = K
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    simpa only [planeCoordinateIsometry.apply_symm_apply] using hz
  · intro hx
    exact ⟨planeCoordinateIsometry.symm x,⟨x,hx,rfl⟩,
      planeCoordinateIsometry.apply_symm_apply x⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The function is unchanged; only its compact-support index is transferred. -/
def onModeSupport (K : Compacts SmallModes.Base) (f : SupportedField (F := E) K) :
    SupportedField (F := E) (modeSupport (jetSupport K)) :=
  ⟨f, f.contDiff, fun x hx => f.zero_on_compl (by simpa only [modeSupport_jetSupport] using hx)⟩

@[simp] lemma onModeSupport_apply (K : Compacts SmallModes.Base)
    (f : SupportedField (F := E) K) (x : SmallModes.Base) : onModeSupport K f x = f x := rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedTarget
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Split an actual smooth compactly supported target using the finite smooth
phase partition.  Every piece is a supported smooth field on a compact subset
of its phase domain, and the sum of the pieces is the original target.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)
open JetPolynomial (SupportedField)
open PhaseMean (ComplexTensor)

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Each target piece is supported both where the target was supported and
where its partition coefficient is supported. -/
def pieceSupport (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    Compacts Base :=
  ⟨(K : Set Base) ∩ tsupport (P.weight i),
    K.isCompact.inter_right (isClosed_tsupport _)⟩

@[simp] theorem coe_pieceSupport (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) = (K : Set Base) ∩ tsupport (P.weight i) := rfl

/-- The piece is constructed by ordinary scalar multiplication of the target. -/
def splitSupported (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (i : ι) : SupportedField (F := F) (P.pieceSupport i) :=
  ContDiffMapSupportedIn.of_support_subset ((P.smooth i).smul A.contDiff)
    (subset_closure.trans (fun _x hx =>
      ⟨A.tsupport_subset (tsupport_smul_subset_right (P.weight i) A hx),
        tsupport_smul_subset_left (P.weight i) A hx⟩))

@[simp] theorem splitSupported_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (i : ι) (x : Base) :
    P.splitSupported A i x = P.weight i x • A x := rfl

end CompactPhasePartition

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite-order bounds for the actual partition split.  A fixed partition has
bounded derivatives of every fixed order.  Consequently the split costs a
constant depending only on that partition and the order, uniformly over all
short scales at most one and linearly in the target seminorm.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

open SmallModes (Base)
open JetPolynomial (SupportedField supportedWeightedSeminorm
  )
open WeightedEstimates

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

/-- A partition coefficient bundled on its actual compact support. -/
def supportedWeight (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    SupportedField (F := ℝ) (P.supportCompact i) :=
  ContDiffMapSupportedIn.of_support_subset (P.smooth i) subset_closure

@[simp] theorem supportedWeight_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (i : ι) (x : Base) : P.supportedWeight i x = P.weight i x := rfl

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBoundaryCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed compact boundary curves and their actual second-form fields.
The cutoff is chosen from the curve geometry, independently of any immersion. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

structure PhaseBoundaryCurve (B : SmoothingAtlas M) where
  index : B.centers
  phase : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base
  smooth : ContDiff ℝ ∞ phase
  inverse_smooth : ContDiff ℝ ∞ phase.symm
  carrier : Set M
  compact : IsCompact carrier
  source : carrier ⊆ ((chart (index : M)).trans phase).source
  active : ∀ p ∈ carrier, B.weight index p ≠ 0

namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

def coordinate (p : M) : SmallModes.Base := baseEquiv (c.phase (chart (c.index : M) p))

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFlatBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat cutoffs for the actual circular disks in primitive preparation.
Their centers and radii are smooth parameters. -/
noncomputable section
open Set Function Filter
open scoped Topology
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def circularRadiusSquared (c p : Base) : ℝ := (p.1-c.1)^2 + (p.2-c.2)^2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CircularSmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smoothing atlas whose positive loci are actual coordinate disks.
The cutoffs are flat circular functions, not arbitrary subordinate bumps. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def circularCoordinateRegion (p : M) (r : ℝ) : Set SmallModes.Base :=
  {x | circularRadiusSquared (coordinateChart p p) x ≤ r^2}

def circularCoordinateDisk (p : M) (r : ℝ) : Set M :=
  (coordinateChart p).source ∩
    (coordinateChart p) ⁻¹' {x | circularRadiusSquared (coordinateChart p p) x < r^2}

def circularDiskClosure (p : M) (r : ℝ) : Set M :=
  (coordinateChart p).symm '' circularCoordinateRegion p r

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorOperatorSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual finite primitive operator, derived from its
supported coefficients and the smooth phase differentials. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance operatorSmoothFiberNormed_r043b26_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorSmoothFiberSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance operatorSmoothFiberComplete_r043b26_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance operatorSmoothDualAdd_r043b26_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance operatorSmoothDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance

namespace SmoothingAtlas
local instance operatorSmoothFiberNormed_r043b26_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorSmoothFiberSpace_r043b26_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance operatorSmoothFiberComplete_r043b26_2 : CompleteSpace TensorFiber := inferInstance
local instance operatorSmoothDualAdd_r043b26_2 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (A : SmoothingAtlas M)

local instance operatorSmoothSectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorSmoothSectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def phaseDifferentialSquare (phi : M → ℝ) (p : M) : CovariantTwoTensor p :=
  (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) phi p).smulRight
    (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) phi p)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPrimitiveFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite smooth primitive families and their partial-cycle metrics.
Different cycles may use different supports and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance familyFiberNormed_r043b26_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance familyFiberSpace_r043b26_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance familyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

local instance familyDualSmul_r043b26_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance familySectionNormed_r043b26_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance familySectionSpace_r043b26_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
structure SmoothPrimitiveFamily (ι : Type*) [Fintype ι]
    (u : ∀ p : M, CovariantTwoTensor p) where
  amplitude : ι → M → ℝ
  phase : ι → M → ℝ
  smoothAmplitude : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amplitude a)
  smoothPhase : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phase a)
  sum_eq : ∀ p, (∑ a, (amplitude a p)^2 •
    SmoothingAtlas.phaseDifferentialSquare (phase a) p) = u p

namespace SmoothPrimitiveFamily
local instance familyFiberNormed_r043b26_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance familyFiberSpace_r043b26_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance familyDualSmul_r043b26_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

local instance familySectionNormed_r043b26_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance familySectionSpace_r043b26_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def term (a : ι) (p : M) : CovariantTwoTensor p :=
  (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma term_apply (a : ι) (p : M) (v w : TangentSpace planeModel p) :
    d.term a p v w = (d.amplitude a p)^2 *
      (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v) *
      (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p w) := by
  change (d.amplitude a p)^2 *
    ((show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v) *
      (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p w)) = _
  ring

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma term_nonneg (a : ι) (p : M) (v : TangentSpace planeModel p) :
    0 ≤ d.term a p v v := by
  rw [d.term_apply]
  nlinarith [sq_nonneg (d.amplitude a p),
    sq_nonneg (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v)]

include d in
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma tensor_nonneg (p : M) (v : TangentSpace planeModel p) : 0 ≤ u p v v := by
  rw [← d.sum_eq p]
  simp only [sum_apply]
  exact Finset.sum_nonneg (fun a _ => d.term_nonneg a p v)

/-- The completed-cycle contribution plus any subset of the current cycle. -/
def cycleTensor (N c : ℕ) (s : Finset ι) (p : M) : CovariantTwoTensor p :=
  ((c : ℝ)/(N : ℝ)) • u p+(N : ℝ)⁻¹ • ∑ a ∈ s, d.term a p

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_nonneg (N c : ℕ) (s : Finset ι) (p : M) (v : TangentSpace planeModel p) :
    0 ≤ d.cycleTensor N c s p v v := by
  change 0 ≤ (c : ℝ)/(N : ℝ)*u p v v+(N : ℝ)⁻¹*(∑ a ∈ s, d.term a p) v v
  apply add_nonneg
  · exact mul_nonneg (by positivity) (d.tensor_nonneg p v)
  · apply mul_nonneg (by positivity)
    simp only [sum_apply]
    exact Finset.sum_nonneg (fun a _ => d.term_nonneg a p v)

end SmoothPrimitiveFamily

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryParam
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
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

lemma circularParam_radius (c : CurvePlane) (r t : ℝ) :
    circularRadiusSquared c (circularParam c r t) = r^2 := by
  dsimp [circularRadiusSquared,circularParam]
  nlinarith [Real.sin_sq_add_cos_sq t]

lemma circularParam_covers {c x : CurvePlane} {r : ℝ} (hr : 0 < r)
    (hx : circularRadiusSquared c x = r^2) :
    ∃ t ∈ Icc (-Real.pi) Real.pi, circularParam c r t = x := by
  let z : ℂ := ⟨x.1-c.1,x.2-c.2⟩
  have hn : ‖z‖ = r := by
    have hs : ‖z‖^2 = r^2 := by
      rw [Complex.sq_norm]
      simpa [Complex.normSq_apply,z,circularRadiusSquared,pow_two] using hx
    nlinarith [norm_nonneg z]
  refine ⟨z.arg,⟨(Complex.neg_pi_lt_arg z).le,Complex.arg_le_pi z⟩,?_⟩
  have hcos := Complex.norm_mul_cos_arg z
  have hsin := Complex.norm_mul_sin_arg z
  rw [hn] at hcos hsin
  apply Prod.ext <;> dsimp [circularParam]
  · dsimp [z] at hcos
    linarith
  · dsimp [z] at hsin
    linarith

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularBoundary (p : M) (r : ℝ) : Set M :=
  (coordinateChart p).source ∩ (coordinateChart p) ⁻¹'
    {x | circularRadiusSquared (coordinateChart p p) x = r^2}

def circularBoundaryParam (p : M) (r : ℝ) (t : ℝ) : M :=
  (coordinateChart p).symm (circularParam (coordinateChart p p) r t)

omit [IsManifold planeModel ∞ M] in
lemma circularBoundaryParam_target (p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) (t : ℝ) :
    circularParam (coordinateChart p p) r t ∈ (coordinateChart p).target :=
  hreg (le_of_eq (circularParam_radius _ _ _))

lemma circularBoundaryParam_smooth (p : M) {r : ℝ}
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContMDiff 𝓘(ℝ) planeModel ∞ (circularBoundaryParam p r) := by
  intro t
  exact (((coordinateChart_symm_smoothOn p) _ (circularBoundaryParam_target p hreg t)).contMDiffAt
    ((coordinateChart p).open_target.mem_nhds (circularBoundaryParam_target p hreg t))).comp t
      ((circularParam_smooth _ r).contMDiff.contMDiffAt)

omit [IsManifold planeModel ∞ M] in
lemma circularBoundary_image (p : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularBoundary p r = circularBoundaryParam p r '' Icc (-Real.pi) Real.pi := by
  ext x
  constructor
  · rintro ⟨hxs,hx⟩
    obtain ⟨t,ht,he⟩ := circularParam_covers hr hx
    exact ⟨t,ht,by rw [circularBoundaryParam,he,(coordinateChart p).left_inv hxs]⟩
  · rintro ⟨t,ht,rfl⟩
    have htgt := circularBoundaryParam_target p hreg t
    refine ⟨(coordinateChart p).map_target htgt,?_⟩
    change circularRadiusSquared _ ((coordinateChart p) ((coordinateChart p).symm _)) = _
    rw [(coordinateChart p).right_inv htgt,circularParam_radius]

lemma circularBoundary_compact (p : M) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularBoundary p r) := by
  rw [circularBoundary_image p hr hreg]
  exact isCompact_Icc.image (circularBoundaryParam_smooth p hreg).continuous

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryTangencies
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives along the explicit circle equal evaluation of the actual
phase covector on its nonzero angular tangent. Compact parameter finiteness
therefore gives finiteness of the genuine surface tangency set. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularPhaseDerivative (q p : M) (ell : CurvePlane) (L : ℝ) (x : M) : ℝ :=
  phaseLinear (phaseDerivative (centeredAtlasPhase q ell L ∘ (coordinateChart p).symm)
    (coordinateChart p x))
    (circularAngularTangent (coordinateChart p p) (coordinateChart p x))

def circularPhaseTangencies (q p : M) (ell : CurvePlane) (L r R : ℝ) : Set M :=
  circularBoundary p r ∩ circularDiskClosure q R ∩ {x | circularPhaseDerivative q p ell L x = 0}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPhaseBoundaryCurve
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate circles as the fixed phase curves of the induction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def circularPhaseBoundaryCurve (i : B.centers) {r r₀ : ℝ} (hr : 0 < r)
    (hsmall : r^2 < r₀^2)
    (hpos : ∀ p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) r₀)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    PhaseBoundaryCurve B where
  index := i
  phase := e
  smooth := he
  inverse_smooth := hi
  carrier := circularBoundary (i : M) r
  compact := circularBoundary_compact (i : M) hr hreg
  source := by
    intro p hp
    refine ⟨?_,?_⟩
    · change p ∈ (chart (i : M)).source
      rw [chart_source]
      simpa only [coordinateChart_source] using hp.1
    · have hx := hcover (coordinateChart (i : M) p) hp.2.le
      change baseEquiv.symm (baseEquiv (chart (i : M) p)) ∈ e.source at hx
      change chart (i : M) p ∈ e.source
      simpa only [baseEquiv.symm_apply_apply] using hx
  active := by
    intro p hp
    apply ne_of_gt ((hpos p).mpr ?_)
    exact ⟨hp.1,hp.2.trans_lt hsmall⟩

omit [CompactSpace M] in
@[simp] lemma circularPhaseBoundaryCurve_carrier (i : B.centers) {r r₀ : ℝ} (hr : 0 < r)
    (hsmall : r^2 < r₀^2)
    (hpos : ∀ p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) r₀)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    (B.circularPhaseBoundaryCurve i hr hsmall hpos hreg e he hi hcover).carrier =
      circularBoundary (i : M) r := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPhaseDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact affine dependence of supported circular phases on their linear
parameters. The curvature parameter stays fixed. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def circularPhase (i : B.centers) (ell : Base) (L : ℝ) : M → ℝ :=
  restore (i : M) (B.outer i)
    (centeredConvexPhase ell L (coordinateChart (i : M) i) ∘ JetPolynomial.planeCoordinateIsometry)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteBoundaryCrossingSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact crossing sets for the remaining curves in a finite induction.
The no-three-curves condition keeps these points off the next boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

noncomputable def boundaryCrossingSet (curves : ι → PhaseBoundaryCurve B) (s : Set ι) : Set M :=
  {p | ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ p ∈ (curves i).carrier ∧ p ∈ (curves j).carrier}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SpatialLoopAmplitude
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed spatial amplitude is independent of the varying immersion,
even though the coefficient calculus stores it as a function of the full jet. -/

noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

/-- The position slots of an actual low jet. -/
def lowJetPosition : LowJet →L[ℝ] Base :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (.inl i))

@[simp] lemma lowJetPosition_apply (J : LowJet) (i : Fin 2) :
    lowJetPosition J i = J (.inl i) := rfl

@[simp] lemma lowJetPosition_lowJet (G : Base → Space) (p : Base) :
    lowJetPosition (lowJet G p) = p := by
  ext i
  rfl

@[simp] lemma lowJetPosition_variationLowJet (H : Base → Space) (p : Base) :
    lowJetPosition (variationLowJet H p) = 0 := by
  ext i
  rfl

/-- Store a fixed function of position in the existing low-jet coefficient API. -/
def spatialAmplitude (a : Base → ℝ) : LowJet → ℝ := fun J => a (lowJetPosition J)

lemma spatialAmplitude_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatialAmplitude a) := ha.comp lowJetPosition.contDiff

@[simp] lemma spatialAmplitude_lowJet (a : Base → ℝ) (G : Base → Space) (p : Base) :
    spatialAmplitude a (lowJet G p) = a p := by
  simp only [spatialAmplitude,lowJetPosition_lowJet]

end ClosedSurfaceR4.JetPolynomial

namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector

variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

/-- The given amplitude is fixed as a function of the base point, throughout
the whole open jet domain used for nearby immersions. -/
def HasSpatialAmplitude (a : Base → ℝ) : Prop :=
  ∀ J ∈ O, l.amplitude J = a (lowJetPosition J)

/-- Normalize the record field itself to the fixed spatial function while
preserving the same velocity loop and its proved geometric identities. -/
def withSpatialAmplitude (a : Base → ℝ) (ha : ContDiff ℝ ∞ a)
    (he : l.HasSpatialAmplitude a) : SurfaceVelocityFamily.Loop O where
  amplitude := spatialAmplitude a
  smoothAmplitude := (spatialAmplitude_smooth ha).contDiffOn
  velocity := l.velocity
  smoothVelocity := l.smoothVelocity
  periodic := l.periodic
  gram_ne := l.gram_ne
  nonzero J hJ := by
    rw [show spatialAmplitude a J = l.amplitude J from (he J hJ).symm]
    exact l.nonzero J hJ
  perpY := l.perpY
  perpC := l.perpC
  length J hJ t := by
    rw [show spatialAmplitude a J = l.amplitude J from (he J hJ).symm]
    exact l.length J hJ t
  mean := l.mean

@[simp] lemma withSpatialAmplitude_amplitude (a : Base → ℝ) (ha : ContDiff ℝ ∞ a)
    (he : l.HasSpatialAmplitude a) (J : LowJet) :
    (l.withSpatialAmplitude a ha he).amplitude J = a (lowJetPosition J) := rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end


