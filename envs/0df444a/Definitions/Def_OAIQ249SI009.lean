-- Prove2me | Definitions.Def_OAIQ249SI009
-- name    : OAIQ249SI009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T09:42:18.404197+00:00
-- url     : https://prove2.me/theorems/0fd9c4a3-63e4-439c-bd96-d13deaf47268
-- title:
--   Definitions bundle OAIQ249SI009 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 48 definitions, 1 inductive type or structure and 3 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveLocalData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.parameterNormData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveLocalPolynomial`, `OAI.ClosedSurfaceR4.RealModes.goodJetPhase`, `OAI.ClosedSurfaceR4.RealModes.planeAdjugate`, `OAI.ClosedSurfaceR4.RealModes.planeAdjugateOperator`, `OAI.ClosedSurfaceR4.RealModes.pullCovector`, `OAI.ClosedSurfaceR4.RealModes.realConnectionX`, `OAI.ClosedSurfaceR4.RealModes.realConnectionY`, `OAI.ClosedSurfaceR4.RealModes.realJetNormal`, `OAI.ClosedSurfaceR4.RealModes.realOsc`, `OAI.ClosedSurfaceR4.RealModes.realScalarCoefficients`, `OAI.ClosedSurfaceR4.RealModes.realTangentDualX`, `OAI.ClosedSurfaceR4.RealModes.realTangentDualY`, `OAI.ClosedSurfaceR4.RealModes.realVectorCoefficients`, `OAI.ClosedSurfaceR4.SmallModes.LowJet.Domain`, `OAI.ClosedSurfaceR4.SmallModes.LowJet.coefficients`, `OAI.ClosedSurfaceR4.SmallModes.LowJet.scalarCoefficients`, `OAI.ClosedSurfaceR4.SmallModes.LowJet.vectorCoefficients`, `OAI.ClosedSurfaceR4.SmallModes.TwoJet`, `OAI.ClosedSurfaceR4.SmallModes.admissibleComplexJets`, `OAI.ClosedSurfaceR4.SmallModes.complexifyJetCLM`, `OAI.ClosedSurfaceR4.SmallModes.oscillate`, `OAI.ClosedSurfaceR4.SmallModes.twoJet`, `OAI.ClosedSurfaceR4.SmallModes.unitMode`, `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.decode`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.GeometricJet`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.ofGeometric`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.primitiveNormalTriple`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.restrict`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetAccelerationCoefficients`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetDomain`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetNormal`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetPreferred`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetProjectedPreferred`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetSecondNormal`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetTangentGram`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.preferredJetDomain`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.supportedJetDomain`, `OAI.ClosedSurfaceR4.VelocityFrame.first` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_AtlasWeights`, `Immersion_ClosedSurface_ChartTransition`, `Immersion_ClosedSurface_ForcedModes`, `Immersion_ClosedSurface_JetBounds`, `Immersion_ClosedSurface_OscillatoryModel`, `Immersion_ClosedSurface_SmoothCoordinates`, `SurfaceImmersion_Atlas_GoodPhaseStability`, `SurfaceImmersion_Atlas_JetPhaseChartFromReal`, `SurfaceImmersion_Atlas_SurfaceJetCoordinates`, `SurfaceImmersion_Correction_PolynomialConnectionBounds`, `SurfaceImmersion_Correction_UniformRealModeCoefficients`, `SurfaceImmersion_Geometry_PlaneAdjugate`, `SurfaceImmersion_Geometry_PreferredJetDomain`, `SurfaceImmersion_Geometry_PreferredJetGeometry`, `SurfaceImmersion_Geometry_PreparedRadialSecondForm`, `SurfaceImmersion_Geometry_RealJetCoefficients`, `SurfaceImmersion_Geometry_SupportedJetDomain`, `SurfaceImmersion_Primitive_ConstructedSurfaceLoop`, `SurfaceImmersion_Primitive_FrozenCircularData`, `SurfaceImmersion_Primitive_JetLoopPullback`, `SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds`, `SurfaceImmersion_Primitive_PrimitiveTermC1Bounds`, `SurfaceImmersion_Primitive_ProjectedVelocityFrame`, `SurfaceImmersion_Primitive_RestrictedSurfaceLoop`, `SurfaceImmersion_Primitive_UniformPrimitiveNormal`, `SurfaceImmersion_Primitive_VelocityFrame`, `SurfaceImmersion_Primitive_VelocityPlaneBasis`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundle `OAIQ249SI008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI011` and `OAIQ249SI014`; the statements `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_cross_phase_exterior_control`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_geometry_of_chartwise_good`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_fixed_chart_nonlinear_solver`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_supported_linear_mean_data`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_coordinate_taylor_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_explicit_finite_split_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_inverse_normal_nonlinear_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_inverse_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_relative_phase_polynomial_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_uniform_polynomial_nearby_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_RealModes_polynomial_frame_envelope`, `OAI_ClosedSurfaceR4_RealModes_polynomial_nonlinear_phase_frame_bound`, `OAI_ClosedSurfaceR4_SmallModes_freeModeBudget_bound`, `OAI_ClosedSurfaceR4_SmallModes_freeModeBudget_size`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_surface_collar_family`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family` and `OAI_ClosedSurfaceR4_phaseTransition_refl_covector`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_supported_patch_geometry`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_directionIn_first_ne_of_covectors`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exists_transverse_circular_radii`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_surface_correction_budgets`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_point_crossings`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_small_metric_prepared_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_convex_circular_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_remainder_C1_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_diagonal_mem_closure`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_half_arc_neighborhood`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_crossings`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_curve_cover`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_coordinate_taylor_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_inverse_normal_nonlinear_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_inverse_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGrid_compact_anchored_polynomial_grid`, `OAI_ClosedSurfaceR4_RealModes_polynomial_frame_envelope`, `OAI_ClosedSurfaceR4_RealModes_polynomial_nonlinear_phase_frame_bound`, `OAI_ClosedSurfaceR4_SmallModes_freeModeBudget_size`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_surface_collar_family`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family`, `OAI_ClosedSurfaceR4_atlas_phase_weight_constants_with_catalog` and `OAI_ClosedSurfaceR4_phaseTransition_refl_covector`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI008

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

section Phase
variable {n : ℕ}


def unitMode (τ : ℝ) (p : Base) : ℂ :=
  Complex.exp (Complex.I / (τ : ℂ) * (p.1 : ℂ))

def oscillate (τ : ℝ) (Z : Field n) : Field n := fun p => unitMode τ p • Z p

end Phase

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

def pullCovector (A : Base →L[ℝ] Base) (ξ : Base) : Base :=
  (ξ.1*(A dx).1+ξ.2*(A dx).2,ξ.1*(A dy).1+ξ.2*(A dy).2)

end ClosedSurfaceR4.RealModes

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




abbrev TwoJet (n : ℕ) := Fin 5 → Ambient n

def twoJet {n : ℕ} (G : Field n) (p : Base) : TwoJet n :=
  ![coordDeriv dx G p, coordDeriv dy G p, coordDeriv dx (coordDeriv dx G) p,
    coordDeriv dx (coordDeriv dy G) p, coordDeriv dy (coordDeriv dy G) p]

namespace LowJet
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



structure Domain (V : Set (TwoJet n)) : Prop where
  isOpen : IsOpen V
  determinant : ∀ J ∈ V, gramDet (J 0) (J 1) ≠ 0
  good : ∀ J ∈ V,
    normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0

def scalarCoefficients (J : TwoJet n) : Fin 8 → ℂ :=
  let X := J 0
  let Y := J 1
  let b := normalPart X Y (J 4)
  ![liftX X Y (X ⬝ᵥ J 2) (Y ⬝ᵥ J 2), liftY X Y (X ⬝ᵥ J 2) (Y ⬝ᵥ J 2),
    liftX X Y (X ⬝ᵥ J 3) (Y ⬝ᵥ J 3), liftY X Y (X ⬝ᵥ J 3) (Y ⬝ᵥ J 3),
    liftX X Y (X ⬝ᵥ J 4) (Y ⬝ᵥ J 4), liftY X Y (X ⬝ᵥ J 4) (Y ⬝ᵥ J 4),
    (normalPart X Y (J 2) ⬝ᵥ b) / (b ⬝ᵥ b),
    (normalPart X Y (J 3) ⬝ᵥ b) / (b ⬝ᵥ b)]

def vectorCoefficients (J : TwoJet n) : Fin 5 → Ambient n :=
  let X := J 0
  let Y := J 1
  let b := normalPart X Y (J 4)
  ![normalPart X Y (J 2), normalPart X Y (J 3), tangentLift X Y 1 0,
    tangentLift X Y 0 1, (b ⬝ᵥ b)⁻¹ • b]

def coefficients (J : TwoJet n) : CoeffIndex n → ℂ
  | Sum.inl i => scalarCoefficients J i
  | Sum.inr (i, a) => vectorCoefficients J i a

end LowJet

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
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

variable [IsManifold planeModel ∞ M]



def coordinateTransition (q p : M) : OpenPartialHomeomorph SmallModes.Base SmallModes.Base :=
  (coordinateChart p).symm.trans (coordinateChart q)

end ClosedSurfaceR4

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

def atlasGram (F : M → Space) (p a : M) : ℝ :=
  NormalFrame.gramDet (coordDeriv dx (coordinateMap F p) (coordinateChart p a))
    (coordDeriv dy (coordinateMap F p) (coordinateChart p a))

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

def realOsc (τ : ℝ) {n : ℕ} (Z : Field n) : RField n :=
  fun p => QuadraticMean.realPart (oscillate τ Z p)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseStability
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

def goodJetPhase : Set (RealTwoJet × Base) :=
  {z | NormalFrame.gramDet (z.1 0) (z.1 1) ≠ 0 ∧ Good (secondTensorFromJet z.1) z.2}

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

def first (u v : Vec) (t : ℝ) : Vec := normalize (blend u v t)

def second (Y C u v : Vec) (t : ℝ) : Vec := unitPerp Y C (first u v t)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityPlaneBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates in the actual two-dimensional velocity plane. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

def planeCoordinates (e₁ e₂ v : Vec) : LoopDensity.Plane := ![v ⬝ᵥ e₁, v ⬝ᵥ e₂]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreparedRadialSecondForm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact pure-radial second form at a prepared spherical point, in
the same coordinates used by the ordered boundary invariant. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes SphericalJets

def scaledSphereCoordinates (F : Plane → Space) (r : ℝ) : RField 4 :=
  spaceCoordinates ∘ (fun y => r • F y) ∘ planeCoordinates.symm

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FrozenCircularData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal data as smooth functions of position and angular value.
The first mixed normal coefficient contains no derivative of the angle. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frozenError (Q : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec) (d : E)
    (z : E × ℝ) : Vec :=
  fderiv ℝ Q z.1 d + (fderiv ℝ R z.1 d) • direction (e₁ z.1) (e₂ z.1) z.2 +
    R z.1 • (Real.cos z.2 • fderiv ℝ e₁ z.1 d + Real.sin z.2 • fderiv ℝ e₂ z.1 d)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceJetCoordinates
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

def decode (J : JetPolynomial.LowJet) : CollarVelocity.JetBase :=
  ((J (.inl 0), J (.inl 1)), fun i a =>
    J (.inr (![1, 2, 3, 4, 6] i, a)))

lemma decode_smooth : ContDiff ℝ ∞ decode := by
  apply ContDiff.prodMk
  · exact (ContinuousLinearMap.proj (.inl 0) : JetPolynomial.LowJet →L[ℝ] ℝ).contDiff.prodMk
      (ContinuousLinearMap.proj (.inl 1) : JetPolynomial.LowJet →L[ℝ] ℝ).contDiff
  · apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro a
    exact (ContinuousLinearMap.proj (.inr (![1, 2, 3, 4, 6] i, a)) :
      JetPolynomial.LowJet →L[ℝ] ℝ).contDiff

end ClosedSurfaceR4.SurfaceJetCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformPrimitiveNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same finite coefficients used for the metric expansion preserve
transverse normal acceleration uniformly over a compact low-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def primitiveNormalTriple (f : JetPolynomial.Base → Euclidean) (p : JetPolynomial.Base) :
    VelocityFrame.NormalTriple :=
  ![spaceCoordinates (fderiv ℝ f p (coordinateVector 0)),
    spaceCoordinates (fderiv ℝ f p (coordinateVector 1)),
    spaceCoordinates (fderiv ℝ (fun q => fderiv ℝ f q (coordinateVector 1))
      p (coordinateVector 1))]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JetPhaseChartFromReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The whole-disk real phase charts in the coordinate representation used
by the nonlinear primitive construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes

def jetPhaseChart (e : OpenPartialHomeomorph Base Base) :
    OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base :=
  (baseEquiv.toHomeomorph.transOpenPartialHomeomorph e).transHomeomorph baseEquiv.symm.toHomeomorph

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialConnectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the tangential reconstruction coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realConnectionX (X Y W : RVec 4) : ℝ :=
  ((Y ⬝ᵥ Y)*(X ⬝ᵥ W)-(X ⬝ᵥ Y)*(Y ⬝ᵥ W))/NormalFrame.gramDet X Y

def realConnectionY (X Y W : RVec 4) : ℝ :=
  ((X ⬝ᵥ X)*(Y ⬝ᵥ W)-(X ⬝ᵥ Y)*(X ⬝ᵥ W))/NormalFrame.gramDet X Y

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformRealModeCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reconstruction estimates on a fixed compact set of real two-jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

def admissibleComplexJets : Set (TwoJet 4) :=
  {J | gramDet (J 0) (J 1) ≠ 0 ∧
    normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0}

def complexifyJetCLM : RealTwoJet →L[ℝ] TwoJet 4 :=
  ContinuousLinearMap.pi fun i => (complexifyCLM 4).comp (ContinuousLinearMap.proj i)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneAdjugate
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit two-dimensional inverse matrix used for phase charts. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes

def planeAdjugate (A : Base →L[ℝ] Base) : Base →L[ℝ] Base :=
  (((A dy).2 • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (A dy).1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (-(A dx).2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (A dx).1 • ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma planeAdjugate_apply (A : Base →L[ℝ] Base) (v : Base) :
    planeAdjugate A v = ((A dy).2*v.1-(A dy).1*v.2,
      -(A dx).2*v.1+(A dx).1*v.2) := rfl

lemma planeAdjugate_norm_le (A : Base →L[ℝ] Base) : ‖planeAdjugate A‖ ≤ 2*‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [planeAdjugate_apply,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff]
  have hdx : ‖A dx‖ ≤ ‖A‖ := by simpa [dx] using A.le_opNorm dx
  have hdy : ‖A dy‖ ≤ ‖A‖ := by simpa [dy] using A.le_opNorm dy
  have ha := (norm_fst_le (A dx)).trans hdx
  have hb := (norm_snd_le (A dx)).trans hdx
  have hc := (norm_fst_le (A dy)).trans hdy
  have hd := (norm_snd_le (A dy)).trans hdy
  have hv1 := norm_fst_le v
  have hv2 := norm_snd_le v
  simp only [Real.norm_eq_abs] at ha hb hc hd hv1 hv2
  constructor
  · calc
      _ ≤ |(A dy).2*v.1|+|(A dy).1*v.2| := abs_sub _ _
      _ ≤ ‖A‖*‖v‖+‖A‖*‖v‖ := by rw [abs_mul,abs_mul]; gcongr
      _ = _ := by ring
  · calc
      _ ≤ |-(A dx).2*v.1|+|(A dx).1*v.2| := abs_add_le _ _
      _ ≤ ‖A‖*‖v‖+‖A‖*‖v‖ := by rw [abs_mul,abs_neg,abs_mul]; gcongr
      _ = _ := by ring

def planeAdjugateOperator : (Base →L[ℝ] Base) →L[ℝ] (Base →L[ℝ] Base) :=
  LinearMap.mkContinuous
    { toFun := planeAdjugate
      map_add' := by
        intro A B
        apply ContinuousLinearMap.ext
        intro v
        change planeAdjugate (A+B) v = planeAdjugate A v + planeAdjugate B v
        simp only [planeAdjugate_apply,add_apply,Prod.fst_add,Prod.snd_add]
        ext <;> dsimp <;> ring
      map_smul' := by
        intro c A
        apply ContinuousLinearMap.ext
        intro v
        change planeAdjugate (c • A) v = c • planeAdjugate A v
        simp only [planeAdjugate_apply,smul_apply,Prod.smul_fst,
          Prod.smul_snd,smul_eq_mul,Prod.smul_mk]
        ext <;> dsimp <;> ring }
    2 planeAdjugate_norm_le

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ProjectedVelocityFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual frame formed from the projected tangent and preferred normal. -/
noncomputable section
open Set
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def projectedFirst (X Y C n : Vec) (t : ℝ) : Vec :=
  first (realNormalPart Y C X) (realNormalPart Y C n) t

def projectedSecond (X Y C n : Vec) (t : ℝ) : Vec :=
  unitPerp Y C (projectedFirst X Y C n t)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetLoopPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the constructed geometric loop to the ordered coordinate jets
used by the quantitative finite correction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates

def jetDomain (Ω : TopologicalSpace.Opens CollarVelocity.JetBase) :
    TopologicalSpace.Opens LowJet :=
  ⟨decode ⁻¹' Ω, Ω.isOpen.preimage decode_smooth.continuous⟩

/-- The velocity supplied by the geometric construction, expressed in the
analytic second-jet coordinates. All its identities survive this pullback. -/
def Loop.ofGeometric {Ω : TopologicalSpace.Opens CollarVelocity.JetBase}
    {a : CollarVelocity.JetBase → ℝ} {V : CollarVelocity.JetBase × ℝ → RVec 4}
    (ha : ContDiffOn ℝ ∞ a Ω) (hV : ContDiffOn ℝ ∞ V (Ω ×ˢ univ))
    (hper : ∀ j ∈ Ω, Function.Periodic (fun t => V (j, t)) 1)
    (hD : ∀ j ∈ Ω, NormalFrame.gramDet (j.2 1) (j.2 4) ≠ 0)
    (hn : ∀ j ∈ Ω, realNormalPart (j.2 1) (j.2 4) (j.2 0) ≠ 0 ∨ a j ≠ 0)
    (hy : ∀ j ∈ Ω, ∀ t, j.2 1 ⬝ᵥ V (j, t) = 0)
    (hc : ∀ j ∈ Ω, ∀ t, j.2 4 ⬝ᵥ V (j, t) = 0)
    (hlen : ∀ j ∈ Ω, ∀ t, V (j, t) ⬝ᵥ V (j, t) =
      realNormalPart (j.2 1) (j.2 4) (j.2 0) ⬝ᵥ
        realNormalPart (j.2 1) (j.2 4) (j.2 0) + a j ^ 2)
    (hm : ∀ j ∈ Ω, (∫ t in 0..1, V (j, t)) = realNormalPart (j.2 1) (j.2 4) (j.2 0)) :
    Loop (jetDomain Ω) where
  amplitude := a ∘ decode
  smoothAmplitude := ha.comp decode_smooth.contDiffOn (fun _ hJ => hJ)
  velocity z := V (decode z.1, z.2)
  smoothVelocity := hV.comp
    ((decode_smooth.contDiffOn.comp contDiffOn_fst (fun z _ => mem_univ z.1)).prodMk
      contDiffOn_snd) (fun _ hz => ⟨hz.1, hz.2⟩)
  periodic J hJ := hper (decode J) hJ
  gram_ne J hJ := hD (decode J) hJ
  nonzero J hJ := hn (decode J) hJ
  perpY J hJ := hy (decode J) hJ
  perpC J hJ := hc (decode J) hJ
  length J hJ := hlen (decode J) hJ
  mean J hJ := hm (decode J) hJ

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ConstructedSurfaceLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the analytic surface-loop input from the geometric frame and
the controlled angle; no periodic velocity family is assumed here. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

def jetNormal (j : CollarVelocity.JetBase) : Vec :=
  realNormalPart (j.2 1) (j.2 4) (j.2 0)

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a preferred normal to nearby second jets by orthogonal projection.
All coefficients and normal vectors are explicit functions of the jet. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

abbrev GeometricJet := CollarVelocity.JetBase

def jetTangentGram (j : GeometricJet) : ℝ := gramDet (j.2 0) (j.2 1)

def jetAccelerationCoefficients (j : GeometricJet) : Base :=
  (((j.2 1 ⬝ᵥ j.2 1)*(j.2 0 ⬝ᵥ j.2 4)-(j.2 0 ⬝ᵥ j.2 1)*(j.2 1 ⬝ᵥ j.2 4))/jetTangentGram j,
   ((j.2 0 ⬝ᵥ j.2 0)*(j.2 1 ⬝ᵥ j.2 4)-(j.2 0 ⬝ᵥ j.2 1)*(j.2 0 ⬝ᵥ j.2 4))/jetTangentGram j)

def jetSecondNormal (j : GeometricJet) : Vec := realNormalPart (j.2 0) (j.2 1) (j.2 4)

def jetProjectedPreferred (n : Base → Vec) (j : GeometricJet) : Vec :=
  realNormalPart (j.2 0) (j.2 1) (n j.1)

def jetPreferred (n : Base → Vec) (j : GeometricJet) : Vec :=
  normalize (jetProjectedPreferred n j)

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredJetDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An open domain of genuine second jets carrying the normal-frame geometry.
The preferred normal is projected from the original spatial normal field. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

def preferredJetDomain (U : Set Base) (n : Base → Vec) : Set GeometricJet :=
  {j | j.1 ∈ U ∧ jetTangentGram j ≠ 0 ∧
    (jetAccelerationCoefficients j).1 < 0 ∧ jetProjectedPreferred n j ≠ 0}

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealJetCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real formulas for the reconstruction coefficients at an actual real
surface jet; complexification preserves every coefficient exactly. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

def realTangentDualX (X Y : RVec 4) : RVec 4 :=
  ((Y ⬝ᵥ Y)/NormalFrame.gramDet X Y) • X+(-(X ⬝ᵥ Y)/NormalFrame.gramDet X Y) • Y

def realTangentDualY (X Y : RVec 4) : RVec 4 :=
  (-(X ⬝ᵥ Y)/NormalFrame.gramDet X Y) • X+((X ⬝ᵥ X)/NormalFrame.gramDet X Y) • Y

def realJetNormal (J : RealTwoJet) (i : Fin 5) := realNormalPart (J 0) (J 1) (J i)

def realScalarCoefficients (J : RealTwoJet) : Fin 8 → ℝ :=
  ![realConnectionX (J 0) (J 1) (J 2),realConnectionY (J 0) (J 1) (J 2),
    realConnectionX (J 0) (J 1) (J 3),realConnectionY (J 0) (J 1) (J 3),
    realConnectionX (J 0) (J 1) (J 4),realConnectionY (J 0) (J 1) (J 4),
    (realJetNormal J 2 ⬝ᵥ realJetNormal J 4)/(realJetNormal J 4 ⬝ᵥ realJetNormal J 4),
    (realJetNormal J 3 ⬝ᵥ realJetNormal J 4)/(realJetNormal J 4 ⬝ᵥ realJetNormal J 4)]

def realVectorCoefficients (J : RealTwoJet) : Fin 5 → RVec 4 :=
  ![realJetNormal J 2,realJetNormal J 3,realTangentDualX (J 0) (J 1),
    realTangentDualY (J 0) (J 1),
    (realJetNormal J 4 ⬝ᵥ realJetNormal J 4)⁻¹ • realJetNormal J 4]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedJetDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The velocity radius stays nonzero on an open neighborhood of the
actual compact jet set, including the zero-amplitude boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

def supportedJetDomain (U : Set Base) (n : Base → Vec) (a : Base → ℝ) : Set GeometricJet :=
  {j | j ∈ preferredJetDomain U n ∧ (jetNormal j ≠ 0 ∨ a j.1 ≠ 0)}

end ClosedSurfaceR4.SurfaceVelocityFamily

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberSpace
local instance amplitudeFiberComplete_r41c975_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeDualAdd
local instance amplitudeDualSmul_r41c975_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberGroup
def parameterNormData (i : ι) (z : PrimitiveAmplitudeData ι) :=
  (primitiveParameterInverse z,
    (fderiv ℝ primitiveParameterInverse z,
      (primitiveParameterAmplitude i z, fderiv ℝ (primitiveParameterAmplitude i) z)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveTermC1Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primitive tensor terms have a uniform C1 bound from their scalar
amplitude and phase-covector coordinate bounds. All constants precede those
functions and every later cycle count. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

local instance termBoundFiberNormed_r41c975_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance termBoundFiberSpace_r41c975_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance termBoundDualNormed_r41c975_1 : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance termBoundDualSpace_r41c975_1 : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
abbrev PrimitiveLocalData := ℝ × (ℝ × (Plane →L[ℝ] ℝ))
def primitiveLocalPolynomial (z : PrimitiveLocalData) : TensorFiber :=
  (z.1^2*z.2.1^2) • z.2.2.smulRight z.2.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_RestrictedSurfaceLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict a constructed loop to a neighborhood where every zero-amplitude
jet has the constant normal velocity required by the supported expansion. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial

variable {O : TopologicalSpace.Opens LowJet}

def restrict (l : SurfaceVelocityFamily.Loop O) (V : TopologicalSpace.Opens LowJet)
    (hVO : (V : Set LowJet) ⊆ O) : SurfaceVelocityFamily.Loop V where
  amplitude := l.amplitude
  smoothAmplitude := l.smoothAmplitude.mono hVO
  velocity := l.velocity
  smoothVelocity := l.smoothVelocity.mono (Set.prod_mono hVO Subset.rfl)
  periodic J hJ := l.periodic J (hVO hJ)
  gram_ne J hJ := l.gram_ne J (hVO hJ)
  nonzero J hJ := l.nonzero J (hVO hJ)
  perpY J hJ := l.perpY J (hVO hJ)
  perpC J hJ := l.perpC J (hVO hJ)
  length J hJ := l.length J (hVO hJ)
  mean J hJ := l.mean J (hVO hJ)

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end


