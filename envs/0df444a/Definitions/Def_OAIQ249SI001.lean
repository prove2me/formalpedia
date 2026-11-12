-- Prove2me | Definitions.Def_OAIQ249SI001
-- name    : OAIQ249SI001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T19:54:44.776715+00:00
-- url     : https://prove2.me/theorems/d4f1c028-6b43-45ff-bd55-7afa674f617d
-- title:
--   Definitions bundle OAIQ249SI001 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 335 declarations of OpenAI's Lean: 156 definitions, 3 inductive types or structures, 1 instance and 175 theorems. The definitions and types are `OAI.ClosedSurfaceR4.AtlasPhaseLabel`, `OAI.ClosedSurfaceR4.CollarVelocity.amplitude`, `OAI.ClosedSurfaceR4.CollarVelocity.angle`, `OAI.ClosedSurfaceR4.CollarVelocity.arcX`, `OAI.ClosedSurfaceR4.CollarVelocity.arcY`, `OAI.ClosedSurfaceR4.CollarVelocity.baseAngle`, `OAI.ClosedSurfaceR4.CollarVelocity.blendedAmplitude`, `OAI.ClosedSurfaceR4.CollarVelocity.blendedAngle`, `OAI.ClosedSurfaceR4.CollarVelocity.blendedPath`, `OAI.ClosedSurfaceR4.CollarVelocity.circleMean`, `OAI.ClosedSurfaceR4.CollarVelocity.clock`, `OAI.ClosedSurfaceR4.CollarVelocity.density`, `OAI.ClosedSurfaceR4.CollarVelocity.equation`, `OAI.ClosedSurfaceR4.CollarVelocity.inverseClock`, `OAI.ClosedSurfaceR4.CollarVelocity.loopX`, `OAI.ClosedSurfaceR4.CollarVelocity.loopY`, `OAI.ClosedSurfaceR4.CollarVelocity.normalInvariant`, `OAI.ClosedSurfaceR4.CollarVelocity.normalizedAngle`, `OAI.ClosedSurfaceR4.CollarVelocity.reparamX`, `OAI.ClosedSurfaceR4.CollarVelocity.reparamY`, `OAI.ClosedSurfaceR4.CollarVelocity.unitAngle`, `OAI.ClosedSurfaceR4.CollarVelocity.unitDensity`, `OAI.ClosedSurfaceR4.CollarVelocity.unitX`, `OAI.ClosedSurfaceR4.CollarVelocity.unitY`, `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.CovarianceCorrector.average`, `OAI.ClosedSurfaceR4.CovarianceCorrector.averageCLM`, `OAI.ClosedSurfaceR4.CovarianceCorrector.centeredPeriodic`, `OAI.ClosedSurfaceR4.CovarianceCorrector.correctedScalar`, `OAI.ClosedSurfaceR4.CovarianceCorrector.correctedVector`, `OAI.ClosedSurfaceR4.CovarianceCorrector.covariance`, `OAI.ClosedSurfaceR4.CovarianceCorrector.covarianceCLM`, `OAI.ClosedSurfaceR4.CovarianceCorrector.covarianceLinearMap`, `OAI.ClosedSurfaceR4.CovarianceCorrector.covarianceSolution`, `OAI.ClosedSurfaceR4.CovarianceCorrector.fluctuation`, `OAI.ClosedSurfaceR4.CovarianceCorrector.meanCLM`, `OAI.ClosedSurfaceR4.CovarianceCorrector.meanOperator`, `OAI.ClosedSurfaceR4.CovarianceCorrector.parameterCorrector`, `OAI.ClosedSurfaceR4.CovarianceCorrector.periodicBilinear`, `OAI.ClosedSurfaceR4.CovarianceCorrector.realCorrector` and 119 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_AtlasLabels`, `Immersion_ClosedSurface_ComplexPullback`, `Immersion_ClosedSurface_FiniteMean`, `Immersion_ClosedSurface_GridBumps`, `Immersion_ClosedSurface_GridCover`, `Immersion_ClosedSurface_GridPartition`, `Immersion_ClosedSurface_MeanSupport`, `Immersion_ClosedSurface_NormalFrame`, `Immersion_ClosedSurface_PhaseMean`, `Immersion_ClosedSurface_QuadraticMean`, `Immersion_ClosedSurface_WeightedBounds`, `SurfaceImmersion_Atlas_AtlasSupportedWeights`, `SurfaceImmersion_Atlas_ChartReadSupport`, `SurfaceImmersion_Atlas_CurvePhaseParameterGraph`, `SurfaceImmersion_Atlas_FiniteChartTranslationBound`, `SurfaceImmersion_Atlas_NonparallelPhaseCovectors`, `SurfaceImmersion_Atlas_SupportedChartEquiv`, `SurfaceImmersion_Atlas_SupportedChartTransport`, `SurfaceImmersion_Atlas_SupportedCoordinateChange`, `SurfaceImmersion_Atlas_SupportedPhaseOperators`, `SurfaceImmersion_Atlas_SupportedWeightedSeminorm`, `SurfaceImmersion_Atlas_TensorPlaneWeight`, `SurfaceImmersion_Correction_BundleSmoothing`, `SurfaceImmersion_Correction_CompactSmoothCutoffs`, `SurfaceImmersion_Correction_ComplexifiedPolynomialOperator`, `SurfaceImmersion_Correction_ConjugatedPolynomialOperator`, `SurfaceImmersion_Correction_CorrectionScaleControl`, `SurfaceImmersion_Correction_CorrectionScales`, `SurfaceImmersion_Correction_CovarianceCorrector`, `SurfaceImmersion_Correction_ExactCorrectionLimit`, `SurfaceImmersion_Correction_ExplicitCorrectionBudgetThreshold`, `SurfaceImmersion_Correction_FixedMeanSubstitution`, `SurfaceImmersion_Correction_JetPolynomialAlgebra`, `SurfaceImmersion_Correction_JetPolynomialCovariance`, `SurfaceImmersion_Correction_JetPolynomialIntegral`, `SurfaceImmersion_Correction_JetPolynomialLinear`, `SurfaceImmersion_Correction_JetPolynomialOperations`, `SurfaceImmersion_Correction_JetPolynomialVariation`, `SurfaceImmersion_Correction_ManifoldCorrectionLimit`, `SurfaceImmersion_Correction_ManifoldSmoothing`, `SurfaceImmersion_Correction_PolynomialPerturbationBounds`, `SurfaceImmersion_Correction_PolynomialPerturbationOperator`, `SurfaceImmersion_Correction_SmoothParameterIntegral`, `SurfaceImmersion_Correction_SmoothPeriodicCalculus`, `SurfaceImmersion_Correction_SmoothPeriodicPrimitive`, `SurfaceImmersion_Correction_SmoothingAtlas`, `SurfaceImmersion_Correction_SmoothingLocalization`, `SurfaceImmersion_Correction_SpecialPointCorrection`, `SurfaceImmersion_Correction_SupportedPolynomialOperator`, `SurfaceImmersion_Correction_TensorSmoothing`, `SurfaceImmersion_Correction_TensorSmoothingSymmetry`, `SurfaceImmersion_Geometry_CovarianceParameter`, `SurfaceImmersion_Geometry_CovarianceRealOperator`, `SurfaceImmersion_Geometry_DirectionalJetBounds`, `SurfaceImmersion_Geometry_ExplicitFixedOrderThreshold`, `SurfaceImmersion_Geometry_ExplicitPowerThreshold`, `SurfaceImmersion_Geometry_GenericProjectionParameter`, `SurfaceImmersion_Geometry_GeometricScaleThreshold`, `SurfaceImmersion_Geometry_JetPullbackExpressions`, `SurfaceImmersion_Geometry_JetVariationLinearity`, `SurfaceImmersion_Geometry_JetVariationSupport`, `SurfaceImmersion_Geometry_JetVariations`, `SurfaceImmersion_Geometry_JointCovarianceParameter`, `SurfaceImmersion_Geometry_LocalCovarianceParameter`, `SurfaceImmersion_Geometry_LocalParameterIntegral`, `SurfaceImmersion_Geometry_LowJetChainRule`, `SurfaceImmersion_Geometry_ManifoldMetricCalculus`, `SurfaceImmersion_Geometry_ModulatedJets`, `SurfaceImmersion_Geometry_PositiveDensityClock`, `SurfaceImmersion_Geometry_PositiveDensityInverse`, `SurfaceImmersion_Geometry_PositiveDensityReparam`, `SurfaceImmersion_Geometry_ProjectionDirections`, `SurfaceImmersion_Geometry_ProjectionSlopeDifferential`, `SurfaceImmersion_Geometry_SupportedOperatorTransport`, `SurfaceImmersion_Geometry_SupportedTupleOperators`, `SurfaceImmersion_Geometry_TangentSlopeLinearization`, `SurfaceImmersion_Geometry_TensorPerturbationOperator`, `SurfaceImmersion_Primitive_BlendedReparamTurns`, `SurfaceImmersion_Primitive_BlendedSpatialTurns`, `SurfaceImmersion_Primitive_BlendedVelocityPath`, `SurfaceImmersion_Primitive_CircularBoundaryParam`, `SurfaceImmersion_Primitive_CircularBoundaryTangencies`, `SurfaceImmersion_Primitive_CircularPrefixMetrics`, `SurfaceImmersion_Primitive_ControlledInteriorLoop`, `SurfaceImmersion_Primitive_JetVelocityCoordinates`, `SurfaceImmersion_Primitive_LoopDensityLinear`, `SurfaceImmersion_Primitive_PeriodicPrimitive`, `SurfaceImmersion_Primitive_VelocityAngleInterpolation`, `SurfaceImmersion_Whitney_BoundaryInvariantCollar`, `SurfaceImmersion_Whitney_CollarDensityMoments`, `SurfaceImmersion_Whitney_CollarVelocity`, `SurfaceImmersion_Whitney_CollarVelocityAngle`, `SurfaceImmersion_Whitney_CollarVelocityCalibration`, `SurfaceImmersion_Whitney_CollarVelocityClock`, `SurfaceImmersion_Whitney_CollarVelocityInverse`, `SurfaceImmersion_Whitney_CollarVelocityMean`, `SurfaceImmersion_Whitney_CollarVelocityPeriod`, `SurfaceImmersion_Whitney_CollarVelocityReparam`, `SurfaceImmersion_Whitney_CollarVelocityTurns`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI003`, `OAIQ249SI004`, `OAIQ249SI005`, `OAIQ249SI006` and `OAIQ249SI007`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_quadratic_family_sum_le`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_smooth_euclidean_four_immersion`, `OAI_ClosedSurfaceR4_PhaseGeometry_good_of_direction_length_pos`, `OAI_ClosedSurfaceR4_PhaseGeometry_reciprocal_second_length_bound`, `OAI_ClosedSurfaceR4_RealModes_realTwoJet_coordinate_prefix_bound` and `OAI_ClosedSurfaceR4_RealModes_realTwoJet_linear_prefix_bound`; the proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_quadratic_family_sum_le` and `OAI_ClosedSurfaceR4_PhaseGeometry_good_of_direction_length_pos`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
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

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- Mathlib d13f23b's `exists_contDiff_support_eq_eq_one_iff` (CircleDomains, q146). -/
theorem _root_.exists_contDiff_support_eq_eq_one_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ∞} {s t : Set E} (hs : IsOpen s)
    (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : E → ℝ, ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1 ∧ Function.support f = s ∧
      (∀ x, x ∈ t ↔ f x = 1) := by
  simpa [contMDiff_iff_contDiff] using
    exists_contMDiff_support_eq_eq_one_iff (modelWithCornersSelf ℝ E) (n := n) hs ht h
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



def WeightedBound (U : Set E) (s : ℝ) (m : ℕ) (C : ℝ) (f : E → F) : Prop :=
  ∀ j ≤ m, ∀ x ∈ U, s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C

lemma WeightedBound.shrink_scale {U : Set E} {s t C : ℝ} {m : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (ht : 0 ≤ t) (hts : t ≤ s) : WeightedBound U t m C f := by
  intro j hj x hx
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht hts j) (norm_nonneg _)).trans (h j hj x hx)

end ClosedSurfaceR4.WeightedEstimates

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

abbrev CVec (n : ℕ) := Fin n → ℂ
abbrev RVec (n : ℕ) := Fin n → ℝ

def realPart {n : ℕ} (Z : CVec n) : RVec n := fun i => (Z i).re

def realPartCLM (n : ℕ) : CVec n →L[ℝ] RVec n :=
  ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i)

lemma realPartCLM_apply {n : ℕ} (Z : CVec n) : realPartCLM n Z = realPart Z := rfl

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.NormalFrame
abbrev Vec := Fin 4 → ℝ

def gramDet (X Y : Vec) : ℝ := (X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) ^ 2

end ClosedSurfaceR4.NormalFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def InTrialBall (U : Set E) (reference : E → F) (r : ℝ) (f : E → F) : Prop :=
  ∀ x ∈ U, ‖f x - reference x‖ < r


def trial (H : E → F) (T : ℝ → (E → F) → E → F) (η : ℝ) : ℕ → E → F
  | 0 => H
  | j + 1 => H - T η (trial H T η j)





structure MeanBounds (U : Set E) (s : ℝ) (reference : E → F) (r : ℝ) (L : ℕ)
    (T : ℝ → (E → F) → E → F) (B K : ℕ → ℝ → ℝ) : Prop where
  B_pos : ∀ m C, 1 ≤ C → 1 ≤ B m C
  K_pos : ∀ m C, 1 ≤ C → 1 ≤ K m C
  smooth : ∀ η, 0 < η → η ≤ 1 → ∀ f, ContDiffOn ℝ ∞ f U →
    InTrialBall U reference r f → ContDiffOn ℝ ∞ (T η f) U
  value : ∀ η, 0 < η → η ≤ 1 → ∀ m C f, 1 ≤ C →
    ContDiffOn ℝ ∞ f U → InTrialBall U reference r f →
    WeightedBound U s (m + L) C f → WeightedBound U s m (η * B m C) (T η f)
  difference : ∀ η, 0 < η → η ≤ 1 → ∀ m C D f g, 1 ≤ C → 0 ≤ D →
    ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g U →
    InTrialBall U reference r f → InTrialBall U reference r g →
    WeightedBound U s (m + L) C f → WeightedBound U s (m + L) C g →
    WeightedBound U s (m + L) D (f - g) →
    WeightedBound U s m (K m C * η * D) (T η f - T η g)



def sizeBound (L : ℕ) (C : ℕ → ℝ) (B : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => C m
  | j + 1, m => C m + B m (sizeBound L C B j (m + L))

def differenceBound (L : ℕ) (C : ℕ → ℝ) (B K : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => B m (C (m + L))
  | j + 1, m => K m (max (sizeBound L C B (j + 1) (m + L))
      (sizeBound L C B j (m + L))) * differenceBound L C B K j (m + L)

end ClosedSurfaceR4.FiniteMean

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
open ClosedSurfaceR4.WeightedEstimates
open Set



abbrev Tensor := Fin 3 → ℝ

end ClosedSurfaceR4.PhaseMean

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

lemma scaled_coordinate_lt {h R x : ℝ} {a : ℤ} (hh : 0 < h) :
    |h⁻¹ * x - a| < R ↔ |x - h * a| < R * h := by
  have he : h⁻¹ * x - a = (x-h*a)/h := by field_simp
  rw [he, abs_div, abs_of_pos hh, div_lt_iff₀ hh]

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridCover
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
attribute [local instance] Classical.propDecidable
abbrev Label := (ZMod 6 × ZMod 6) × Fin 3

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma contDiff_of_tsupport_subset {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx (hfs hh))
    exact contDiffAt_const.congr_of_eventuallyEq hz



end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma tsupport_indicator_subset {U K : Set E} {f : E → F} (hK : IsClosed K)
    (hf : ∀ x ∈ U, x ∉ K → f x = 0) : tsupport (U.indicator f) ⊆ K := by
  classical
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  by_cases hxU : x ∈ U
  · exact hx (by rw [indicator_of_mem hxU, hf x hxU hn])
  · exact hx (indicator_of_notMem hxU _)

lemma contDiff_indicator_of_support {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    (hz : ∀ x ∈ U, x ∉ K → f x = 0) : ContDiff ℝ ∞ (U.indicator f) := by
  classical
  apply contDiff_of_tsupport_subset hU ((tsupport_indicator_subset hK hz).trans hKU)
  apply hf.congr
  intro x hx
  exact indicator_of_mem hx f

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates

lemma inverse_sqrt_smooth : ContDiffOn ℝ ∞ (fun r : ℝ => (Real.sqrt r)⁻¹) (Ioi 0) := by
  apply (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)).inv
  intro r hr
  exact (Real.sqrt_pos.2 hr).ne'

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]

abbrev AtlasPhaseLabel := ι × Fin (Fintype.card PhaseGrid.Label)

end ClosedSurfaceR4

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

abbrev ComplexTensor := Fin 3 → ℂ

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def iteratedDirectional : List A → (A → E) → A → E
  | [], f => f
  | v :: vs, f => fun x => fderiv ℝ (iteratedDirectional vs f) x v

lemma contDiffOn_iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    (hf : ContDiffOn ℝ ∞ f U) (vs : List A) :
    ContDiffOn ℝ ∞ (iteratedDirectional vs f) U := by
  induction vs with
  | nil => exact hf
  | cons v vs ih =>
    exact (ih.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetChainRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

abbrev Base := Fin 2 → ℝ
abbrev Space := Fin 4 → ℝ
abbrev LowIndex := Fin 2 ⊕ (Fin 7 × Fin 4)
abbrev LowJet := LowIndex → ℝ

def coordinateVector (v : Fin 2) : Base := Pi.single v 1

def lowWord : Fin 7 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]

/-- Actual ordered coordinate derivatives; no symmetry convention is needed. -/
def jet (G : Base → Space) (w : List (Fin 2)) (a : Fin 4) (p : Base) : ℝ :=
  iteratedDirectional (w.map coordinateVector) (fun q => G q a) p

def lowJet (G : Base → Space) (p : Base) : LowJet
  | Sum.inl i => p i
  | Sum.inr (w, a) => jet G (lowWord w) a p

lemma jet_smooth {G : Base → Space} (hG : ContDiff ℝ ∞ G) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (jet G w a) := by
  have h := contDiffOn_iteratedDirectional isOpen_univ (contDiff_pi.mp hG a).contDiffOn
    (w.map coordinateVector)
  exact contDiffOn_univ.mp h

lemma lowJet_smooth {G : Base → Space} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (lowJet G) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff
  | inr i => exact jet_smooth hG (lowWord i.1) i.2

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite chart data with inner and outer cutoffs for smoothing on a closed
surface. All chart and cutoff data are chosen independently of the input. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def chart (p : M) : OpenPartialHomeomorph M Base :=
  (chartAt Plane p).trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toOpenPartialHomeomorph

lemma chart_source (p : M) : (chart p).source = (chartAt Plane p).source := by
  simp [chart]

variable [IsManifold planeModel ∞ M]

lemma chart_smooth (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ, Base) ∞ (chart p) (chart p).source := by
  rw [chart_source]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma chart_symm_smooth (p : M) :
    ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ (chart p).symm (chart p).target := by
  have h := (contMDiffOn_chart_symm (I := planeModel) (x := p) (n := ∞)).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contMDiff.contMDiffOn
    (fun x (hx : x ∈ (chart p).target) => by simpa [chart] using hx)
  simpa [chart] using h

/-- The outer cutoff is one on the support of the partition weight and has
its own closed support inside the same chart. -/
structure SmoothingAtlas (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] where
  centers : Finset M
  weight : centers → M → ℝ
  outer : centers → M → ℝ
  weight_smooth : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (weight i)
  weight_support : ∀ i, tsupport (weight i) ⊆ (chart (i : M)).source
  outer_smooth : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (outer i)
  outer_support : ∀ i, tsupport (outer i) ⊆ (chart (i : M)).source
  outer_one : ∀ i x, x ∈ tsupport (weight i) → outer i x = 1
  partition : ∀ x, ∑ i, (weight i x) ^ 2 = 1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingLocalization
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

def localize (p : M) (ψ : M → ℝ) (f : M → V) : Base → V :=
  (chart p).target.indicator (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x))

variable [CompactSpace M]

/-- Both scalar localization and input support are retained in coordinates. -/
lemma localize_tsupport_inter (p : M) {ψ : M → ℝ}
    (hψ : tsupport ψ ⊆ (chart p).source) (f : M → V) :
    tsupport (localize p ψ f) ⊆ (chart p) '' (tsupport ψ ∩ tsupport f) := by
  have hsub : tsupport ψ ∩ tsupport f ⊆ (chart p).source := fun _ hx => hψ hx.1
  have hK : IsCompact ((chart p) '' (tsupport ψ ∩ tsupport f)) :=
    ((isClosed_tsupport ψ).inter (isClosed_tsupport f)).isCompact.image_of_continuousOn
      ((chart p).continuousOn.mono hsub)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_cases ht : x ∈ (chart p).target
  · by_contra hn
    have heq : localize p ψ f x = 0 := by
      by_cases ha : ψ ((chart p).symm x) = 0
      · simp [localize, ht, ha]
      by_cases hb : f ((chart p).symm x) = 0
      · simp [localize, ht, hb]
      exact False.elim (hn ⟨(chart p).symm x,
        ⟨subset_tsupport ψ ha, subset_tsupport f hb⟩, (chart p).right_inv ht⟩)
    exact hx heq
  · exact False.elim (hx (indicator_of_notMem ht _))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def restore (p : M) (χ : M → ℝ) (h : Base → V) : M → V :=
  (chart p).source.indicator (fun x => χ x • h (chart p x))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothing
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

def bundleRestore (i : A.centers) (h : Base → F) (x : M) : E x :=
  A.outer i x • (e i).symmL ℝ x (h (chart (i : M) x))

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

abbrev TensorFiber := Plane →L[ℝ] Plane →L[ℝ] ℝ

local instance tensorModelNormed_r3ec6d4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorModelSpace_r3ec6d4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorModelComplete_r3ec6d4_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

abbrev CovariantTwoTensor (p : M) :=
  TangentSpace planeModel p →L[ℝ] TangentSpace planeModel p →L[ℝ] ℝ

local instance tensorDualAdd_r3ec6d4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance tensorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance tensorModelNormed_r3ec6d4_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorModelSpace_r3ec6d4_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorModelComplete_r3ec6d4_2 : CompleteSpace TensorFiber := inferInstance
local instance tensorDualAdd_r3ec6d4_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

def tensorTriv (i : A.centers) :
    Trivialization TensorFiber (TotalSpace.proj : TotalSpace TensorFiber
      (CovariantTwoTensor (M := M)) → M) :=
  trivializationAt TensorFiber (CovariantTwoTensor (M := M)) (i : M)

instance tensorTriv_mem (i : A.centers) : MemTrivializationAtlas (A.tensorTriv i) := by
  unfold tensorTriv
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SmoothingAtlas
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
open JetPolynomial (Base)

local instance symmetryModelNormed_r3ec6d4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance symmetryModelSpace_r3ec6d4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance symmetryModelComplete_r3ec6d4_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance symmetryDualAdd_r3ec6d4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance symmetryDualSmul_r3ec6d4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
/-- Transpose a covariant tensor by interchanging its two arguments. -/
def tensorTranspose {p : M} (u : CovariantTwoTensor p) : CovariantTwoTensor p :=
  (show TensorFiber from u).flip

omit [IsManifold planeModel ∞ M] in
@[simp] lemma tensorTranspose_apply {p : M} (u : CovariantTwoTensor p)
    (v w : TangentSpace planeModel p) : tensorTranspose u v w = u w v := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variations of the ordered coordinate jets. The position entries
do not vary, and a second-jet variation costs at most two short-scale powers. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma directional_add {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : A → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List A) :
    iteratedDirectional w (fun x => f x + g x) =
      fun x => iteratedDirectional w f x + iteratedDirectional w g x := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional, ih]
    funext x
    have hfs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn w)
    have hgs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hg.contDiffOn w)
    rw [fderiv_fun_add (hfs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) (hgs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x),
      add_apply]

lemma directional_smul {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : A → E}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (w : List A) :
    iteratedDirectional w (fun x => c • f x) = fun x => c • iteratedDirectional w f x := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional, ih]
    funext x
    have hfs := contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn w)
    exact congrArg (fun L : A →L[ℝ] E => L v)
      (((hfs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt.const_smul c).fderiv)

lemma jet_add {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (fun q => G q + H q) w a p = jet G w a p + jet H w a p :=
  congrFun (directional_add (contDiff_pi.mp hG a) (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p

lemma jet_smul {H : Base → Space} (hH : ContDiff ℝ ∞ H)
    (c : ℝ) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (fun q => c • H q) w a p = c * jet H w a p :=
  congrFun (directional_smul (contDiff_pi.mp hH a) c (w.map coordinateVector)) p

def variationLowJet (H : Base → Space) (p : Base) : LowJet
  | .inl _ => 0
  | .inr (i, a) => jet H (lowWord i) a p

lemma variationLowJet_smooth {H : Base → Space} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (variationLowJet H) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiff_const
  | inr i => exact jet_smooth hH (lowWord i.1) i.2

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedWeightedSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted derivative bounds as actual seminorms on smooth fields
with fixed compact support, for finite derivative-loss parametrix iteration. -/
noncomputable section
open TopologicalSpace
open scoped Distributions NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev SupportedField (K : Compacts A) := ContDiffMapSupportedIn A F ⊤ K

def supportedWeightedSeminorm (K : Compacts A) (s : ℝ≥0) (m : ℕ) :
    Seminorm ℝ (SupportedField (F := F) K) :=
  (Finset.range (m + 1)).sup fun j =>
    s ^ j • ContDiffMapSupportedIn.seminorm ℝ A F ⊤ K j

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedCoordinateChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric linear coordinate changes preserve the supported weighted
seminorms exactly. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

def pushSupported (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A) (f : SupportedField (F := F) K) :
    SupportedField (F := F) (K.map e e.continuous) :=
  ⟨f ∘ e.symm, f.contDiff.comp e.symm.contDiff, fun y hy => by
    apply f.zero_on_compl
    intro hx
    exact hy ⟨e.symm y, hx, e.apply_symm_apply y⟩⟩

def pullSupported (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    (f : SupportedField (F := F) (K.map e e.continuous)) : SupportedField (F := F) K :=
  ⟨f ∘ e, f.contDiff.comp e.contDiff, fun x hx => by
    apply f.zero_on_compl
    rintro ⟨z, hz, hzx⟩
    exact hx (e.injective hzx ▸ hz)⟩

def supportedCoordinateEquiv (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A) :
    SupportedField (F := F) K ≃ₗ[ℝ] SupportedField (F := F) (K.map e e.continuous) where
  toFun := pushSupported e K
  invFun := pullSupported e K
  left_inv f := by
    apply DFunLike.ext
    intro x
    change f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  right_inv f := by
    apply DFunLike.ext
    intro x
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  map_add' f g := by
    apply DFunLike.ext
    intro x
    rfl
  map_smul' c f := by
    apply DFunLike.ext
    intro x
    rfl

/-- The two coordinate conventions used by the geometric and jet formulas. -/
def planeCoordinateIsometry : (Fin 2 → ℝ) ≃ₗᵢ[ℝ] ℝ × ℝ where
  toLinearEquiv := LinearEquiv.finTwoArrow ℝ ℝ
  norm_map' x := by
    change max ‖x 0‖ ‖x 1‖ = ‖x‖
    apply le_antisymm
    · exact max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1)
    · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _

end ClosedSurfaceR4.JetPolynomial

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
local instance weightPlaneFiberNormed_r3ec6d4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace_r3ec6d4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance weightPlaneDualAdd_r3ec6d4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul_r3ec6d4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance weightPlaneSectionNormed_r3ec6d4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace_r3ec6d4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def chartWeight (i : A.centers) : Base → ℝ :=
  (chart (i : M)).target.indicator (fun x => A.weight i ((chart (i : M)).symm x))

variable [CompactSpace M]

lemma chartWeight_smooth (i : A.centers) : ContDiff ℝ ∞ (A.chartWeight i) := by
  let K : Set Base := (chart (i : M)) '' tsupport (A.weight i)
  have hK : IsCompact K := (isClosed_tsupport (A.weight i)).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.weight_support i))
  have hKU : K ⊆ (chart (i : M)).target := by
    rintro x ⟨p,hp,rfl⟩
    exact (chart (i : M)).map_source (A.weight_support i hp)
  apply contDiff_indicator_of_support (chart (i : M)).open_target hK.isClosed hKU
    ((A.weight_smooth i).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  intro x hx hnot
  by_contra hz
  exact hnot ⟨(chart (i : M)).symm x,subset_tsupport (A.weight i) hz,(chart (i : M)).right_inv hx⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport smooth compactly supported fields through an actual local
coordinate homeomorphism. Extension by zero preserves the original support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The image compact set for the local coordinate system. -/
def chartSupport (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) : Compacts B :=
  ⟨e '' K, K.isCompact.image_of_continuousOn (e.continuousOn.mono hK)⟩

omit [NormedSpace ℝ A] [NormedSpace ℝ B] in
lemma chartSupport_subset (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) : (chartSupport e K hK : Set B) ⊆ e.target := by
  rintro _ ⟨x,hx,rfl⟩
  exact e.map_source (hK hx)

omit [NormedSpace ℝ B] in
lemma chartPush_zero (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) :
    ∀ y ∈ e.target, y ∉ (chartSupport e K hK : Set B) → f (e.symm y) = 0 := by
  intro y hy hn
  apply f.zero_on_compl
  intro hx
  exact hn ⟨e.symm y,hx,e.right_inv hy⟩

def chartPush (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) :
    SupportedField (F := F) (chartSupport e K hK) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
      (chartSupport_subset e K hK) (f.contDiff.comp_contDiffOn he) (chartPush_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset (chartSupport e K hK).isCompact.isClosed
      (chartPush_zero e K hK f)))

@[simp] lemma chartPush_apply (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) (y : B) :
    chartPush e he K hK f y = e.target.indicator (f ∘ e.symm) y := rfl

def chartPushLM (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) (chartSupport e K hK) where
  toFun := chartPush e he K hK
  map_add' f g := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;> simp [chartPush_apply, hy]
  map_smul' c f := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;> simp [chartPush_apply, hy]

lemma chartPush_eval_source (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K)
    {x : A} (hx : x ∈ e.source) : chartPush e he K hK f (e x) = f x := by
  rw [chartPush_apply, Set.indicator_of_mem (e.map_source hx)]
  simp only [Function.comp_apply, e.left_inv hx]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invertible local-chart transport on supported fields and their linear
operators. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A B F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ A] in
lemma chartPull_zero (e : OpenPartialHomeomorph A B) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) :
    ∀ x ∈ e.source, x ∉ (K : Set A) → f (e x) = 0 := by
  intro x hx hn
  apply f.zero_on_compl
  rintro ⟨z,hz,hez⟩
  have hzx : z = x := by
    have hh := congrArg e.symm hez
    simpa only [e.left_inv (hK hz), e.left_inv hx] using hh
  exact hn (hzx ▸ hz)

def chartPull (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) :
    SupportedField (F := F) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_source K.isCompact.isClosed hK
      (f.contDiff.comp_contDiffOn he) (chartPull_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset K.isCompact.isClosed (chartPull_zero e K hK f)))

@[simp] lemma chartPull_apply (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) (x : A) :
    chartPull e he K hK f x = e.source.indicator (f ∘ e) x := rfl

lemma chartPull_push (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) K) :
    chartPull e he K hK (chartPush e hi K hK f) = f := by
  apply DFunLike.ext
  intro x
  by_cases hx : x ∈ e.source
  · rw [chartPull_apply, Set.indicator_of_mem hx]
    exact chartPush_eval_source e hi K hK f hx
  · rw [chartPull_apply, Set.indicator_of_notMem hx]
    exact (f.zero_on_compl (fun hk => hx (hK hk))).symm

lemma chartPush_pull (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) (f : SupportedField (F := F) (chartSupport e K hK)) :
    chartPush e hi K hK (chartPull e he K hK f) = f := by
  apply DFunLike.ext
  intro y
  by_cases hy : y ∈ e.target
  · rw [chartPush_apply, Set.indicator_of_mem hy]
    change chartPull e he K hK f (e.symm y) = f y
    rw [chartPull_apply, Set.indicator_of_mem (e.map_target hy)]
    simp only [Function.comp_apply, e.right_inv hy]
  · rw [chartPush_apply, Set.indicator_of_notMem hy]
    exact (f.zero_on_compl (fun hk => hy (chartSupport_subset e K hK hk))).symm

def chartEquiv (e : OpenPartialHomeomorph A B)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) (K : Compacts A)
    (hK : (K : Set A) ⊆ e.source) :
    SupportedField (F := F) K ≃ₗ[ℝ] SupportedField (F := F) (chartSupport e K hK) where
  toFun := chartPush e hi K hK
  invFun := chartPull e he K hK
  left_inv := chartPull_push e he hi K hK
  right_inv := chartPush_pull e he hi K hK
  map_add' := (chartPushLM e hi K hK).map_add
  map_smul' := (chartPushLM e hi K hK).map_smul

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedTupleOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tuples of supported linear operators, with actual weighted
seminorm bounds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

variable {A F E ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup E] [Module ℝ E]
  [Fintype ι]

def tupleSupportedLM (K : Compacts A) (L : ι → E →ₗ[ℝ] SupportedField (F := F) K) :
    E →ₗ[ℝ] SupportedField (F := ι → F) K where
  toFun z := ⟨fun p i => L i z p,
    contDiff_pi.mpr (fun i => (L i z).contDiff), fun p hp => by
      funext i
      exact (L i z).zero_on_compl hp⟩
  map_add' z w := by
    apply DFunLike.ext
    intro p
    funext i
    exact congrArg (fun f : SupportedField (F := F) K => f p) ((L i).map_add z w)
  map_smul' c z := by
    apply DFunLike.ext
    intro p
    funext i
    exact congrArg (fun f : SupportedField (F := F) K => f p) ((L i).map_smul c z)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedOperatorTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of differential operators through a fixed isometric coordinate
change, including their finite derivative-loss estimates. -/
noncomputable section
open TopologicalSpace
open scoped NNReal

namespace ClosedSurfaceR4.JetPolynomial

variable {A B F G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def transportSupportedLM (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A)
    (L : SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := G) K) :
    SupportedField (F := F) (K.map e e.continuous) →ₗ[ℝ]
      SupportedField (F := G) (K.map e e.continuous) :=
  (supportedCoordinateEquiv e K).toLinearMap.comp
    (L.comp (supportedCoordinateEquiv e K).symm.toLinearMap)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothParameterIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth parameter dependence of an integral over a fixed compact interval. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def partialDerivative (F : P × ℝ → E) (z : P × ℝ) : P →L[ℝ] E :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P ℝ)

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma contDiff_partialDerivative {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialDerivative F) :=
  (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiff_const

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma partial_hasFDerivAt {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : P) (t : ℝ) :
    HasFDerivAt (fun q => F (q, t)) (partialDerivative F (p, t)) p := by
  have hi : HasFDerivAt (fun q : P => (q, t)) (ContinuousLinearMap.inl ℝ P ℝ) p := by
    simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inl ℝ P ℝ).hasFDerivAt (x := p)).add_const (0, t)
  exact (hF.differentiable (by simp) (p, t)).hasFDerivAt.comp p hi

omit [CompleteSpace E] in
/-- Compactness gives the domination required to differentiate under the
integral. No uniform derivative bound is an extra premise. -/
theorem hasFDerivAt_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (p₀ : P) :
    HasFDerivAt (fun p => ∫ t in a..b, F (p, t))
      (∫ t in a..b, partialDerivative F (p₀, t)) p₀ := by
  have hDs := contDiff_partialDerivative hF
  have hK : IsCompact (closedBall p₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall p₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDs.continuous.continuousOn
  have hcF (p : P) : Continuous (fun t => F (p, t)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hcD (p : P) : Continuous (fun t => partialDerivative F (p, t)) :=
    hDs.continuous.comp (continuous_const.prodMk continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := ball p₀ 1) (bound := fun _ => C) (ball_mem_nhds p₀ zero_lt_one)
  · exact Eventually.of_forall (fun p => (hcF p).aestronglyMeasurable)
  · exact (hcF p₀).intervalIntegrable a b
  · exact (hcD p₀).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro p hp
    exact hC (p, t) ⟨ball_subset_closedBall hp, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t p _ => partial_hasFDerivAt hF p t)

/-- Induction on derivative order; the target Banach space is allowed to
change to a continuous-linear-map space at each induction step. -/
theorem contDiff_integral_nat (a b : ℝ) (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : P × ℝ → E), ContDiff ℝ ∞ F →
      ContDiff ℝ n (fun p => ∫ t in a..b, F (p, t)) := by
  induction n with
  | zero =>
    intro E _ _ _ F hF
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ (fun p => ∫ t in a..b, F (p, t)) from
      fun p => (hasFDerivAt_integral hF a b p).differentiableAt).continuous
  | succ n ih =>
    intro E _ _ _ F hF
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun p => ∫ t in a..b, partialDerivative F (p, t),
      ih (P →L[ℝ] E) (partialDerivative F) (contDiff_partialDerivative hF),
      fun p => hasFDerivAt_integral hF a b p⟩

/-- Integrating a smooth family on a fixed compact interval preserves all
orders of smoothness. -/
theorem contDiff_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_integral_nat a b n E F hF

end ClosedSurfaceR4.SmoothParameterIntegral

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rawPrimitive (f : ℝ → E) (x : ℝ) : E := ∫ t in 0..x, f t

def primitive (f : ℝ → E) (x : ℝ) : E :=
  rawPrimitive f x - ∫ t in 0..1, rawPrimitive f t

omit [CompleteSpace E] in
theorem rawPrimitive_periodic {f : ℝ → E} (hf : Continuous f)
    (hperiod : Function.Periodic f 1) (hmean : (∫ t in 0..1, f t) = 0) :
    Function.Periodic (rawPrimitive f) 1 := by
  intro x
  unfold rawPrimitive
  rw [hperiod.intervalIntegral_add_eq_add 0 x (fun a b => hf.intervalIntegrable a b)]
  simp only [zero_add, hmean, add_zero]

omit [CompleteSpace E] in
theorem primitive_periodic {f : ℝ → E} (hf : Continuous f)
    (hperiod : Function.Periodic f 1) (hmean : (∫ t in 0..1, f t) = 0) :
    Function.Periodic (primitive f) 1 := by
  intro x
  simp only [primitive, rawPrimitive_periodic hf hperiod hmean x]

omit [CompleteSpace E] in
theorem integral_lift_eq_haar (f : UnitAddCircle → E) :
    (∫ t in 0..1, f (t : UnitAddCircle)) = ∫ t, f t ∂AddCircle.haarAddCircle := by
  calc
    _ = ∫ t : UnitAddCircle, f t := by
      simpa only [zero_add] using UnitAddCircle.intervalIntegral_preimage 0 f
    _ = _ := by simpa only [inv_one, one_smul] using
      (AddCircle.integral_haarAddCircle (f := f)).symm

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPeriodicPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jointly smooth normalized primitives with parameters. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiff_rawPrimitive_joint {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : P × ℝ => rawPrimitive (fun t => F (z.1, t)) z.2) := by
  let A : (P × ℝ) × ℝ → E := fun z => F (z.1.1, z.1.2 * z.2)
  have hA : ContDiff ℝ ∞ A := hF.comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have hi := SmoothParameterIntegral.contDiff_integral hA 0 1
  have hs := contDiff_snd.smul hi
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  change (∫ t in 0..z.2, F (z.1, t)) =
    z.2 • (∫ t in 0..1, F (z.1, z.2 * t))
  simpa only [A, rawPrimitive, mul_zero, mul_one, Pi.smul_apply] using
    (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun t => F (z.1, t)) z.2).symm

/-- Normalization by the mean preserves joint smoothness in the parameter
and the real periodic argument. -/
theorem contDiff_primitive_joint {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : P × ℝ => primitive (fun t => F (z.1, t)) z.2) := by
  have hraw := contDiff_rawPrimitive_joint hF
  have hmean := SmoothParameterIntegral.contDiff_integral hraw 0 1
  exact hraw.sub (hmean.comp contDiff_fst)

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalParameterIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parameter integration on an open admissible domain, localized by a smooth cutoff. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
/-- A cutoff supported inside the parameter domain turns a locally smooth
family into a globally smooth family without changing its values near the center. -/
lemma contDiff_supported_smul {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {χ : P → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ S) :
    ContDiff ℝ ∞ (fun z : P × ℝ => χ z.1 • F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.1 ∈ S
  · exact (hχ.comp contDiff_fst).contDiffAt.smul
      ((hF z ⟨hz, mem_univ z.2⟩).contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hz, mem_univ z.2⟩))
  · have hn : z.1 ∉ tsupport χ := fun h => hz (hsupp h)
    have he : χ =ᶠ[𝓝 z.1] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hn] with p hp
      exact image_eq_zero_of_notMem_tsupport hp
    have he' := he.comp_tendsto (continuous_fst.continuousAt :
      Tendsto Prod.fst (𝓝 z) (𝓝 z.1))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [he'] with w hw
    exact (congrArg (fun a : ℝ => a • F w) hw).trans (zero_smul ℝ (F w))

omit [CompleteSpace E] in
lemma exists_smooth_extension_near {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) {p : P} (hp : p ∈ S) :
    ∃ G : P × ℝ → E, ContDiff ℝ ∞ G ∧
      ∀ᶠ q in 𝓝 p, ∀ t : ℝ, G (q, t) = F (q, t) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS p hp
  let χ : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hsupp : tsupport (χ : P → ℝ) ⊆ S := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by change ε / 2 < ε; linarith)).trans hball
  refine ⟨fun z => χ z.1 • F z, contDiff_supported_smul hS hF χ.contDiff hsupp, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with q hq
  intro t
  rw [show χ q = 1 from hq, one_smul]

/-- Smooth parameter integrals require smoothness only over the open parameter
region where the geometric data are admissible. -/
theorem contDiffOn_integral {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) S := by
  apply hS.contDiffOn_iff.mpr
  intro p hp
  obtain ⟨G, hG, he⟩ := exists_smooth_extension_near hS hF hp
  apply (contDiff_integral hG a b).contDiffAt.congr_of_eventuallyEq
  filter_upwards [he] with q hq
  exact intervalIntegral.integral_congr (fun t _ => (hq t).symm)

end ClosedSurfaceR4.SmoothParameterIntegral

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CovarianceCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The covariance solve in paper 094-01, Section 6, equations
`covariance-equation` and `covariance-solve`. The averaging operator below is
the actual normalized Haar integral on the period circle. The finite linear
solve is proved invertible using constant positive speed and connectedness.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

abbrev Period := UnitAddCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Normalized average over one period. -/
def average (f : Period → E) : E := ∫ t, f t ∂AddCircle.haarAddCircle

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_of_continuous {f : Period → E} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact isCompact_univ

omit [CompleteSpace E] in
lemma average_add {f g : Period → E} (hf : Continuous f) (hg : Continuous g) :
    average (fun t => f t + g t) = average f + average g :=
  integral_add (integrable_of_continuous hf) (integrable_of_continuous hg)

omit [CompleteSpace E] in
lemma average_sub {f g : Period → E} (hf : Continuous f) (hg : Continuous g) :
    average (fun t => f t - g t) = average f - average g :=
  integral_sub (integrable_of_continuous hf) (integrable_of_continuous hg)

@[simp] lemma average_const (v : E) : average (fun _ : Period => v) = v := by
  simp [average]

omit [CompleteSpace E] in
lemma average_const_smul (c : ℝ) (f : Period → E) :
    average (fun t => c • f t) = c • average f := integral_smul c f

/-- The covariance operator applied to a vector. -/
def covariance (V : Period → E) (v m : E) : E :=
  average (fun t => inner ℝ (V t - v) m • (V t - v))

def correctedScalar (V : Period → E) (v : E) (q : ℝ)
    (r : Period → ℝ) (m : E) : Period → ℝ :=
  fun t => r t + inner ℝ (V t - v) m / q

def correctedVector (V : Period → E) (v : E) (q : ℝ)
    (r : Period → ℝ) (m : E) : Period → E :=
  fun t => q⁻¹ • (correctedScalar V v q r m t • V t - m)

def fluctuation (r : Period → ℝ) : Period → ℝ := fun t => r t - average r

/-- The covariance defines a linear operator on the orthogonal complement. -/
def covarianceLinearMap (V : Period → E) (hV : Continuous V) (v : E) : E →ₗ[ℝ] E where
  toFun := covariance V v
  map_add' m n := by
    change average (fun t => inner ℝ (V t - v) (m + n) • (V t - v)) = _
    simp_rw [inner_add_right, add_smul]
    exact average_add
      (((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const))
      (((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const))
  map_smul' c m := by
    change average (fun t => inner ℝ (V t - v) (c • m) • (V t - v)) = _
    simp_rw [inner_smul_right, mul_smul]
    exact average_const_smul c _

def meanOperator (V : Period → E) (hV : Continuous V) (v : E) (q : ℝ) : E →ₗ[ℝ] E :=
  LinearMap.id - q⁻¹ • covarianceLinearMap V hV v

omit [CompleteSpace E] in
@[simp] lemma meanOperator_apply (V : Period → E) (hV : Continuous V)
    (v : E) (q : ℝ) (m : E) :
    meanOperator V hV v q m = m - q⁻¹ • covariance V v m := rfl

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPeriodicCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical periodic primitives and angular derivatives in a smooth family. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.SmoothPeriodicCalculus

open CovarianceCorrector PeriodicPrimitive

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def angleDerivative (F : A × ℝ → E) (z : A × ℝ) : E :=
  fderiv ℝ F z (0, 1)

def bundle (f : ℝ → E) (hp : Function.Periodic f 1) (hc : Continuous f) : C(Period, E) :=
  ⟨hp.lift, continuous_coinduced_dom.mpr hc⟩

omit [NormedSpace ℝ E] in
@[simp] lemma bundle_apply (f : ℝ → E) (hp : Function.Periodic f 1) (hc : Continuous f)
    (t : ℝ) : bundle f hp hc (t : Period) = f t := rfl

def bundleFamily (F : A × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) : A → C(Period, E) :=
  fun p => bundle (fun t => F (p, t)) (hp p)
    (hF.continuous.comp (continuous_const.prodMk continuous_id))

@[simp] lemma bundleFamily_apply (F : A × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ p, Function.Periodic (fun t => F (p, t)) 1) (p : A) (t : ℝ) :
    bundleFamily F hF hp p (t : Period) = F (p, t) := rfl

omit [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedSpace ℝ E] in
lemma periodic_lift (F : A → C(Period, E)) (p : A) :
    Function.Periodic (fun t : ℝ => F p (t : Period)) 1 := by
  intro t
  change F p ((t + 1 : ℝ) : Period) = _
  rw [AddCircle.coe_add_period]

variable [CompleteSpace E]

variable [FiniteDimensional ℝ A]

def primitiveFamily (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) : A → C(Period, E) :=
  bundleFamily (fun z : A × ℝ => primitive (fun t : ℝ => F z.1 (t : Period)) z.2)
    (contDiff_primitive_joint hF) (fun p => primitive_periodic
      ((F p).continuous.comp (AddCircle.continuous_mk' 1)) (periodic_lift F p)
      ((integral_lift_eq_haar (F p)).trans (hm p)))

@[simp] lemma primitiveFamily_apply (F : A → C(Period, E))
    (hF : ContDiff ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)))
    (hm : ∀ p, (∫ t, F p t ∂AddCircle.haarAddCircle) = 0) (p : A) (t : ℝ) :
    primitiveFamily F hF hm p (t : Period) = primitive (fun s : ℝ => F p (s : Period)) t := rfl

end ClosedSurfaceR4.SmoothPeriodicCalculus

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

/-- A sum of monomials. Jet factors are independent of the angular variable. -/
inductive Expression where
  | coeff (c : LowJet × ℝ → ℝ)
  | atom (word : List (Fin 2)) (component : Fin 4) (tail : Expression)
  | add (left right : Expression)

namespace Expression

def eval : Expression → (Base → Space) → Base × ℝ → ℝ
  | .coeff c, G, z => c (lowJet G z.1, z.2)
  | .atom w a e, G, z => jet G w a z.1 * eval e G z
  | .add e f, G, z => eval e G z + eval f G z

def mapCoeff (f : (LowJet × ℝ → ℝ) → (LowJet × ℝ → ℝ)) : Expression → Expression
  | .coeff c => .coeff (f c)
  | .atom w a e => .atom w a (mapCoeff f e)
  | .add e g => .add (mapCoeff f e) (mapCoeff f g)

/-- Largest order of a jet factor. Coefficients themselves use jets through order two. -/
def order : Expression → ℕ
  | .coeff _ => 2
  | .atom w _ e => max w.length e.order
  | .add e f => max e.order f.order

/-- Scale loss when the second jet is controlled. -/
def loss : Expression → ℕ
  | .coeff _ => 0
  | .atom w _ e => (w.length - 2) + e.loss
  | .add e f => max e.loss f.loss

def SmoothCoeffs (O : Set LowJet) : Expression → Prop
  | .coeff c => ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)
  | .atom _ _ e => e.SmoothCoeffs O
  | .add e f => e.SmoothCoeffs O ∧ f.SmoothCoeffs O

@[simp] lemma order_mapCoeff (e : Expression) (f) : (e.mapCoeff f).order = e.order := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [mapCoeff, order, ih]
  | add e g ihe ihg => simp only [mapCoeff, order, ihe, ihg]

@[simp] lemma loss_mapCoeff (e : Expression) (f) : (e.mapCoeff f).loss = e.loss := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [mapCoeff, loss, ih]
  | add e g ihe ihg => simp only [mapCoeff, loss, ihe, ihg]

lemma eval_smooth {O : Set LowJet} {S : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {e : Expression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.eval G) (S ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact he.comp (((lowJet_smooth hG).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, Set.mem_univ _⟩)
  | atom w a e ih =>
    exact (((jet_smooth hG w a).comp contDiff_fst).contDiffOn).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first variation of an actual higher-jet polynomial, including the
variation of its smooth second-jet coefficients. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

def variation : Expression → (Base → Space) → (Base → Space) → Base × ℝ → ℝ
  | .coeff c, G, H, z =>
      fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0)
  | .atom w a e, G, H, z =>
      jet H w a z.1 * e.eval G z + jet G w a z.1 * e.variation G H z
  | .add e f, G, H, z => e.variation G H z + f.variation G H z

theorem variation_smooth {O : Set LowJet} (hO : IsOpen O) {U : Set Base}
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) {e : Expression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.variation G H) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    have hc : ContDiffOn ℝ ∞ (fderiv ℝ c) (O ×ˢ Set.univ) :=
      he.fderiv_of_isOpen (hO.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact (hc.comp (((lowJet_smooth hG).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, hz.2⟩)).clm_apply
        (((variationLowJet_smooth hH).comp contDiff_fst).prodMk contDiff_const).contDiffOn
  | atom w a e ih =>
    exact (((jet_smooth hH w a).comp contDiff_fst).contDiffOn.mul (eval_smooth (e := e) hG hQ he)).add
      (((jet_smooth hG w a).comp contDiff_fst).contDiffOn.mul (ih he))
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of the fast phase from arbitrary ordered directional jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates

def phase (τ : ℝ) (φ : Base → ℝ) (p : Base) : ℂ :=
  Complex.exp (Complex.I / (τ : ℂ) * (φ p : ℂ))

lemma phase_smooth {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) :
    ContDiff ℝ ∞ (phase τ φ) :=
  ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ)).cexp)

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial perturbations have one fixed short-scale exponent. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ}

def order (P : Fin n → Expression) : ℕ := Finset.univ.sup (fun l => (P l).order)
def loss (P : Fin n → Expression) : ℕ := Finset.univ.sup (fun l => (P l).loss + 6)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedPhaseOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase multiplication is an actual linear operator on supported smooth
fields, with the same fixed support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℂ ℝ F]

def multiplierLM (K : Compacts Base) (a : Base → ℂ) (ha : ContDiff ℝ ∞ a) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) K where
  toFun H := ⟨fun p => a p • H p, ha.smul H.contDiff, fun p hp => by
    change a p • H p = 0
    simp only [H.zero_on_compl hp, Pi.zero_apply, smul_zero]⟩
  map_add' H J := by
    apply DFunLike.ext
    intro p
    exact smul_add (a p) (H p) (J p)
  map_smul' c H := by
    apply DFunLike.ext
    intro p
    exact smul_comm (a p) c (H p)

namespace ModulatedJets

def phaseLM (K : Compacts Base) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) K :=
  multiplierLM K (phase τ φ) (phase_smooth hφ τ)

def inversePhaseLM (K : Compacts Base) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) K :=
  phaseLM K hφ.neg τ

end ModulatedJets
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariationLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual polynomial first variation is linear in its smooth direction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_add {H K : Base → Space}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (p : Base) :
    variationLowJet (fun q => H q + K q) p = variationLowJet H p + variationLowJet K p := by
  funext i
  cases i with
  | inl i => simp [variationLowJet]
  | inr i => exact jet_add hH hK (lowWord i.1) i.2 p

lemma variationLowJet_smul {H : Base → Space} (hH : ContDiff ℝ ∞ H)
    (c : ℝ) (p : Base) :
    variationLowJet (fun q => c • H q) p = c • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [variationLowJet]
  | inr i => exact jet_smul hH c (lowWord i.1) i.2 p

namespace Expression

lemma variation_add (e : Expression) (G : Base → Space) {H K : Base → Space}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (z : Base × ℝ) :
    e.variation G (fun q => H q + K q) z = e.variation G H z + e.variation G K z := by
  induction e with
  | coeff c =>
    simp only [variation, variationLowJet_add hH hK]
    have hp : (variationLowJet H z.1 + variationLowJet K z.1, (0 : ℝ)) =
        (variationLowJet H z.1, 0) + (variationLowJet K z.1, 0) := by simp
    rw [hp, map_add]
  | atom w a e ih =>
    simp only [variation, jet_add hH hK, ih]
    ring
  | add e f ihe ihf =>
    simp only [variation, ihe, ihf]
    ring

lemma variation_smul (e : Expression) (G : Base → Space) {H : Base → Space}
    (hH : ContDiff ℝ ∞ H) (c : ℝ) (z : Base × ℝ) :
    e.variation G (fun q => c • H q) z = c * e.variation G H z := by
  induction e with
  | coeff d =>
    simp only [variation, variationLowJet_smul hH]
    have hp : (c • variationLowJet H z.1, (0 : ℝ)) = c • (variationLowJet H z.1, (0 : ℝ)) := by simp
    rw [hp, map_smul]
    rfl
  | atom w a e ih =>
    simp only [variation, jet_smul hH, ih]
    ring
  | add e f ihe ihf =>
    simp only [variation, ihe, ihf]
    ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariationSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearized polynomial operators preserve the support of the varying
field, even when the coefficients are only smooth near that support. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma tsupport_iteratedDirectional {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : List A) (f : A → E) :
    tsupport (iteratedDirectional w f) ⊆ tsupport f := by
  induction w with
  | nil => exact Set.Subset.rfl
  | cons v w ih => exact (tsupport_fderiv_apply_subset ℝ v).trans ih

lemma tsupport_jet (H : Base → Space) (w : List (Fin 2)) (a : Fin 4) :
    tsupport (jet H w a) ⊆ tsupport H :=
  (tsupport_iteratedDirectional (w.map coordinateVector) (fun p => H p a)).trans
    (tsupport_comp_subset (g := fun v : Space => v a) rfl H)

lemma variationLowJet_zero_of_notMem {H : Base → Space} {p : Base} (hp : p ∉ tsupport H) :
    variationLowJet H p = 0 := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    change jet H (lowWord i.1) i.2 p = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_jet H (lowWord i.1) i.2 h))

namespace Expression

lemma variation_zero_of_notMem (e : Expression) (G : Base → Space) {H : Base → Space}
    {p : Base} (hp : p ∉ tsupport H) (t : ℝ) : e.variation G H (p, t) = 0 := by
  induction e with
  | coeff c =>
    simp only [variation, variationLowJet_zero_of_notMem hp]
    change fderiv ℝ c (lowJet G p, t) (0 : LowJet × ℝ) = 0
    exact map_zero _
  | atom w a e ih =>
    have hj : jet H w a p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_jet H w a h))
    simp only [variation, hj, ih, zero_mul, mul_zero, add_zero]
  | add e f ihe ihf => simp only [variation, ihe, ihf, add_zero]

lemma tsupport_variation (e : Expression) (G H : Base → Space) (t : ℝ) :
    tsupport (fun p => e.variation G H (p, t)) ⊆ tsupport H := by
  apply closure_minimal _ (isClosed_tsupport H)
  intro p hp
  by_contra h
  exact hp (e.variation_zero_of_notMem G h t)

theorem variation_smooth_global {O : Set LowJet} (hO : IsOpen O) {U K : Set Base}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) {e : Expression}
    (he : e.SmoothCoeffs O) {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) (hHsupp : tsupport H ⊆ K) (t : ℝ) :
    ContDiff ℝ ∞ (fun p => e.variation G H (p, t)) := by
  have hlocal := (variation_smooth hO hG hH hQ he).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hp => ⟨hp, Set.mem_univ t⟩)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ U
  · exact (hlocal p hp).contDiffAt (hU.mem_nhds hp)
  · have hpk : p ∉ K := fun hk => hp (hKU hk)
    have heq : (fun q => e.variation G H (q, t)) =ᶠ[nhds p] (fun _ => 0) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hpk] with q hq
      exact e.variation_zero_of_notMem G (fun hs => hq (hHsupp hs)) t
    exact contDiffAt_const.congr_of_eventuallyEq heq

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedPolynomialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual polynomial linearization as an operator on smooth fields of
fixed compact support, with its finite derivative-loss seminorm estimate. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

variable {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}

def variationLM (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ) :
    SupportedField (F := Space) K →ₗ[ℝ] SupportedField (F := ℝ) K where
  toFun H := ContDiffMapSupportedIn.of_support_subset
    (e.variation_smooth_global hO hU K.isCompact.isClosed hKU he hG H.contDiff hQ H.tsupport_subset t)
    (subset_closure.trans ((e.tsupport_variation G H t).trans H.tsupport_subset))
  map_add' H J := by
    apply DFunLike.ext
    intro p
    exact e.variation_add G H.contDiff J.contDiff (p, t)
  map_smul' c H := by
    apply DFunLike.ext
    intro p
    exact e.variation_smul G H.contDiff c (p, t)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ComplexifiedPolynomialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complexification of the actual supported polynomial linearization. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

def realFieldCLM : (Fin 4 → ℂ) →L[ℝ] Space :=
  ContinuousLinearMap.pi fun a => Complex.reCLM.comp (ContinuousLinearMap.proj a)

def imagFieldCLM : (Fin 4 → ℂ) →L[ℝ] Space :=
  ContinuousLinearMap.pi fun a => Complex.imCLM.comp (ContinuousLinearMap.proj a)

namespace Expression

def complexVariationLM {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ℂ) K :=
  let R := variationLM hO hU he hG hQ K hKU t
  (ContDiffMapSupportedIn.postcompLM Complex.ofRealCLM).comp
      (R.comp (ContDiffMapSupportedIn.postcompLM realFieldCLM)) +
    (ContDiffMapSupportedIn.postcompLM (Complex.I • Complex.ofRealCLM)).comp
      (R.comp (ContDiffMapSupportedIn.postcompLM imagFieldCLM))

end Expression
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
open WeightedEstimates ModulatedJets

namespace Expression

def conjugatedVariationLM {O : Set LowJet} {U : Set Base} {G : Base → Space} {e : Expression}
    (hO : IsOpen O) (hU : IsOpen U) (he : e.SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (τ t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ℂ) K :=
  (inversePhaseLM K hφ τ).comp
    ((complexVariationLM hO hU he hG hQ K hKU t).comp (phaseLM K hφ τ))

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated derivative of the actual finite polynomial perturbation,
with its fixed scale loss and linear dependence on epsilon. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def conjugatedLM (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ℂ) K :=
  ∑ l, ε ^ (l.val + 1) •
    (P l).conjugatedVariationLM hO hU (hP l) hG hQ K hKU hφ τ t

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPerturbationOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor-valued polynomial perturbations inherit one fixed derivative
budget and one fixed short-scale exponent from their three components. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def tensorOrder (P : Fin 3 → Fin n → Expression) : ℕ := Finset.univ.sup (fun i => order (P i))
def tensorLoss (P : Fin 3 → Fin n → Expression) : ℕ := Finset.univ.sup (fun i => loss (P i))

def tensorConjugatedLM (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K :=
  tupleSupportedLM K (fun i => conjugatedLM hO hU (P i) (hP i) hG hQ K hKU hφ τ ε t)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FixedMeanSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean correction for one fixed operator with derivative loss.
The smallness threshold is uniform in the operator; no infinite-dimensional
inverse or convergence of a derivative-losing iteration is asserted. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rescaledMean (η : ℝ) (A : (E → F) → E → F) (θ : ℝ) (f : E → F) : E → F :=
  (θ / η) • A f

/-- The actual finite sequence depends only on the fixed mean operator. -/
def fixedTrial (H : E → F) (A : (E → F) → E → F) (j : ℕ) : E → F :=
  trial H (fun _ => A) 1 j

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSupportedWeights
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

def chartWeightCompact (i : A.centers) : Compacts JetPolynomial.Base :=
  ⟨(chart (i : M)) '' tsupport (A.weight i),
    (isClosed_tsupport (A.weight i)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (A.weight_support i))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

lemma tsupport_comp_preimage {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero V]
    (f : X → V) (g : Y → X) (hg : Continuous g) : tsupport (f ∘ g) ⊆ g ⁻¹' tsupport f := by
  apply closure_minimal _ ((isClosed_tsupport f).preimage hg)
  intro y hy
  exact subset_tsupport f hy

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

abbrev CurvePlane := ℝ × ℝ

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested compact cutoffs in finite-dimensional parameter spaces. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma compact_open_thickening {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter isOpen_ball).mem_nhdsSet.mpr (subset_inter hKU hr))
  refine ⟨V, hV, hKV, ?_, fun x hx => (hVU hx).1⟩
  exact (isCompact_closedBall (0 : E) r).of_isClosed_subset isClosed_closure
    (fun x hx => ball_subset_closedBall (hVU hx).2)

theorem compact_cutoff {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨V, hV, hKV, hVc, hVU⟩ := compact_open_thickening hK hU hKU
  obtain ⟨χ, hχ, hχr, hχs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV hK.isClosed hKV
  have hs : tsupport χ = closure V := by
    change closure (Function.support χ) = closure V
    rw [hχs]
  refine ⟨χ, hχ, ?_, fun x => hχr (mem_range_self x), ?_, ?_⟩
  · change IsCompact (tsupport χ)
    rw [hs]
    exact hVc
  · rw [hs]
    exact hVU
  · exact fun x hx => (hχone x).mp hx

/-- The inner cutoff is one on an open collar, and the outer one is one
on the whole closed support of the inner cutoff. -/
theorem nested_compact_cutoffs {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ φ χ : E → ℝ, ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ χ ∧
        HasCompactSupport φ ∧ HasCompactSupport χ ∧
        (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
        tsupport χ ⊆ U ∧ tsupport φ ⊆ U ∧
        (∀ x ∈ W, φ x = 1) ∧ (∀ x ∈ tsupport φ, χ x = 1) := by
  obtain ⟨V, hV, hKV, hVc, hVU⟩ := compact_open_thickening hK hU hKU
  obtain ⟨W, hW, hKW, hWc, hWV⟩ := compact_open_thickening hK hV hKV
  obtain ⟨φ, hφ, hφc, hφr, hφs, hφone⟩ := compact_cutoff hWc hV hWV
  obtain ⟨χ, hχ, hχc, hχr, hχs, hχone⟩ := compact_cutoff hVc hU hVU
  refine ⟨W, hW, hKW, ?_, φ, χ, hφ, hχ, hφc, hχc, hφr, hχr, hχs,
    hφs.trans (subset_closure.trans hVU), ?_, ?_⟩
  · exact subset_closure.trans (hWV.trans (subset_closure.trans hVU))
  · exact fun x hx => hφone x (subset_closure hx)
  · exact fun x hx => hχone x (subset_closure (hφs hx))

omit [FiniteDimensional ℝ E] in
lemma supported_local_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : E → ℝ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    exact (congrArg (fun t : ℝ => t • f y) hy).trans (zero_smul ℝ _)

theorem compact_smooth_extension {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∃ g : E → F, ContDiff ℝ ∞ g ∧ EqOn g f W := by
  obtain ⟨W, hW, hKW, hWU, φ, χ, hφ, _, _, _, _, _, _, hφs, hφone, _⟩ :=
    nested_compact_cutoffs hK hU hKU
  exact ⟨W, hW, hKW, hWU, fun x => φ x • f x,
    supported_local_smul hU hφ hf hφs, fun x hx => by simp only [hφone x hx, one_smul]⟩

end ClosedSurfaceR4.CollarVelocity

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
open JetPolynomial (Base)

def tangentRay (b : Bool) (t : ℝ) : Base :=
  if b then ![t,1] else ![1,t]

end ClosedSurfaceR4.FiniteOrderSmoothing

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
abbrev ProjectionTarget (n : ℕ) := EuclideanSpace ℝ (Fin n)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionSlopeDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of a graph-direction coordinate. At a projection kernel
its derivative is exactly the projected derivative divided by the height. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def tangentRayVelocity (b : Bool) : Base :=
  if b then ![1,0] else ![0,1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TangentSlopeLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact linearization of the projective tangent-direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

def directionJetLinearization
    (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ) (b : Bool) (z : Base × ℝ) :
    Base × ℝ →L[ℝ] ProjectionTarget n × ℝ :=
  (H z.1).comp ((ContinuousLinearMap.snd ℝ Base ℝ).smulRight (tangentRayVelocity b)) +
    ((fderiv ℝ H z.1).comp (ContinuousLinearMap.fst ℝ Base ℝ)).flip (tangentRay b z.2)

@[simp] lemma directionJetLinearization_apply
    (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ) (b : Bool) (z w : Base × ℝ) :
    directionJetLinearization H b z w =
      w.2 • H z.1 (tangentRayVelocity b) +
        fderiv ℝ H z.1 w.1 (tangentRay b z.2) := by
  change H z.1 (w.2 • tangentRayVelocity b) +
    fderiv ℝ H z.1 w.1 (tangentRay b z.2) = _
  rw [map_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FiniteChartTranslationBound
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smallness simultaneously in any fixed finite collection of compact
chart regions. The bound is independent of the translated map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [Fintype ι]

def ChartDerivativeClose (p : ι → M) (S : ι → Set Base)
    (f g : M → ProjectionTarget 3) (ε : ℝ) : Prop :=
  ∀ i x, x ∈ S i → ‖fderiv ℝ (g ∘ (chart (p i)).symm) x-
    fderiv ℝ (f ∘ (chart (p i)).symm) x‖ < ε

end ClosedSurfaceR4.FiniteOrderSmoothing

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

local instance nonparallelVolumeHaar_r3ec6d4_1 : (volume : Measure CurvePlane).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
def covectorDet (v w : CurvePlane) : ℝ := v.1*w.2-v.2*w.1

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summability of the exact-correction scales

The iteration uses `t ↦ t^(6/5)`. For an explicit sufficiently small initial
scale, the entire sequence is dominated by a geometric series. This gives
the displacement budget needed for the exact correction.
-/

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology

/-- The fast-decaying scale used in successive smoothing steps. -/
noncomputable def correctionScale (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => (correctionScale t n) ^ (6 / 5 : ℝ)

lemma correctionScale_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ correctionScale t n := by
  induction n with
  | zero => exact ht
  | succ n hn => exact Real.rpow_nonneg hn _

lemma scale_step_le_half {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 32) :
    t ^ (6 / 5 : ℝ) ≤ t / 2 := by
  have hfifth : t ^ (1 / 5 : ℝ) ≤ 1 / 2 := by
    calc
      _ ≤ ((1 / 2 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
        apply Real.rpow_le_rpow ht _ (by norm_num)
        norm_num at hsmall ⊢
        exact hsmall
      _ = 1 / 2 := by
        rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
        norm_num
  by_cases hzero : t = 0
  · subst t
    norm_num
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.rpow_add hpos,
      Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hfifth ht]

/-- A concrete geometric majorant, independent of the later block lengths. -/
theorem correctionScale_le_geometric {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 32)
    (n : ℕ) : correctionScale t n ≤ t * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [correctionScale]
  | succ n hn =>
    have hhalf : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnt : correctionScale t n ≤ t := hn.trans (by nlinarith)
    have hstep := scale_step_le_half (correctionScale_nonneg ht n) (hnt.trans hsmall)
    change (correctionScale t n) ^ (6 / 5 : ℝ) ≤ _
    calc
      _ ≤ correctionScale t n / 2 := hstep
      _ ≤ (t * (1 / 2 : ℝ) ^ n) / 2 := by linarith
      _ = t * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- The exact-correction scales have total mass strictly less than `1/4`. -/
theorem correctionScale_summable {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 32) :
    Summable (correctionScale t) ∧ (∑' n, correctionScale t n) < 1 / 4 := by
  have hgeom : Summable (fun n : ℕ => t * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left t
  have hs : Summable (correctionScale t) :=
    Summable.of_nonneg_of_le (correctionScale_nonneg ht)
      (correctionScale_le_geometric ht hsmall) hgeom
  refine ⟨hs, ?_⟩
  have hle := hs.tsum_le_tsum (correctionScale_le_geometric ht hsmall) hgeom
  have hsum : (∑' n : ℕ, t * (1 / 2 : ℝ) ^ n) = 2 * t := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
    ring
  rw [hsum] at hle
  linarith

end ClosedSurfaceR4.ExactCorrection

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionScaleControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and the cumulative displacement budget for the actual scales. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace ClosedSurfaceR4.ExactCorrection

lemma correctionScale_pos {t : ℝ} (ht : 0 < t) (n : ℕ) :
    0 < correctionScale t n := by
  induction n with
  | zero => exact ht
  | succ n hn => exact Real.rpow_pos_of_pos hn _

lemma correctionScale_le_initial {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) (n : ℕ) :
    correctionScale t n ≤ t := by
  apply (correctionScale_le_geometric ht hsmall n).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) : (1/2 : ℝ)^n ≤ 1) ht

lemma correctionScale_tsum_le {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) :
    (∑' n, correctionScale t n) ≤ 2*t := by
  have hgeom : Summable (fun n : ℕ => t*(1/2 : ℝ)^n) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).mul_left t
  have hh := (correctionScale_summable ht hsmall).1.tsum_le_tsum
    (correctionScale_le_geometric ht hsmall) hgeom
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma correctionScale_partial_sum_le {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) (N : ℕ) :
    ∑ n ∈ Finset.range N, correctionScale t n ≤ 2*t := by
  apply le_trans _ (correctionScale_tsum_le ht hsmall)
  exact (correctionScale_summable ht hsmall).1.sum_le_tsum (Finset.range N)
    (fun n _ => correctionScale_nonneg ht n)

lemma correction_displacement_budget {t ρ : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32)
    (hρ : 0 ≤ ρ) (N : ℕ) :
    ρ/8 + ρ*(∑ n ∈ Finset.range N, correctionScale t n) ≤ ρ/4 := by
  have hh := mul_le_mul_of_nonneg_left (correctionScale_partial_sum_le ht hsmall N) hρ
  have hs := mul_le_mul_of_nonneg_left hsmall hρ
  nlinarith

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ExactCorrectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing the correction sequence to a smooth isometric limit

A correction sequence with eventually summable bounds at every derivative
order converges smoothly in coordinate space. Convergence of its pullback
metrics then gives an isometric immersion whenever the limiting metric is
positive definite.
-/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Finite-stage maps, with the initial map kept separate from the corrections. -/
def partialMap (F : E → V) (U : ℕ → E → V) (N : ℕ) (x : E) : V :=
  F x + ∑ n ∈ Finset.range N, U n x

/-- The limit map defined by the convergent correction series. -/
def limitMap (F : E → V) (U : ℕ → E → V) (x : E) : V :=
  F x + ∑' n, U n x

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitPowerThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit integer-power thresholds for the finitely many real powers
used by the first correction block. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

/-- The exponent of this threshold depends only on a lower bound for the
positive exponent, not on either numerical constant. -/
def powerThreshold (n : ℕ) (c b : ℝ) : ℝ := (min 1 (b/(c+1)))^n

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ExplicitCorrectionBudgetThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit scale preserving the input and metric correction budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

def correctionBudgetThreshold (A B a N L : ℝ) : ℝ :=
  min (powerThreshold 5 |N*(1+B)| (B-A))
    (powerThreshold 5 |L*(1+2*B)| (a/8))

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular derivatives, averaging, and normalized primitives act only on
smooth low-jet coefficients, preserving polynomial jet order and scale loss. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

def angle (e : Expression) : Expression := e.mapCoeff angleDerivative

def mean (e : Expression) : Expression :=
  e.mapCoeff (fun c z => ∫ t in 0..1, c (z.1, t))

def primitive (e : Expression) : Expression :=
  e.mapCoeff (fun c z => PeriodicPrimitive.primitive (fun t => c (z.1, t)) z.2)

@[simp] lemma order_angle (e : Expression) : e.angle.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_angle (e : Expression) : e.angle.loss = e.loss := loss_mapCoeff _ _
@[simp] lemma order_mean (e : Expression) : e.mean.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_mean (e : Expression) : e.mean.loss = e.loss := loss_mapCoeff _ _
@[simp] lemma order_primitive (e : Expression) : e.primitive.order = e.order := order_mapCoeff _ _
@[simp] lemma loss_primitive (e : Expression) : e.primitive.loss = e.loss := loss_mapCoeff _ _

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear operators in the angular variable preserve higher-jet polynomials.
This includes operators whose coefficients depend smoothly on the second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def liftOperator (T : LowJet → (ℝ → ℝ) → ℝ → ℝ) (e : Expression) : Expression :=
  e.mapCoeff (fun c z => T z.1 (fun t => c (z.1, t)) z.2)

@[simp] lemma order_liftOperator (T : LowJet → (ℝ → ℝ) → ℝ → ℝ) (e : Expression) :
    (e.liftOperator T).order = e.order := order_mapCoeff _ _

@[simp] lemma loss_liftOperator (T : LowJet → (ℝ → ℝ) → ℝ → ℝ) (e : Expression) :
    (e.liftOperator T).loss = e.loss := loss_mapCoeff _ _

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CovarianceParameter
attribute [-simp] _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.bundleFamily_apply _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.bundle_apply _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.primitiveFamily_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Smooth parameter dependence of the actual finite covariance solve.  Averaging
is a bounded linear map on continuous periodic functions; the covariance is
a quadratic map on that Banach space.  Thus no regularity assumption on the
inverse matrix is needed.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

section PeriodicMaps

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Apply a continuous bilinear map pointwise to continuous periodic maps. -/
def periodicBilinear (B : E →L[ℝ] F →L[ℝ] G) :
    C(Period, E) →L[ℝ] C(Period, F) →L[ℝ] C(Period, G) := by
  let b : C(Period, E) → C(Period, F) → C(Period, G) := fun f g =>
    ⟨fun t => B (f t) (g t), (B.continuous.comp f.continuous).clm_apply g.continuous⟩
  let L : C(Period, E) →ₗ[ℝ] C(Period, F) →ₗ[ℝ] C(Period, G) :=
    LinearMap.mk₂ ℝ b
      (by intros; ext; simp [b, map_add])
      (by intros; ext; simp [b, map_smul])
      (by intros; ext; simp [b, map_add])
      (by intros; ext; simp [b, map_smul])
  exact L.mkContinuous₂ ‖B‖ (by
    intro f g
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    exact (B.le_opNorm₂ (f t) (g t)).trans (by
      gcongr
      · exact f.norm_coe_le_norm t
      · exact g.norm_coe_le_norm t))

@[simp] theorem periodicBilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : C(Period, E)) (g : C(Period, F)) (t : Period) :
    periodicBilinear B f g t = B (f t) (g t) := rfl

variable [CompleteSpace E]

/-- The normalized Haar average, bundled with its norm bound. -/
def averageCLM : C(Period, E) →L[ℝ] E :=
  ({ toFun := fun f => ∫ t, f t ∂AddCircle.haarAddCircle
     map_add' := fun f g => integral_add
       (integrable_of_continuous f.continuous) (integrable_of_continuous g.continuous)
     map_smul' := fun c f => integral_smul c f } : C(Period, E) →ₗ[ℝ] E).mkContinuous
    1 (by
      intro f
      have h := norm_integral_le_of_norm_le_const
        (μ := AddCircle.haarAddCircle) (f := fun t => f t)
        (Filter.Eventually.of_forall f.norm_coe_le_norm)
      simpa using h)

omit [CompleteSpace E] in
@[simp] theorem averageCLM_apply (f : C(Period, E)) :
    averageCLM f = ∫ t, f t ∂AddCircle.haarAddCircle := rfl

def centeredPeriodic (V : C(Period, E)) : C(Period, E) :=
  V - ContinuousMap.const Period (averageCLM V)

end PeriodicMaps

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The covariance as a quadratic expression in a continuous periodic map. -/
def covarianceCLM (V : C(Period, E)) : E →L[ℝ] E :=
  averageCLM (periodicBilinear (InnerProductSpace.rankOne ℝ)
    (centeredPeriodic V) (centeredPeriodic V))

def meanCLM (V : C(Period, E)) (q : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - q⁻¹ • covarianceCLM V

def weightedAverage (V : C(Period, E)) (r : C(Period, ℝ)) : E :=
  averageCLM (periodicBilinear (ContinuousLinearMap.lsmul ℝ ℝ) r V)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem weightedAverage_apply (V : C(Period, E)) (r : C(Period, ℝ)) :
    weightedAverage V r = average (fun t => r t • V t) := rfl

def covarianceSolution (V : C(Period, E)) (r : C(Period, ℝ)) (q : ℝ) : E :=
  (meanCLM V q).inverse (weightedAverage V r)

def parameterCorrector (V : P → C(Period, E)) (r : P → C(Period, ℝ))
    (q : P → ℝ) (x : P) : Period → E :=
  correctedVector (V x) (average (V x)) (q x) (r x)
    (covarianceSolution (V x) (r x) (q x))

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JointCovarianceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the covariance solve from the joint position-angle data. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contDiff_average_joint {V : P → C(Period, E)}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period))) :
    ContDiff ℝ ∞ (fun p => average (V p)) := by
  have hi := SmoothParameterIntegral.contDiff_integral hV 0 1
  simpa only [PeriodicPrimitive.integral_lift_eq_haar, average] using hi

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalCovarianceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The covariance correction is smooth on the open admissible geometric domain. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma contDiffOn_average_joint {V : P → C(Period, E)} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => average (V p)) S := by
  have hi := SmoothParameterIntegral.contDiffOn_integral hS hV 0 1
  simpa only [PeriodicPrimitive.integral_lift_eq_haar, average] using hi

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CovarianceRealOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual covariance correction acting on real-parameter forcing.
This form exposes linearity and does not require separate periodicity proofs
for the individual coefficients of a jet polynomial. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def realMoment (V : C(Period, E)) (r : ℝ → ℝ) : E :=
  ∫ t in 0..1, r t • V (t : Period)

def realMeanSolution (V : C(Period, E)) (q : ℝ) (r : ℝ → ℝ) : E :=
  (meanCLM V q).inverse (realMoment V r)

def realCorrector (V : C(Period, E)) (q : ℝ) (r : ℝ → ℝ) (t : ℝ) : E :=
  let m := realMeanSolution V q r
  q⁻¹ • ((r t + inner ℝ (V (t : Period) - average V) m / q) • V (t : Period) - m)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual covariance inversion preserves finite polynomial dependence on
higher jets. Its inverse matrix depends only on the low-jet geometric data. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def covariance (V : LowJet → C(Period, E)) (q : LowJet → ℝ) (L : E →L[ℝ] ℝ)
    (e : Expression) : Expression :=
  e.liftOperator (fun Q f t => L (realCorrector (V Q) (q Q) f t))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma order_covariance (V : LowJet → C(Period, E)) (q : LowJet → ℝ)
    (L : E →L[ℝ] ℝ) (e : Expression) : (e.covariance V q L).order = e.order :=
  order_liftOperator _ _

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma loss_covariance (V : LowJet → C(Period, E)) (q : LowJet → ℝ)
    (L : E →L[ℝ] ℝ) (e : Expression) : (e.covariance V q L).loss = e.loss :=
  loss_liftOperator _ _

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialOperations
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def neg (e : Expression) : Expression := e.mapCoeff (fun c z => -c z)
def sub (e f : Expression) : Expression := .add e f.neg

@[simp] lemma eval_neg (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    e.neg.eval G z = -e.eval G z := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [neg, mapCoeff, eval] at *; rw [ih]; ring
  | add e f ihe ihf => simp only [neg, mapCoeff, eval] at *; rw [ihe, ihf]; ring

@[simp] lemma eval_sub (e f : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.sub f).eval G z = e.eval G z - f.eval G z := by
  simp only [sub, eval, eval_neg, sub_eq_add_neg]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldCorrectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The correction-series limit on the surface

The bounds are imposed on smooth coordinate representatives on a fixed
neighborhood of each point. They may depend on the chart, and are only
eventual in the correction index for each derivative order.
-/

noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

open Filter Manifold
open scoped Topology ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def manifoldPartialMap (F : M → Space) (U : ℕ → M → Space) (N : ℕ) (x : M) : Space :=
  F x + ∑ n ∈ Finset.range N, U n x

def manifoldLimitMap (F : M → Space) (U : ℕ → M → Space) (x : M) : Space :=
  F x + ∑' n, U n x

end ClosedSurfaceR4.ExactCorrection

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

abbrev Base := ℝ × ℝ

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitFixedOrderThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-order scale conditions with one explicitly specified
threshold. Its reciprocal is polynomial in the finite numerical budgets. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection

def fixedOrderNumericalBudget (k : ℕ) (D B K : ℝ) (C : ℕ → ℝ) : ℝ :=
  2+D*B+K+∑ m ∈ Finset.range (k/2+1), |C m|

def fixedOrderThreshold (k : ℕ) (ρ a η D B K : ℝ) (C : ℕ → ℝ) : ℝ :=
  powerThreshold 10 (fixedOrderNumericalBudget k D B K C) (min η (min (ρ/4) (a/8)))

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GeometricScaleThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The grid scale-ratio threshold has a polynomial reciprocal. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

def geometricScaleThreshold (a E : ℝ) (e : ℕ) (x : ℝ) : ℝ :=
  min 1 ((a-a/2)/(2*(E*x^e)))

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetPullbackExpressions
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator
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

/-- The position stored in a positional two-jet. -/
def lowPosition : LowJet →L[ℝ] Base :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (.inl i))

@[simp] lemma lowPosition_lowJet (G : Base → Space) (x : Base) :
    lowPosition (lowJet G x) = x := rfl

end ClosedSurfaceR4.JetPolynomial

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
section
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev surfaceDifferential (F : M → V) (p : M) : TangentSpace planeModel p →L[ℝ] V :=
  mfderiv planeModel 𝓘(ℝ,V) F p

end
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def inducedForm (F : M → V) (p : M) (v w : TangentSpace planeModel p) : ℝ :=
  inner ℝ (surfaceDifferential F p v) (surfaceDifferential F p w)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular clock associated to a positive periodic density of mass one. -/
noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
  {ρ : B × ℝ → ℝ} {U : Set B}

def clock (ρ : B × ℝ → ℝ) (b : B) (t : ℝ) : ℝ := ∫ s in 0..t, ρ (b, s)

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
@[simp] lemma clock_zero (ρ : B × ℝ → ℝ) (b : B) : clock ρ b 0 = 0 := by simp [clock]

end ClosedSurfaceR4.PositiveDensity

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

def inverseClock (ρ : B × ℝ → ℝ) (b : B) (θ : ℝ) : ℝ :=
  Function.invFun (clock ρ b) θ

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveDensityReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reparametrization converts an exact positive weighted mean into the uniform mean. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ρ : B × ℝ → ℝ} {F : B × ℝ → E} {U : Set B}

def reparametrize (ρ : B × ℝ → ℝ) (F : B × ℝ → E) (z : B × ℝ) : E :=
  F (z.1, inverseClock ρ z.1 z.2)

end ClosedSurfaceR4.PositiveDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit small circular arc and positive averaging density. This gives
an alternative collar construction without solving a squared-amplitude equation. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

/-- Rational parametrization of a small arc around `(1,0)`. -/
def arcX (a t : ℝ) : ℝ := (1 - (a * Real.cos t) ^ 2) / (1 + (a * Real.cos t) ^ 2)
def arcY (a t : ℝ) : ℝ := (2 * (a * Real.cos t)) / (1 + (a * Real.cos t) ^ 2)

/-- A positive density that makes the two mean constraints elementary. -/
def density (a t : ℝ) : ℝ := (1 + (a * Real.cos t) ^ 2) / (1 + a ^ 2 / 2)

lemma arcDen_pos (a t : ℝ) : 0 < 1 + (a * Real.cos t) ^ 2 := by positivity
lemma densityDen_pos (a : ℝ) : 0 < 1 + a ^ 2 / 2 := by positivity

lemma density_pos (a t : ℝ) : 0 < density a t :=
  div_pos (arcDen_pos a t) (densityDen_pos a)

@[simp] lemma arcX_zero (t : ℝ) : arcX 0 t = 1 := by simp [arcX]
@[simp] lemma arcY_zero (t : ℝ) : arcY 0 t = 0 := by simp [arcY]
@[simp] lemma density_zero (t : ℝ) : density 0 t = 1 := by simp [density]

lemma arcX_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => arcX z.1 z.2) := by
  exact (contDiff_const.sub ((contDiff_fst.mul contDiff_snd.cos).pow 2)).div
    (contDiff_const.add ((contDiff_fst.mul contDiff_snd.cos).pow 2))
    (fun z => (arcDen_pos z.1 z.2).ne')

lemma arcY_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => arcY z.1 z.2) := by
  exact (contDiff_const.mul (contDiff_fst.mul contDiff_snd.cos)).div
    (contDiff_const.add ((contDiff_fst.mul contDiff_snd.cos).pow 2))
    (fun z => (arcDen_pos z.1 z.2).ne')

lemma arcX_periodic (a : ℝ) : Function.Periodic (arcX a) (2 * Real.pi) := by
  intro t
  simp only [arcX, Real.cos_add_two_pi]

lemma arcY_periodic (a : ℝ) : Function.Periodic (arcY a) (2 * Real.pi) := by
  intro t
  simp only [arcY, Real.cos_add_two_pi]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact mean constraints for the explicit collar velocity arc. -/
noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.CollarVelocity

def circleMean (f : ℝ → ℝ) : ℝ := (2 * Real.pi)⁻¹ * ∫ t in 0..2 * Real.pi, f t

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibrate the explicit collar arc to the required tangential mean. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity

def amplitude (R v a : ℝ) : ℝ := Real.sqrt 2 * a / (R + v)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityClock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit positive change of angular variable for the collar arc. -/
noncomputable section
open Filter
open scoped Topology ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def clock (a t : ℝ) : ℝ := t + a ^ 2 / (2 * (2 + a ^ 2)) * Real.sin (2 * t)

lemma density_eq (a t : ℝ) :
    density a t = 1 + a ^ 2 / (2 + a ^ 2) * Real.cos (2 * t) := by
  rw [Real.cos_two_mul]
  unfold density
  have h : 2 + a ^ 2 ≠ 0 := by positivity
  field_simp [(densityDen_pos a).ne', h]
  ring

lemma hasDerivAt_clock (a t : ℝ) : HasDerivAt (clock a) (density a t) t := by
  have hs := (Real.hasDerivAt_sin (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have h := (hasDerivAt_id t).add (hs.const_mul (a ^ 2 / (2 * (2 + a ^ 2))))
  change HasDerivAt (fun t => t + a ^ 2 / (2 * (2 + a ^ 2)) * Real.sin (2 * t)) _ t
  refine h.congr_deriv (Eq.symm ?_)
  · rw [density_eq]
    have hd : 2 + a ^ 2 ≠ 0 := by positivity
    field_simp [hd]

lemma clock_strictMono (a : ℝ) : StrictMono (clock a) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_clock a t).deriv]
  exact density_pos a t

lemma clock_continuous (a : ℝ) : Continuous (clock a) :=
  (show Differentiable ℝ (clock a) from fun t => (hasDerivAt_clock a t).differentiableAt).continuous

lemma clock_period (a t : ℝ) : clock a (t + 2 * Real.pi) = clock a t + 2 * Real.pi := by
  unfold clock
  rw [show 2 * (t + 2 * Real.pi) = (2 * t + 2 * Real.pi) + 2 * Real.pi by ring]
  rw [Real.sin_add_two_pi, Real.sin_add_two_pi]
  ring

lemma clock_displacement_bound (a t : ℝ) :
    |clock a t - t| ≤ |a ^ 2 / (2 * (2 + a ^ 2))| := by
  unfold clock
  rw [add_sub_cancel_left, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

lemma clock_surjective (a : ℝ) : Function.Surjective (clock a) := by
  let C := |a ^ 2 / (2 * (2 + a ^ 2))|
  have hlo (t : ℝ) : t - C ≤ clock a t := by
    have h := (abs_le.mp (clock_displacement_bound a t)).1
    dsimp [C]
    linarith
  have hhi (t : ℝ) : clock a t ≤ t + C := by
    have h := (abs_le.mp (clock_displacement_bound a t)).2
    dsimp [C]
    linarith
  apply (clock_continuous a).surjective
  · apply tendsto_atTop_mono hlo
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-C) tendsto_id
  · exact tendsto_atBot_mono hhi (tendsto_atBot_add_const_right atBot C tendsto_id)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth parameter dependence of the explicit collar clock's inverse. -/
noncomputable section
open Filter
open scoped Topology ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma clock_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => clock z.1 z.2) := by
  apply contDiff_snd.add
  apply ContDiff.mul
  · exact (contDiff_fst.pow 2).div
      (contDiff_const.mul (contDiff_const.add (contDiff_fst.pow 2)))
      (fun z => by positivity)
  · exact (contDiff_const.mul contDiff_snd).sin

def inverseClock (a θ : ℝ) : ℝ := Function.invFun (clock a) θ

@[simp] lemma clock_inverseClock (a θ : ℝ) : clock a (inverseClock a θ) = θ :=
  Function.rightInverse_invFun (clock_surjective a) θ

@[simp] lemma inverseClock_clock (a t : ℝ) : inverseClock a (clock a t) = t :=
  Function.leftInverse_invFun (clock_strictMono a).injective t

@[simp] lemma clock_zero (a : ℝ) : clock a 0 = 0 := by simp [clock]
@[simp] lemma inverseClock_zero (a : ℝ) : inverseClock a 0 = 0 := by
  simpa only [clock_zero] using inverseClock_clock a 0

lemma inverseClock_period (a θ : ℝ) :
    inverseClock a (θ + 2 * Real.pi) = inverseClock a θ + 2 * Real.pi := by
  apply (clock_strictMono a).injective
  rw [clock_inverseClock, clock_period, clock_inverseClock]

def equation (z : (ℝ × ℝ) × ℝ) : ℝ := clock z.1.1 z.2 - z.1.2

lemma equation_smooth : ContDiff ℝ ∞ equation := by
  exact (clock_smooth.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd

lemma equation_partial (a θ t : ℝ) :
    fderiv ℝ equation ((a, θ), t) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (density a t) := by
  have he := equation_smooth.differentiable (by norm_num)
  have hi : HasFDerivAt (fun s : ℝ => ((a, θ), s))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) t := by
    exact hasFDerivAt_prodMk_right (a, θ) t
  have hcomp := he.differentiableAt.hasFDerivAt.comp t hi
  have hderiv := ((hasDerivAt_clock a t).sub_const θ).hasFDerivAt
  exact hcomp.unique hderiv

lemma equation_partial_invertible (a θ t : ℝ) :
    (fderiv ℝ equation ((a, θ), t) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
  rw [equation_partial]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (density a t)⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (density_pos a t).ne']
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, (density_pos a t).ne']

lemma inverseClock_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => inverseClock z.1 z.2) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let u : (ℝ × ℝ) × ℝ := (z, inverseClock z.1 z.2)
  have hc := equation_smooth.contDiffAt (x := u)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hi := equation_partial_invertible z.1 z.2 (inverseClock z.1 z.2)
  have hs := hc.contDiffAt_implicitFunction hn hi
  have he := hc.eventually_apply_implicitFunction hn hi
  have heq : (fun w : ℝ × ℝ => inverseClock w.1 w.2) =ᶠ[𝓝 z]
      hc.implicitFunction hn hi := by
    filter_upwards [he] with w hw
    apply (clock_strictMono w.1).injective
    rw [clock_inverseClock]
    change clock w.1 (hc.implicitFunction hn hi w) - w.2 =
      clock z.1 (inverseClock z.1 z.2) - z.2 at hw
    rw [clock_inverseClock, sub_self] at hw
    exact (sub_eq_zero.mp hw).symm
  exact hs.congr_of_eventuallyEq heq

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The collar velocity has the desired uniform mean after reparametrization. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def reparamX (a θ : ℝ) : ℝ := arcX a (inverseClock a θ)
def reparamY (a θ : ℝ) : ℝ := arcY a (inverseClock a θ)

lemma reparamX_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => reparamX z.1 z.2) :=
  arcX_smooth.comp (contDiff_fst.prodMk inverseClock_smooth)

lemma reparamY_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => reparamY z.1 z.2) :=
  arcY_smooth.comp (contDiff_fst.prodMk inverseClock_smooth)

lemma reparamX_periodic (a : ℝ) : Function.Periodic (reparamX a) (2 * Real.pi) := by
  intro θ
  simp only [reparamX, inverseClock_period]
  exact arcX_periodic a _

lemma reparamY_periodic (a : ℝ) : Function.Periodic (reparamY a) (2 * Real.pi) := by
  intro θ
  simp only [reparamY, inverseClock_period]
  exact arcY_periodic a _

@[simp] lemma reparamX_zero (θ : ℝ) : reparamX 0 θ = 1 := arcX_zero _
@[simp] lemma reparamY_zero (θ : ℝ) : reparamY 0 θ = 0 := arcY_zero _

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit collar arc has exactly two stationary angular positions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def baseAngle (a t : ℝ) : ℝ := 2 * Real.arctan (a * Real.cos t)
def angle (a θ : ℝ) : ℝ := baseAngle a (inverseClock a θ)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact turning positions for the collar arc, including after reparametrization. -/
noncomputable section

namespace ClosedSurfaceR4.CollarVelocity

@[simp] lemma angle_zero (a : ℝ) : angle a 0 = 2 * Real.arctan a := by
  simp [angle, baseAngle]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityAngleInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpolate the collar angle to a circle-covering interior angle without extra turns. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def blendedAngle (a A s h t : ℝ) : ℝ :=
  h + (1 - s) * baseAngle a t + s * (A * Real.cos t)

end ClosedSurfaceR4.CollarVelocity

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

abbrev Plane := Fin 2 → ℝ

end ClosedSurfaceR4.LoopDensity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedVelocityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth transition paths and their strict convex-hull margin. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def blendedPath (a A s h t : ℝ) : LoopDensity.Plane :=
  ![Real.cos (blendedAngle a A s h (2 * Real.pi * t)),
    Real.sin (blendedAngle a A s h (2 * Real.pi * t))]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedReparamTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-turn geometry for the blended path after positive reparametrization. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def unitAngle (a A s h t : ℝ) : ℝ := blendedAngle a A s h (2 * Real.pi * t)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BlendedSpatialTurns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spatial derivative at each turn of the normalized blended loop. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def blendedAmplitude (a A s : ℝ) : ℝ := (1 - s) * (2 * Real.arctan a) + s * A

end ClosedSurfaceR4.CollarVelocity

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

def circularParam (c : CurvePlane) (r t : ℝ) : CurvePlane :=
  (c.1+r*Real.cos t,c.2+r*Real.sin t)

lemma circularParam_smooth (c : CurvePlane) (r : ℝ) : ContDiff ℝ ∞ (circularParam c r) := by
  change ContDiff ℝ ∞ (fun t => (c.1+r*Real.cos t,c.2+r*Real.sin t))
  fun_prop

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryTangencies
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
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularAngularTangent (c x : CurvePlane) : CurvePlane := (-(x.2-c.2),x.1-c.1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarVelocityPeriod
attribute [-simp] _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.averageCLM_apply _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.periodicBilinear_apply _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.weightedAverage_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the explicit collar arc to the unit period used by the corrector. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open CovarianceCorrector SmoothPeriodicCalculus

def unitX (a t : ℝ) : ℝ := reparamX a (2 * Real.pi * t)
def unitY (a t : ℝ) : ℝ := reparamY a (2 * Real.pi * t)

lemma unitX_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => unitX z.1 z.2) :=
  reparamX_smooth.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))

lemma unitY_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => unitY z.1 z.2) :=
  reparamY_smooth.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))

lemma unitX_periodic (a : ℝ) : Function.Periodic (unitX a) 1 := by
  intro t
  unfold unitX
  rw [mul_add, mul_one]
  exact reparamX_periodic a _

lemma unitY_periodic (a : ℝ) : Function.Periodic (unitY a) 1 := by
  intro t
  unfold unitY
  rw [mul_add, mul_one]
  exact reparamY_periodic a _

def loopX (a : ℝ) : C(Period, ℝ) :=
  bundle (unitX a) (unitX_periodic a)
    ((unitX_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous)

def loopY (a : ℝ) : C(Period, ℝ) :=
  bundle (unitY a) (unitY_periodic a)
    ((unitY_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous)

@[simp] lemma loopX_apply (a t : ℝ) : loopX a (t : Period) = unitX a t := rfl
@[simp] lemma loopY_apply (a t : ℝ) : loopY a (t : Period) = unitY a t := rfl

@[simp] lemma loopX_zero (t : Period) : loopX 0 t = 1 := by
  induction t using QuotientAddGroup.induction_on
  exact reparamX_zero _

@[simp] lemma loopY_zero (t : Period) : loopY 0 t = 0 := by
  induction t using QuotientAddGroup.induction_on
  exact reparamY_zero _

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CollarDensityMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unit-period moment equations for the prescribed collar density. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def unitDensity (a t : ℝ) : ℝ := density a (2 * Real.pi * t)

@[simp] lemma unitDensity_zero (t : ℝ) : unitDensity 0 t = 1 := density_zero _

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ControlledInteriorLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the interior velocity angle: a small translation with large turn
jets, an actual positive density, the exact prescribed vector mean, and exactly
two turns. No density or transverse-correction solvability is assumed. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open TransverseSmallFunction

def normalizedAngle (ρ : Base × ℝ → ℝ) (a A s h : Base → ℝ) : Base × ℝ → ℝ :=
  PositiveDensity.reparametrize ρ
    (fun z => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2)

end ClosedSurfaceR4.CollarVelocity

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
open JetPolynomial

abbrev Euclidean := EuclideanSpace ℝ (Fin 4)

end ClosedSurfaceR4.JetVelocityCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_BoundaryInvariantCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform collar positivity for the normal invariant used by later curves. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalInvariant (D S : E × ℝ → ℝ) (b c k : E → ℝ) (z : E × ℝ) : ℝ :=
  (D z * b z.1 + S z * c z.1) ^ 2 + k z.1 * b z.1 ^ 2

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPrefixMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered prefix metrics of a finite circular family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace CircularPrimitiveFamily
local instance prefixFiberNormed_r3ec6d4_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance prefixFiberSpace_r3ec6d4_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance prefixDualAdd_r3ec6d4_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance prefixDualSmul_r3ec6d4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {B : SmoothingAtlas M}
  {N : ℕ}

def prefixIndices (k : Fin (N+1)) : Finset (Fin N) :=
  Finset.univ.filter (fun a => a.val < k.val)

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


