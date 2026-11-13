-- Prove2me | Definitions.Def_OAIQ249SI013
-- name    : OAIQ249SI013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:42:29.299482+00:00
-- url     : https://prove2.me/theorems/d1dee822-ddc7-45e6-bd96-f80f6febff2e
-- title:
--   Definitions bundle OAIQ249SI013 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 46 definitions, 8 inductive types or structures and 25 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CorrectionGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.FiniteBoundaryGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.cutoff`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.directionIn`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.inPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.Stage`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.Stage.CanAdvance`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.Stage.defect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.Stage.size`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.Transition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.stageRadius`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.cycleAmplitude`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.BundleWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.InputBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleCutoff`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleLocalize`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalQuadraticPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.inputSize`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.linearAtlasPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseCurveSecondField`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseRealChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.quadraticOverlapCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorChartRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.adaptiveFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.fiberToThree`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalizedTensorDefect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.preparedFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberSpace`, `OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_PhaseStock`, `Immersion_ClosedSurface_PositiveBasis`, `Immersion_ClosedSurface_QuadraticSupport`, `SurfaceImmersion_Atlas_AtlasFiniteCancellation`, `SurfaceImmersion_Atlas_AtlasMetricBounds`, `SurfaceImmersion_Atlas_AtlasQuadraticTargets`, `SurfaceImmersion_Atlas_BundleAtlasBounds`, `SurfaceImmersion_Atlas_BundleCutoffCoordinates`, `SurfaceImmersion_Atlas_CenteredConvexPhase`, `SurfaceImmersion_Atlas_CompactPhaseCurveVectors`, `SurfaceImmersion_Atlas_CoordinateGauss`, `SurfaceImmersion_Atlas_CoordinateTaylorIdentity`, `SurfaceImmersion_Atlas_MetricGoodPhaseData`, `SurfaceImmersion_Atlas_PhaseBasisPerturbation`, `SurfaceImmersion_Atlas_PhaseBoundaryCurve`, `SurfaceImmersion_Atlas_PhaseCurvePairGeometry`, `SurfaceImmersion_Atlas_SpatialPhaseBasis`, `SurfaceImmersion_Atlas_SurfacePhaseCharts`, `SurfaceImmersion_Atlas_TensorChartRead`, `SurfaceImmersion_Atlas_TensorFiberCoordinates`, `SurfaceImmersion_Atlas_TensorPlaneCoordinates`, `SurfaceImmersion_Atlas_UniformNearbyAtlasSmallIncrement`, `SurfaceImmersion_Correction_AdaptiveCorrectionStep`, `SurfaceImmersion_Correction_BundleSmoothing`, `SurfaceImmersion_Correction_CorrectionGeometry`, `SurfaceImmersion_Correction_CoupledSmoothing`, `SurfaceImmersion_Correction_PreparedCorrection`, `SurfaceImmersion_Correction_SmoothPrimitiveFamily`, `SurfaceImmersion_Correction_SmoothingLocalSections`, `SurfaceImmersion_Correction_SmoothingLocalization`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_TensorSmoothing`, `SurfaceImmersion_Geometry_CompactSectionBounds`, `SurfaceImmersion_Geometry_CurveSecondFields`, `SurfaceImmersion_Geometry_FiniteBoundaryGeometry`, `SurfaceImmersion_Geometry_GlobalMetricStep`, `SurfaceImmersion_Geometry_GlobalMetricStepBound`, `SurfaceImmersion_Geometry_InputSize`, `SurfaceImmersion_Geometry_OrderedBoundaryInvariant`, `SurfaceImmersion_Geometry_PureRadialGauss`, `SurfaceImmersion_Geometry_QuadraticOverlapSupports`, `SurfaceImmersion_Primitive_BoundaryProfileCoordinates`, `SurfaceImmersion_Primitive_PhaseBoundaryProfile`, `SurfaceImmersion_Primitive_PhaseCurveCrossings`, `SurfaceImmersion_Primitive_PrimitiveCycleAssembly`, `SurfaceImmersion_Primitive_ReferenceCircularAtlas`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI003` and `OAIQ249SI004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI006`, `OAIQ249SI015` and `OAIQ249SI016`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_profiled_phase_primitive_metric`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_finite_slow_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_operator_identity`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_interaction_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_local_model`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_catalog_global_quadratic_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_crossing_safe_phase_normal_gluing`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_shifted_linear_metric_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_quadratic_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_global_polynomial_quadratic_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_atlas_seed_profile`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_linearized_representatives`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveCoordinateData_operator`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_real_restored_polynomial_quadratic`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_atlas_free_size`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_local_correction_assembly`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_small_increment`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metric_residualFactor_eq`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metric_sizeFactor_eq`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_combined_mean`, `OAI_ClosedSurfaceR4_PhaseGeometry_fixed_compact_polynomial_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_fixed_compact_polynomial_solver_family`, `OAI_ClosedSurfaceR4_PhaseGeometry_mem_phaseMarginCompact_of_relative_margin`, `OAI_ClosedSurfaceR4_PhaseGeometry_phaseMarginCompact_noncritical`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_compact_surface_metric_error`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_primitive_normal_triple` and `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_analytic_curve_crossing_loop`; the proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_profiled_phase_primitive_metric`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_finite_slow_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_second_transition`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_operator_identity`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_interaction_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_local_model`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_catalog_global_quadratic_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_crossing_safe_phase_normal_gluing`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_shifted_linear_metric_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_quadratic_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_global_polynomial_quadratic_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_nonlinear_jet_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_nonlinear_lowJet_neighborhood_of_C2`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_intrinsic_crossing_transition`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_atlas_seed_profile`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_linearized_representatives`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveCoordinateData_operator`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_real_restored_polynomial_quadratic`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_polynomial_representation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_atlas_free_size`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_local_correction_assembly`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_small_increment`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_metricPhaseData_of_whitney`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metric_residualFactor_eq`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_metric_sizeFactor_eq`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_combined_mean`, `OAI_ClosedSurfaceR4_PhaseGeometry_fixed_compact_polynomial_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_fixed_compact_polynomial_solver_family`, `OAI_ClosedSurfaceR4_PhaseGeometry_mem_phaseMarginCompact_of_relative_margin`, `OAI_ClosedSurfaceR4_PhaseGeometry_phaseMarginCompact_noncritical`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_compact_surface_metric_error`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_longitudinal_profile`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_primitive_normal_triple`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_scaled_longitudinal_profile` and `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_analytic_curve_crossing_loop`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
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
import Definitions.Def_OAIQ249SI003
import Definitions.Def_OAIQ249SI004

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


def covectorSquare (ξ : Base) : PhaseMean.Tensor := ![ξ.1 ^ 2, ξ.1 * ξ.2, ξ.2 ^ 2]


end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseStock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set



structure PhaseBasis where
  ξ : Fin 3 → Base
  Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ
  decomposition : ∀ H, ∑ i, Q i H • covectorSquare (ξ i) = H
  nonzero : ∀ i, ξ i ≠ 0

end ClosedSurfaceR4.PhaseGeometry

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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate displacement sumDisplacement)



def quadraticPhase {ι : Type*} (φ : ι → Base → ℝ) : QuadraticLabel ι → Base → ℝ
  | .inl i => fun p => 2 * φ i p
  | .inr ⟨i, j, b⟩ => if b then (fun p => φ i p - φ j p) else (fun p => φ i p + φ j p)

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

variable [CompactSpace M]

lemma localize_compact (p : M) {ψ : M → ℝ} (hψ : tsupport ψ ⊆ (chart p).source)
    (f : M → V) : HasCompactSupport (localize p ψ f) :=
  ((isClosed_tsupport ψ).isCompact.image_of_continuousOn
    ((chart p).continuousOn.mono hψ)).of_isClosed_subset (isClosed_tsupport _) (localize_tsupport p hψ f)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingLocalSections
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localization only requires smoothness on the chosen chart. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_smooth_on (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ f (chart p).source) :
    ContDiff ℝ ∞ (localize p ψ f) := by
  have hfc := hf.comp (chart_symm_smooth p) (chart p).mapsTo_symm
  have hlocal : ContDiffOn ℝ ∞
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target :=
    (((hψ.comp_contMDiffOn (chart_symm_smooth p)).pow 2).smul hfc).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  case neg => exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)
  obtain ⟨y, hy, hxy⟩ := localize_tsupport p hsupp f hx
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

def bundleLocalize (i : A.centers) (u : ∀ x, E x) : Base → F :=
  localize (i : M) (A.weight i) (A.bundleComponent e i u)

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleComponent_smooth_on (i : A.centers) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContMDiffOn planeModel 𝓘(ℝ, F) ∞ (A.bundleComponent e i u) (chart (i : M)).source := by
  have h := ((e i).contMDiffOn_section_iff (chart (i : M)).open_source (hdomain i)).mp
    hu.contMDiffOn
  apply h.congr
  intro x hx
  exact (e i).continuousLinearMapAt_apply_of_mem ℝ (hdomain i hx) (u x)

variable [CompactSpace M]

lemma bundleLocalize_smooth (i : A.centers) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContDiff ℝ ∞ (A.bundleLocalize e i u) :=
  localize_smooth_on (i : M) (A.weight_smooth i) (A.weight_support i)
    (A.bundleComponent_smooth_on e hdomain i hu)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_BundleAtlasBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted atlas bounds for section restoration. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

def BundleWeightedBound (s : ℝ) (m : ℕ) (C : ℝ) (u : ∀ x, E x) : Prop :=
  ∀ i : A.centers, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (A.bundleLocalize e i u)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_BundleCutoffCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading a section with an arbitrary compact chart cutoff is bounded by
its atlas norm. This allows phase patches to use unweighted tensor values. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
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
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)

def bundleCutoff (i : A.centers) (ψ : M → ℝ) (u : ∀ x, E x) : Base → F :=
  localize (i : M) ψ (A.bundleComponent e i u)

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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
local instance tensorModelComplete_r740b02_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
local instance tensorModelComplete_r740b02_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul
variable (A : SmoothingAtlas M)

def TensorWeightedBound (s : ℝ) (m : ℕ) (C : ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) : Prop :=
  A.BundleWeightedBound (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv s m C u

end SmoothingAtlas
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
open PhaseMean

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed
local instance coordinateFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
def fiberToThree : TensorFiber →L[ℝ] Tensor :=
  LinearMap.toContinuousLinearMap {
    toFun := fun B k => B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

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
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.sectionTensorNormed
local instance sectionTensorSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorEncode (u : ∀ x : M, CovariantTwoTensor x) : Base → A.centers → TensorFiber :=
  fun x i => A.bundleLocalize A.tensorTriv i u x

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorChartRead (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x) : Base → Tensor :=
  fiberToThree ∘ A.bundleCutoff A.tensorTriv i (A.outer i) u

end SmoothingAtlas
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
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
local instance planeReadSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorPlaneRead (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x) : SmallModes.Base → Tensor :=
  A.tensorChartRead i u ∘ planeCoordinateIsometry.symm

lemma tensorPlaneRestore_smooth {f : A.centers → SmallModes.Base → Tensor}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.tensorPlaneRestore f p)) := by
  apply ContMDiff.sum_section
  intro i _
  exact A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Taylor identity for the metric plus its finite polynomial
perturbation, in the coordinates of the forced-mode construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def coordinatePolynomialValue {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (t : ℝ) : SmallModes.Base → PhaseMean.Tensor :=
  fun p k => ∑ l, ε ^ (l.val + 1) * (P k l).eval G (planeCoordinateIsometry.symm p,t)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def jetChartMap (i : A.centers) (F : M → Space) : JetPolynomial.Base → JetPolynomial.Space :=
  spaceCoordinates ∘ A.vectorChartRead i F

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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
local instance metricBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricBoundDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
local instance metricBoundDualAdd_r740b02_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
local instance metricBoundSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_smooth {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (inducedTensor F p)) := by
  rw [← A.metric_from_chart_reads hF]
  apply A.tensorPlaneRestore_smooth
  intro i
  apply ((A.planeWeight_smooth i).pow 2).smul
  exact contDiffOn_univ.mp (RealModes.contDiffOn_realMetricTensor isOpen_univ
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasQuadraticTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported quadratic targets for the global phase expansion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasQuadraticTargetsFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticTargetsFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasQuadraticTargetsDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticTargetsDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance atlasQuadraticTargetsSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticTargetsSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def globalQuadraticPhase (φ : ι → M → ℝ) (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    JetPolynomial.Base → ℝ :=
  RealModes.quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l ∘ planeCoordinateIsometry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBasisPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coefficient forms for nearby phase covectors. The inverse
operator constructs the new decomposition and preserves compact positive
cone margins. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def perturbedPhaseOperator (P : PhaseBasis) (xi : Fin 3 → Base) :
    PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
  ∑ i, (P.Q i).smulRight (covectorSquare (xi i))

lemma perturbedPhaseOperator_apply (P : PhaseBasis) (xi : Fin 3 → Base)
    (H : PhaseMean.Tensor) :
    perturbedPhaseOperator P xi H = ∑ i, P.Q i H • covectorSquare (xi i) := by
  simp only [perturbedPhaseOperator, sum_apply, ContinuousLinearMap.smulRight_apply]

def perturbedPhaseCoefficient (P : PhaseBasis) (xi : Fin 3 → Base) (i : Fin 3) :
    PhaseMean.Tensor →L[ℝ] ℝ :=
  (P.Q i).comp (perturbedPhaseOperator P xi).inverse

lemma perturbedPhase_decomposition (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : (perturbedPhaseOperator P xi).IsInvertible) (H : PhaseMean.Tensor) :
    ∑ i, perturbedPhaseCoefficient P xi i H • covectorSquare (xi i) = H := by
  calc
    _ = perturbedPhaseOperator P xi ((perturbedPhaseOperator P xi).inverse H) :=
      (perturbedPhaseOperator_apply P xi _).symm
    _ = H := hxi.self_apply_inverse H

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SpatialPhaseBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual point-dependent phase bases. Outside the region of invertible
phase triples a fixed basis supplies harmless global values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def admissiblePhaseCovectors (P : PhaseBasis) (xi : Fin 3 → Base) : Prop :=
  (perturbedPhaseOperator P xi).IsInvertible ∧ ∀ i, xi i ≠ 0

def resolvedPhaseBasis (P : PhaseBasis) (xi : Fin 3 → Base) : PhaseBasis := by
  classical
  exact if h : admissiblePhaseCovectors P xi then
    ⟨xi,perturbedPhaseCoefficient P xi,perturbedPhase_decomposition P h.1,h.2⟩
  else P

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

def centeredSpatialBasis (P : PhaseBasis) (ell : Fin 3 → Base) (L : ℝ)
    (c p : Base) : PhaseBasis :=
  resolvedPhaseBasis P (fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)

end ClosedSurfaceR4.PhaseGeometry

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
open SmallModes NormalFrame

/-- Gaussian curvature times the coordinate metric determinant. -/
def coordinateGauss (E F G : Base → ℝ) (p : Base) : ℝ :=
  (2*coordDeriv dx (coordDeriv dy F) p-
    coordDeriv dy (coordDeriv dy E) p-coordDeriv dx (coordDeriv dx G) p)/2-
  inverseMetricPair (E p) (F p) (G p)
    (coordDeriv dx E p/2) (coordDeriv dx F p-coordDeriv dy E p/2)
    (coordDeriv dy F p-coordDeriv dx G p/2) (coordDeriv dy G p/2)+
  inverseMetricPair (E p) (F p) (G p)
    (coordDeriv dy E p/2) (coordDeriv dx G p/2)
    (coordDeriv dy E p/2) (coordDeriv dx G p/2)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OrderedBoundaryInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's ordered crossing expression in coordinates adapted to
the boundary curve, for the actual second fundamental form. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes SmallModes

def orderedCrossing (F : RField 4) (v w p : Base) (κ : ℝ) : ℝ :=
  (realSecondForm F v w p ⬝ᵥ normalize (realSecondForm F v v p)) ^ 2 +
    κ * gramDet (coordDeriv v F p) (coordDeriv w F p)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PureRadialGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature in the initial ordered crossing invariant is the actual
Gaussian curvature computed from the induced metric, rather than a freely
specified scalar. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame

def coordinateGaussianCurvature (E F G : Base → ℝ) (p : Base) : ℝ :=
  coordinateGauss E F G p/(E p*G p-(F p)^2)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five Euclidean profiles used by the exact primitive determine the
canonical normal frame in the real surface coordinates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame SurfaceJetCoordinates JetVelocityCoordinates
open SurfaceVelocityFamily.Loop

def boundaryProfileMap : EuclideanBoundaryProfile →L[ℝ] BoundaryProfile :=
  ContinuousLinearMap.pi fun i =>
    spaceCoordinates.toContinuousLinearMap.comp (ContinuousLinearMap.proj i)

@[simp] lemma boundaryProfileMap_apply (J : EuclideanBoundaryProfile) (i : Fin 5) :
    boundaryProfileMap J i = spaceCoordinates (J i) := rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseBoundaryProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseRealChartMap (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base) (F : M → Space) : RField 4 :=
  A.jetChartMap i F ∘ T ∘ baseEquiv.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfacePhaseCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual surface chart associated with a nonlinear phase. It is
independent of the correction atlas and supplies the chart transitions for later curves. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfacePhaseChart (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    OpenPartialHomeomorph M SmallModes.Base :=
  ((FiniteOrderSmoothing.chart q).trans e).transHomeomorph baseEquiv.toHomeomorph

def surfacePhaseTransition (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    OpenPartialHomeomorph SmallModes.Base SmallModes.Base :=
  (surfacePhaseChart p e).symm.trans (surfacePhaseChart q f)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactSectionBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every smooth input has finite bounds at each fixed atlas order. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Arbitrarily high map norms are finite; no uniform high-order input bound
is required for the eventual waiting argument. -/
theorem exists_shifted_bound (q m : ℕ) {f : M → F}
    (hf : ContMDiff planeModel 𝓘(ℝ, F) ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ A.ShiftedBound q m 1 C f := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_compact (i : M) (A.weight_support i) f) (q + m)
  refine ⟨∑ i : A.centers, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro i j hj x
  have h := hb i j hj x (mem_univ x)
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ] at h ⊢
  exact h.trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i))

variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- Smooth tensor inputs likewise have finite localized bounds at every
fixed order, even when their high derivatives are large. -/
theorem exists_bundle_bound (m : ℕ) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.BundleWeightedBound e 1 m C u := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (A.bundleLocalize_smooth e hdomain i hu)
    (localize_compact (i : M) (A.weight_support i) _) m
  refine ⟨∑ i : A.centers, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro i
  exact (hb i).mono_const (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

local instance overlapTargetsFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance overlapTargetsDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance overlapTargetsSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [ChartedSpace Plane M] [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma globalQuadraticSupport_closed {ι : Type*} (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) :
    ∀ l : RealModes.QuadraticLabel ι, IsClosed (globalQuadraticSupport S l) := by
  intro l
  rcases l with a | ⟨a,b,c⟩
  · exact hS a
  · exact (hS a).inter (hS b)

namespace SmoothingAtlas
local instance overlapTargetsFiberNormed_r740b02_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace_r740b02_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance overlapTargetsDualAdd_r740b02_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_r740b02_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance overlapTargetsSectionNormed_r740b02_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace_r740b02_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def quadraticOverlapCompact (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) : TopologicalSpace.Compacts JetPolynomial.Base :=
  ⟨(chart (k : M)) '' (tsupport (A.weight k) ∩ globalQuadraticSupport S l),
    ((isClosed_tsupport _).inter (globalQuadraticSupport_closed S hS l)).isCompact.image_of_continuousOn
      ((chart (k : M)).continuousOn.mono (fun _ h => A.weight_support k h.1))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformNearbyAtlasSmallIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance uniformNearbySmallFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformNearbySmallFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance uniformNearbySmallDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformNearbySmallDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance uniformNearbySmallSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformNearbySmallSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The fixed geometric phase expressed as a smooth function on the surface. -/
def linearAtlasPhase (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (a : A.centers × Fin 3) : M → ℝ :=
  restore (a.1 : M) (A.outer a.1)
    (phaseLinear (w a.1 a.2 • (Q a.1).ξ a.2) ∘ planeCoordinateIsometry)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricGoodPhaseData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metric-adapted phase geometry, including all cross-chart
quadratic phases needed by the small-increment construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance metricPhaseDataFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricPhaseDataFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricPhaseDataDualAdd_r740b02_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricPhaseDataDualSmul_r740b02_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricPhaseDataSectionNormed_r740b02_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricPhaseDataSectionSpace_r740b02_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
structure MetricGoodPhaseData (g : SmoothMetric M) (F : M → Space) where
  A : SmoothingAtlas M
  Q : A.centers → PhaseBasis
  w : A.centers → Fin 3 → ℝ
  weight_pos : ∀ i j, 0 < w i j
  outer_locally_one : ∀ i x, x ∈ tsupport (A.weight i) →
    A.outer i =ᶠ[𝓝 x] (fun _ => 1)
  immersion : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
  pure_good : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j)
  metric_positive : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    0 < (Q i).Q j (A.tensorPlaneRead i g.inner x)
  quadratic_good : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
      (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed atlas data used when taking the smooth correction limit. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance correctionGeometryFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance correctionGeometryFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance correctionGeometryDualAdd_r740b02_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance correctionGeometryDualSmul_r740b02_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance correctionGeometrySectionNormed_r740b02_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance correctionGeometrySectionSpace_r740b02_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
structure CorrectionGeometry (_g : SmoothMetric M) (_F : M → Space) where
  A : SmoothingAtlas M
  outer_locally_one : ∀ i x, x ∈ tsupport (A.weight i) →
    A.outer i =ᶠ[𝓝 x] (fun _ => 1)

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

local instance coupledModelNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance coupledModelSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance coupledModelComplete_r740b02_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance coupledModelNormed_r740b02_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance coupledModelSpace_r740b02_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance coupledModelComplete_r740b02_2 : CompleteSpace TensorFiber := inferInstance
variable (A : SmoothingAtlas M)

/-- The map carries a two-derivative prefix, while the metric defect has none. -/
def InputBound (t : ℝ) (m : ℕ) (C : ℝ) (G : M → Space)
    (H : ∀ p : M, CovariantTwoTensor p) : Prop :=
  A.ShiftedBound 2 m t C G ∧ A.TensorWeightedBound t m C H

end SmoothingAtlas
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
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberNormed
local instance inputSizeSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputSizeSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The least nonnegative bound for the joint map/metric input. -/
def inputSize (t : ℝ) (m : ℕ) (G : M → Space)
    (H : ∀ p : M, CovariantTwoTensor p) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ A.InputBound t m C G H}

/-- Every finite-stage smooth input has a finite joint norm, without any
uniform bound on its higher derivatives. -/
theorem exists_input_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ)
    {G : M → Space} {H : ∀ p : M, CovariantTwoTensor p}
    (hG : ContMDiff planeModel spaceModel ∞ G)
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (H p))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H := by
  obtain ⟨CG,hCG,hGb⟩ := A.exists_shifted_bound 2 m hG
  obtain ⟨CH,hCH,hHb⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain m hH
  refine ⟨CG+CH,add_nonneg hCG hCH,?_,?_⟩
  · intro i j hj x
    have hh := hGb i j hj x
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ 1*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) G) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht ht1) (norm_nonneg _)
      _ ≤ CG+CH := by simpa only [one_mul] using hh.trans (le_add_of_nonneg_right hCH)
  · intro i
    exact ((hHb i).shrink_scale ht ht1).mono_const (le_add_of_nonneg_left hCG)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized-defect identity for the unsmoothed global map update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance metricStepFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricStepFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricStepDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricStepDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricStepSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricStepSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def normalizedTensorDefect (target : ∀ p : M, CovariantTwoTensor p) (δ : ℝ) (F : M → Space) :
    ∀ p : M, CovariantTwoTensor p := (δ^2)⁻¹ • (target - inducedTensor F)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStepBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global weighted estimate for the concrete unsmoothed normalized-defect update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance stepBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance stepBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance stepBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance stepBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

local instance stepBoundSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance stepBoundSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
include A in
lemma normalizedTensorDefect_smooth {target : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (δ : ℝ) {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (normalizedTensorDefect target δ F p)) :=
  (ht.sub_section (A.inducedTensor_smooth hF)).const_smul_section

end SmoothingAtlas
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
local instance preparedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance preparedFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance preparedDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance preparedDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

local instance preparedSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance preparedSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Uniform geometric radii and the order-dependent estimates used by the
iteration. This package is obtained by `preparedCorrection_nonempty`. -/
structure PreparedCorrection (d : CorrectionGeometry g F) where
  a : ℝ
  ρ : ℝ
  baseline : ℝ
  budget : ℝ
  a_pos : 0 < a
  ρ_pos : 0 < ρ
  baseline_nonneg : 0 ≤ baseline
  budget_pos : 0 < budget
  baseline_lt : baseline < budget/4
  ε : ℕ → ℝ
  L : ℕ → ℝ
  N : ℕ → ℕ → ℝ
  ε_pos : ∀ k, 0 < ε k
  ε_le_one : ∀ k, ε k ≤ 1
  L_nonneg : ∀ k, 0 ≤ L k
  N_nonneg : ∀ k m, 0 ≤ N k m
  preserve : ∀ k t, 0 < t → t < ε k →
    baseline+N k (correctionInputOrder k)*t^(1/5 : ℝ)*(1+budget) ≤ budget ∧
    L k*(1+2*budget)*t^(1/5 : ℝ) ≤ a/8
  step : ∀ k (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε k → ∀ j : ℕ,
    correctionOrder k ≤ j → j ≤ correctionOrder k+1 →
    d.A.InputBound t (correctionInputOrder k) budget G
      (normalizedTensorDefect g.inner (t^(correctionOrder k : ℝ)) G) →
    d.A.WeightedBound 1 2 (ρ/4) (G-F) →
    (∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner
      (t^(correctionOrder k : ℝ)) G) x-d.A.tensorEncode g.inner x‖ ≤ a/8) →
    ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
      (∀ m ≤ correctionOrder k/2, d.A.WeightedBound 1 m (ρ*t) U) ∧
      d.A.TensorWeightedBound (t^(6/5 : ℝ)) 0
        (L k*(1+2*budget)*t^(1/5 : ℝ))
        (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) ∧
      ∀ m C, 0 ≤ C → d.A.InputBound t m C G
        (normalizedTensorDefect g.inner (t^(correctionOrder k : ℝ)) G) →
        d.A.InputBound (t^(6/5 : ℝ)) m
          (baseline+N k m*t^(1/5 : ℝ)*(1+C)) (G+U)
          (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveSecondFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth global representatives of second-form fields along a compact curve.
A cutoff in its own phase chart extends the field without choosing a normal frame. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes NormalFrame SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- This cutoff is selected from the curve and phase chart before selecting
any later isometric immersion. -/
lemma phase_curve_cutoff (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {K : Set SmallModes.Base} (hK : IsCompact K)
    (hKt : ∀ p ∈ K, baseEquiv.symm p ∈ e.target)
    (hKa : ∀ p ∈ K, A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0) :
    ∃ β : SmallModes.Base → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      (∀ p ∈ K, β p = 1) ∧ ∀ p ∈ tsupport β,
        baseEquiv.symm p ∈ e.target ∧ A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0 := by
  let U : Set SmallModes.Base := baseEquiv.symm ⁻¹' e.target ∩
    {p | A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0}
  have hU : IsOpen U := (e.open_target.preimage baseEquiv.symm.continuous).inter
    (isOpen_ne.preimage ((A.chartWeight_smooth i).continuous.comp
      (hi.continuous.comp baseEquiv.symm.continuous)))
  obtain ⟨β,hβ,hβc,_,hβs,hβone⟩ := CollarVelocity.compact_cutoff hK hU
    (fun p hp => ⟨hKt p hp,hKa p hp⟩)
  exact ⟨β,hβ,hβc,hβone,fun p hp => hβs hp⟩

def phaseCurveSecondField (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (β : SmallModes.Base → ℝ) (F : M → Space) (v w : SmallModes.Base → SmallModes.Base) : M → Space :=
  restore (i : M) (A.outer i) (fun x => spaceCoordinates.symm
    (β (baseEquiv (e x)) • realSecondForm (A.phaseRealChartMap i e.symm F)
      (v (baseEquiv (e x))) (w (baseEquiv (e x))) (baseEquiv (e x))))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

omit [CompactSpace M] in
lemma coordinate_continuous : ContinuousOn c.coordinate c.carrier :=
  baseEquiv.continuous.comp_continuousOn
    (((chart (c.index : M)).trans c.phase).continuousOn.mono c.source)

omit [CompactSpace M] in
lemma coordinate_compact : IsCompact (c.coordinate '' c.carrier) :=
  c.compact.image_of_continuousOn c.coordinate_continuous

lemma cutoff_exists : ∃ β : SmallModes.Base → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
    (∀ x ∈ c.coordinate '' c.carrier, β x = 1) ∧
    ∀ x ∈ tsupport β, baseEquiv.symm x ∈ c.phase.target ∧
      B.chartWeight c.index (c.phase.symm (baseEquiv.symm x)) ≠ 0 := by
  apply B.phase_curve_cutoff c.index c.phase c.inverse_smooth c.coordinate_compact
  · rintro x ⟨p,hp,rfl⟩
    have hs : chart (c.index : M) p ∈ c.phase.source := (c.source hp).2
    simpa only [coordinate,baseEquiv.symm_apply_apply] using c.phase.map_source hs
  · rintro x ⟨p,hp,rfl⟩
    have hs : chart (c.index : M) p ∈ c.phase.source := (c.source hp).2
    change B.chartWeight c.index (c.phase.symm (baseEquiv.symm (baseEquiv (c.phase (chart (c.index : M) p))))) ≠ 0
    rw [baseEquiv.symm_apply_apply,c.phase.left_inv hs,SmoothingAtlas.chartWeight,
      indicator_of_mem ((chart (c.index : M)).map_source (c.source hp).1),
      (chart (c.index : M)).left_inv (c.source hp).1]
    exact c.active p hp

def cutoff : SmallModes.Base → ℝ := Classical.choose c.cutoff_exists

def second (F : M → Space) (p : M) : Vec :=
  spaceCoordinates (B.phaseCurveSecondField c.index c.phase c.cutoff F
    (fun _ => dy) (fun _ => dy) p)

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseCurveVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth direction coefficients for the actual pieces of later curves
inside one fixed primitive disk. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

def inPhase (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (K : Set M) : Set Base := (surfacePhaseChart q e) '' (c.carrier ∩ K)

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseCurveCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic ordered crossing invariants for the fixed later curves.
Their values can be computed in whichever phase chart is being corrected. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

def crossing (F : M → Space) (p : M) : ℝ :=
  let H := B.phaseRealChartMap c.index c.phase.symm F
  let T := surfacePhaseTransition (d.index : M) d.phase (c.index : M) c.phase
  let v := fderiv ℝ T (d.coordinate p) dy
  orderedCrossing H dy v (c.coordinate p)
    (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy)
      (c.coordinate p))

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCurvePairGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both ordered crossings and both pure second forms in either fixed
curve chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

def directionIn (p : M) : SmallModes.Base :=
  fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (d.index : M) d.phase) (c.coordinate p) dy

end PhaseBoundaryCurve
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
open ExactCorrection WeightedEstimates
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions
local instance adaptiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance adaptiveFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance adaptiveDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance adaptiveDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}

namespace PreparedCorrection
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions
local instance adaptiveFiberSpace_r740b02_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance adaptiveDualAdd_r740b02_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance adaptiveDualSmul_r740b02_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (c : PreparedCorrection d)

local instance adaptiveSectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance adaptiveSectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def stageRadius (t : ℝ) (n : ℕ) : ℝ :=
  c.ρ/8+c.ρ*(∑ i ∈ Finset.range n, correctionScale t i)

structure Stage (t : ℝ) (n : ℕ) where
  order : ℕ
  map : M → Space
  smooth : ContMDiff planeModel spaceModel ∞ map
  scale_small : correctionScale t n < c.ε order
  input : d.A.InputBound (correctionScale t n) (correctionInputOrder order) c.budget map
    (normalizedTensorDefect g.inner ((correctionScale t n)^(correctionOrder order : ℝ)) map)
  near : d.A.WeightedBound 1 2 (c.stageRadius t n) (map-F)
  metric : ∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner
    ((correctionScale t n)^(correctionOrder order : ℝ)) map) x-
    d.A.tensorEncode g.inner x‖ ≤ c.a/8

namespace Stage
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions
local instance adaptiveFiberSpace_r740b02_3 : NormedSpace ℝ TensorFiber := inferInstance
local instance adaptiveDualAdd_r740b02_3 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance adaptiveDualSmul_r740b02_3 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {c} {t : ℝ} {n : ℕ}

local instance adaptiveSectionNormed_r740b02_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance adaptiveSectionSpace_r740b02_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def defect (s : c.Stage t n) : ∀ p : M, CovariantTwoTensor p :=
  normalizedTensorDefect g.inner ((correctionScale t n)^(correctionOrder s.order : ℝ)) s.map

lemma finiteInput (s : c.Stage t n) (ht : 0 < t) (htsmall : t ≤ 1/32) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ d.A.InputBound (correctionScale t n) m C s.map s.defect := by
  exact d.A.exists_input_bound (correctionScale_pos ht n).le
    ((correctionScale_le_initial ht.le htsmall n).trans (by linarith)) m s.smooth
    (d.A.normalizedTensorDefect_smooth g.contMDiff _ s.smooth)

def size (s : c.Stage t n) (m : ℕ) : ℝ :=
  d.A.inputSize (correctionScale t n) m s.map s.defect

def CanAdvance (s : c.Stage t n) : Prop :=
  correctionScale t n < c.ε (s.order+1) ∧
  c.baseline+c.N s.order (correctionInputOrder (s.order+1))*
    (correctionScale t n)^(1/5 : ℝ)*(1+s.size (correctionInputOrder (s.order+1))) ≤ c.budget

end Stage

structure Transition {t : ℝ} {n : ℕ} (s : c.Stage t n) where
  next : c.Stage t (n+1)
  increment : M → Space
  smooth : ContMDiff planeModel spaceModel ∞ increment
  map_eq : next.map = s.map+increment
  order_eq : next.order = if s.CanAdvance then s.order+1 else s.order
  small : ∀ m ≤ correctionOrder s.order/2,
    d.A.WeightedBound 1 m (c.ρ*correctionScale t n) increment
  recurrence : ∀ m C, 0 ≤ C →
    d.A.InputBound (correctionScale t n) m C s.map s.defect →
    d.A.InputBound (correctionScale t (n+1)) m
      (c.baseline+c.N s.order m*(correctionScale t n)^(1/5 : ℝ)*(1+C)) next.map next.defect

end PreparedCorrection
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

namespace SmoothPrimitiveFamily
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyDualAdd
local instance familyFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance familyFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance familyDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

local instance familySectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance familySectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma term_symmetric (a : ι) (p : M) (v w : TangentSpace planeModel p) :
    d.term a p v w = d.term a p w v := by
  rw [d.term_apply,d.term_apply]
  ring

include d in
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma tensor_symmetric (p : M) (v w : TangentSpace planeModel p) : u p v w = u p w v := by
  rw [← d.sum_eq p]
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun a _ => d.term_symmetric a p v w)

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_symmetric (N c : ℕ) (s : Finset ι) (p : M) (v w : TangentSpace planeModel p) :
    d.cycleTensor N c s p v w = d.cycleTensor N c s p w v := by
  change (c : ℝ)/(N : ℝ)*u p v w+(N : ℝ)⁻¹*(∑ a ∈ s, d.term a p) v w =
    (c : ℝ)/(N : ℝ)*u p w v+(N : ℝ)⁻¹*(∑ a ∈ s, d.term a p) w v
  simp only [sum_apply]
  rw [d.tensor_symmetric p v w]
  congr 2
  exact Finset.sum_congr rfl (fun a _ => d.term_symmetric a p v w)

end SmoothPrimitiveFamily

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteBoundaryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite boundary invariant retained by successive primitive corrections. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*}

structure FiniteBoundaryGeometry (curves : ι → PhaseBoundaryCurve B) (E : Set M)
    (F : M → Space) (n : PreferredNormal F) : Prop where
  nonzero : ∀ j p, p ∈ (curves j).carrier → (curves j).second F p ≠ 0
  avoids : ∀ j p, p ∈ (curves j).carrier →
    spaceCoordinates (n.vector p) ≠ -normalize ((curves j).second F p)
  positive : ∀ j k, j ≠ k → ∀ p ∈ E, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
    0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p)
  crossing : ∀ j k, j ≠ k → ∀ p ∈ E, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
    0 < (curves j).crossing (curves k) F p

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCycleAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-cycle identities for independently chosen primitive families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance assemblyFiberNormed_r740b02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance assemblyFiberSpace_r740b02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance assemblyDualAdd_r740b02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance assemblyDualSmul_r740b02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

local instance assemblySectionNormed_r740b02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance assemblySectionSpace_r740b02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def cycleAmplitude (N : ℕ) (a : ι) (p : M) : ℝ :=
  d.amplitude a p/Real.sqrt (N : ℝ)

end ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A reference circular atlas with positive coefficient forms and convex
phases, chosen before the number of cycles or generic perturbations. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

structure ReferenceCircularAtlas (A : SmoothingAtlas M) (gref g : SmoothMetric M) (c C : ℝ) where
  B : SmoothingAtlas M
  P : B.centers → PhaseBasis
  L : B.centers → ℝ
  radius : B.centers → ℝ
  epsilon : B.centers → ℝ
  L_pos : ∀ i, 0 < L i
  radius_pos : ∀ i, 0 < radius i
  epsilon_pos : ∀ i, 0 < epsilon i
  region : ∀ i : B.centers, circularCoordinateRegion (i : M) (radius i) ⊆ (coordinateChart (i : M)).target
  weight_nonneg : ∀ i p, 0 ≤ B.weight i p
  weight_positive : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (radius i)
  outer : ∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1)
  parameters : ∀ i j ell, ell ∈ Metric.closedBall ((P i).ξ j) (epsilon i) →
    ell ≠ 0 ∧ ‖ell‖ ≤ ‖(P i).ξ‖+1
  admissible : ∀ (i : B.centers) p, p ∈ circularDiskClosure (i : M) (radius i) →
    admissiblePhaseCovectors (P i) (fun j => phaseDerivative
      (centeredConvexPhase ((P i).ξ j) (L i) (coordinateChart (i : M) i)) (coordinateChart (i : M) p))
  positive : ∀ (i : B.centers) p, p ∈ circularDiskClosure (i : M) (radius i) → ∀ j,
    0 < (centeredSpatialBasis (P i) (P i).ξ (L i) (coordinateChart (i : M) i)
      (coordinateChart (i : M) p)).Q j (coordinateMetric gref (i : M) (coordinateChart (i : M) p))
  convex : ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
    (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
    ∀ (i : B.centers) p, p ∈ circularDiskClosure (i : M) (radius i) →
      ∀ ell : Base, ‖ell‖ ≤ ‖(P i).ξ‖+1 → ∀ v : Base,
        (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
          (centeredConvexPhase ell (L i) (coordinateChart (i : M) i)) (coordinateChart (i : M) p) v v
  charts : ∀ (i : B.centers) j ell, ell ∈ Metric.closedBall ((P i).ξ j) (epsilon i) →
    ∃ e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base,
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ x, (baseEquiv (e x)).1 = centeredConvexPhase ell (L i)
        (coordinateChart (i : M) i) (baseEquiv x)) ∧
      ∀ x ∈ circularCoordinateRegion (i : M) (radius i), baseEquiv.symm x ∈ e.source

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


