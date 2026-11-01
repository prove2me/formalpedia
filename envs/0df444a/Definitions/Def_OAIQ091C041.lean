-- Prove2me | Definitions.Def_OAIQ091C041
-- name    : OAIQ091C041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:10:24.445982+00:00
-- url     : https://prove2.me/theorems/a29df66f-32f5-40c7-add8-fdbd71809c40
-- title:
--   Definitions bundle OAIQ091C041 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 200 declarations of OpenAI's Lean: 42 definitions and 158 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.normalEndpointBoundary`, `OAI.PositiveEinsteinFour.Geometry.normalEndpointJetData`, `OAI.PositiveEinsteinFour.Geometry.normalSegmentCurve`, `OAI.PositiveEinsteinFour.Geometry.normalSegmentEnergy`, `OAI.PositiveEinsteinFour.Geometry.normalSegmentPosition`, `OAI.PositiveEinsteinFour.Geometry.normalSegmentVelocity`, `OAI.PositiveEinsteinFour.Geometry.scalarChartLift`, `OAI.PositiveEinsteinFour.Geometry.scalarChartTest`, `OAI.PositiveEinsteinFour.Geometry.scalarCoercive_h1Space`, `OAI.PositiveEinsteinFour.Geometry.scalarCoercive_meanZeroSpace`, `OAI.PositiveEinsteinFour.Geometry.scalarCompactDerivativeL2`, `OAI.PositiveEinsteinFour.Geometry.scalarCompactTestL2`, `OAI.PositiveEinsteinFour.Geometry.scalarDirichletDensity`, `OAI.PositiveEinsteinFour.Geometry.scalarEnergyRoot`, `OAI.PositiveEinsteinFour.Geometry.scalarEnergyRootL2`, `OAI.PositiveEinsteinFour.Geometry.scalarFirstJetRangeInclusion`, `OAI.PositiveEinsteinFour.Geometry.scalarFlowTranslation`, `OAI.PositiveEinsteinFour.Geometry.scalarGeodesicOscillation`, `OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZeroProjection`, `OAI.PositiveEinsteinFour.Geometry.scalarMeanZeroDirichlet`, `OAI.PositiveEinsteinFour.Geometry.scalarMeanZeroGradient`, `OAI.PositiveEinsteinFour.Geometry.scalarMeanZeroValue`, `OAI.PositiveEinsteinFour.Geometry.scalarPairConstant`, `OAI.PositiveEinsteinFour.Geometry.scalarRadialOscillation`, `OAI.PositiveEinsteinFour.Geometry.scalarTranslatedField`, `OAI.PositiveEinsteinFour.Geometry.smoothL2Hodge`, `OAI.PositiveEinsteinFour.Geometry.smoothL2HodgeLinear`, `OAI.PositiveEinsteinFour.Geometry.smoothOneFormHodgeEnergy`, `OAI.PositiveEinsteinFour.Geometry.smoothRadialNorm`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarDirichlet`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarLaplacian`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarLaplacianField`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarLaplacianL2`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarShiftedRhs`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormDDelta`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormHodge`, `OAI.PositiveEinsteinFour.Geometry.twoFormCodiffDensity`, `OAI.PositiveEinsteinFour.Geometry.twoFormCodiffPairing`, `OAI.PositiveEinsteinFour.Geometry.twoFormDeRhamDensity`, `OAI.PositiveEinsteinFour.Geometry.twoFormFiberSignedTrace` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C024`, `OAIQ091C025`, `OAIQ091C060`, `OAIQ091C061`, `OAIQ091C062`, `OAIQ091C063` and `OAIQ091C068`; the statements `OAI_PositiveEinsteinFour_Bianchi_matrixRotation_energy` and `OAI_PositiveEinsteinFour_Bianchi_rawGradientGenerator_casimir`; the proofs of `OAI_PositiveEinsteinFour_Bianchi_matrixRotation_energy`, `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_jointTraceEnergy_le_hessian`, `OAI_PositiveEinsteinFour_Geometry_ScalarCovariantData_curvature_identity` and `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C021

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Smooth two-form fields are defined by their actual coefficients in
local positively oriented orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothTwoFormHodge (o : FrameOrientation g) : smoothTwoForms o →ₗ[ℝ] smoothTwoForms o where
  toFun u := ⟨fun c => twoFormHodge (u.val c), TwoFormSmooth.hodge u.property⟩
  map_add' u v := by
    apply Subtype.ext
    funext c
    exact map_add twoFormHodge (u.val c) (v.val c)
  map_smul' r u := by
    apply Subtype.ext
    funext c
    exact map_smul twoFormHodge r (u.val c)

theorem smoothTwoFormHodge_involutive (o : FrameOrientation g) :
    Function.Involutive (smoothTwoFormHodge o) := by
  intro u
  apply Subtype.ext
  funext c
  exact twoFormHodge_involutive (u.val c)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual frame Laplacian descends to a smooth scalar on the base.
This supplies smooth test functions for the distributional Poisson equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarLaplacianBase_smooth (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (scalarLaplacianBase g a) := by
  intro c
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have h := (chartScalarLaplacian_contDiffAt g ha c _ hz).contMDiffAt.comp c
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      (mem_chart_source FourSpace c))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c)] with x hx
  have heq := chartScalarLaplacian_eq_base g ha c
    ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source hx⟩
  simpa only [(chartAt FourSpace c).left_inv hx] using! heq.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity for the scalar functions used by the compact heat
parametrix. Four derivatives suffice for the value, gradient and Hessian
identities; no smooth extension of the parametrix is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_finite_framed_continuous (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (k : ℕ) (hk : k ≤ 3) :
    Continuous (fun e : FrameBundle g => frameTensor e.frame.matrix
      (iteratedScalarDerivative g f e.base k (chartAt FourSpace e.base e.base))) := by
  apply continuous_framedTensor g (fun c => iteratedScalarDerivative g f c k)
  · intro c z hz a
    exact (scalar_finite_derivative_contDiffAt g hf c k 0 (by omega) z hz a).continuousAt
  · intro c d z hz hx
    exact scalar_finite_derivative_transition g hf c d k hk z hz hx

theorem scalar_finite_gradient_continuous (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (i : Fin 4) :
    Continuous (fun e : FrameBundle g => scalarGradient g f e i) :=
  (show Continuous (fun T : CovariantCoordinates 1 => T ![i]) from
    continuous_apply _).comp (scalar_finite_framed_continuous g hf 1 (by omega))

theorem scalar_finite_hessian_continuous (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (i j : Fin 4) :
    Continuous (fun e : FrameBundle g => scalarHessian g f e i j) :=
  (show Continuous (fun T : CovariantCoordinates 2 => T ![i, j]) from
    continuous_apply _).comp (scalar_finite_framed_continuous g hf 2 (by omega))

theorem scalar_finite_parallel_derivative (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (γ : ℝ → FrameBundle g)
    (t : ℝ) (i : Fin 4) (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ i t)
    (k : ℕ) (hk : k ≤ 2) (a : Fin k → Fin 4) :
    HasDerivAt (fun s => frameTensor (γ s).frame.matrix
      (iteratedScalarDerivative g f (γ s).base k (chartAt FourSpace (γ s).base (γ s).base)) a)
      (frameTensor (γ t).frame.matrix
        (iteratedScalarDerivative g f (γ t).base (k + 1)
          (chartAt FourSpace (γ t).base (γ t).base)) (Fin.cons i a)) t := by
  apply hasDerivAt_framedTensor g (fun c => iteratedScalarDerivative g f c k)
  · intro c z hz v
    exact (scalar_finite_derivative_contDiffAt g hf c k 1 (by omega) z hz v).differentiableAt one_ne_zero
  · intro c d z hz hx
    exact scalar_finite_derivative_transition g hf c d k (by omega) z hz hx
  · intro c d z hz hx
    exact scalar_finite_derivative_transition g hf c d (k + 1) (by omega) z hz hx
  · exact hγ
  · exact hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hilbert completion of actual smooth two-form sections with their
intrinsic L2 pairing. The inclusion of pointwise smooth sections is an
injective linear isometry with dense range. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

/- The L2 topology of the completion differs from the pointwise topology
on the smooth function submodule. -/

theorem smoothTwoForm_norm_sq (u : SmoothL2TwoForm o) :
    ‖u‖ ^ 2 = ∫ x, ‖(u : smoothTwoForms o).val x‖ ^ 2 ∂normalizedVolume g := by
  rw [← real_inner_self_eq_norm_sq]
  exact smoothTwoFormL2Inner_self u

end
end PositiveEinsteinFour.Geometry
end


section

/-! Frame-independent energies descend continuously through the compact
frame bundle. Their integrability follows from finite Riemannian volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [CompactSpace (FrameBundle g)]

variable [T3Space M]

variable [MeasurableSpace M] [BorelSpace M]

theorem totalGradientEnergy_integrable (d : MetricGreenData g μ) (opposite : OppositeWeylData d)
    (o : FrameOrientation g) (hRic : RicciThree g) (hvolume : FinitePositiveVolume g) :
    Integrable (fun c => plusGradientEnergy o c + minusGradientEnergy o c) (normalizedVolume g) := by
  let : CompactSpace M := compactSpace_of_compact_frames (g := g)
  let : IsProbabilityMeasure (normalizedVolume g) := normalizedVolume_isProbability hvolume
  exact (continuous_totalGradientEnergy d opposite o hRic).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem orientedNormSquares_integrable (o : FrameOrientation g)
    (hnorm : PetersenOrientedNormInput o) (hvolume : FinitePositiveVolume g) :
    Integrable (fun c => plusNorm o c ^ 2) (normalizedVolume g) ∧
      Integrable (fun c => minusNorm o c ^ 2) (normalizedVolume g) := by
  let : CompactSpace M := compactSpace_of_compact_frames (g := g)
  let : IsProbabilityMeasure (normalizedVolume g) := normalizedVolume_isProbability hvolume
  exact ⟨hnorm.plusSquareSmooth.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _),
    hnorm.minusSquareSmooth.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Extension of the actual Hodge involution to the L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothL2HodgeLinear : SmoothL2TwoForm o →ₗ[ℝ] SmoothL2TwoForm o :=
  smoothTwoFormHodge o

def smoothL2Hodge : SmoothL2TwoForm o →ₗᵢ[ℝ] SmoothL2TwoForm o where
  toLinearMap := smoothL2HodgeLinear
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [smoothTwoForm_norm_sq, smoothTwoForm_norm_sq]
    apply integral_congr_ae
    filter_upwards [] with x
    change ‖twoFormHodge ((u : smoothTwoForms o).val x)‖ ^ 2 = _
    rw [twoFormHodge.norm_map]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Einstein curvature preserves the actual Hodge splitting. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormMatrixMul (K : Matrix (Fin 6) (Fin 6) ℝ) (a : TwoFormFour) : TwoFormFour :=
  WithLp.toLp 2 (K *ᵥ WithLp.ofLp a)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form Hodge star as a six-dimensional matrix, and
its action on the first pair of curvature indices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormHodgeMatrix_apply (a : TwoFormFour) :
    WithLp.toLp 2 (twoFormHodgeMatrix *ᵥ WithLp.ofLp a) = twoFormHodge a := by
  ext i
  fin_cases i <;>
    simp [twoFormHodgeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      twoFormHodge, twoFormHodgeLinear]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-variation boundary for a common affine endpoint curve is
independent of the chart used for the adjacent curve segment. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalEndpoint_velocity_chart (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) :
    chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) *ᵥ
      (fun i => frameChartMatrix g e.base e i 0) =
        (fun i => frameChartMatrix g c e i 0) := by
  have h := congrArg (fun E : Mat4 => fun i => E i 0)
    (frameChartMatrix_change g e.base c e (mem_chart_source FourSpace e.base) hc)
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using! h

def normalEndpointBoundary (g : SmoothMetric M) (e : FrameBundle g) (a : Fin 3 → ℝ) : ℝ :=
  chartEnergyBoundary g e.base (chartAt FourSpace e.base e.base)
    (fun i => frameChartMatrix g e.base e i 0) (normalEndpointDirection g e a) 0

theorem normalEndpoint_boundary_chart (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    chartEnergyBoundary g c (chartAt FourSpace c e.base)
      (fun i => frameChartMatrix g c e i 0) (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
      (WithLp.ofLp (endpointChartSecond e.base c (chartAt FourSpace e.base e.base)
        (normalEndpointDirection g e a) 0)) = normalEndpointBoundary g e a := by
  have hz := (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hd : (chartAt FourSpace e.base).symm (chartAt FourSpace e.base e.base) ∈
      (chartAt FourSpace c).source := by
    simpa only [(chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)] using hc
  have h := chartEnergyBoundary_transition g e.base c (chartAt FourSpace e.base e.base)
    hz hd (fun i => frameChartMatrix g e.base e i 0) (normalEndpointDirection g e a) 0
  have hcoord : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    simp only [chartTransition, (chartAt FourSpace e.base).left_inv
      (mem_chart_source FourSpace e.base)]
  rw [hcoord, normalEndpoint_velocity_chart g e c hc,
    normalEndpoint_first_chart g e c hc a] at h
  simpa only [normalEndpointBoundary, endpointChartSecond_zero, WithLp.ofLp_toLp,
    chartTransitionSecondJet, Matrix.mulVec_zero, zero_add] using h.symm

theorem normalEndpointBoundary_zero (g : SmoothMetric M) (e : FrameBundle g) :
    normalEndpointBoundary g e 0 = 0 := by
  have hz : (Fin.cons (0 : ℝ) (0 : Fin 3 → ℝ) : Fin 4 → ℝ) = 0 := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  unfold normalEndpointBoundary normalEndpointDirection
  rw [hz, Matrix.mulVec_zero]
  exact chartEnergyBoundary_zero _ _ _ _

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The Riemannian volume, evaluated on a measurable
set in one chart. This is the target measure for the weighted area bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeMeasure_chart_image (g : SmoothMetric M) (c : M)
    (A : Set M) (hA : MeasurableSet A) (hAc : A ⊆ (chartAt FourSpace c).source) :
    volumeMeasure g A = riemannianChartFactor *
      ∫⁻ z in (chartAt FourSpace c) '' A, ENNReal.ofReal (chartVolumeDensity g c z) := by
  let B := (chartAt FourSpace c) '' A
  have hB : MeasurableSet B := chart_image_measurable c A hA hAc
  have hBt : B ⊆ (chartAt FourSpace c).target := by
    rintro z ⟨x, hx, rfl⟩
    exact (chartAt FourSpace c).map_source (hAc hx)
  have hback : (chartAt FourSpace c).symm '' B = A := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      rwa [(chartAt FourSpace c).left_inv (hAc hy)]
    · intro hx
      exact ⟨chartAt FourSpace c x, ⟨x, hx, rfl⟩, (chartAt FourSpace c).left_inv (hAc hx)⟩
  have h := congrArg (fun μ : Measure FourSpace => μ B) (chartHausdorffMeasure_eq_density g c)
  simp only [Measure.restrict_apply hB, inter_eq_left.mpr hBt,
    Measure.smul_apply, smul_eq_mul] at h
  rw [chartHausdorffMeasure_apply g c B hB hBt, hback, withDensity_apply _ hB] at h
  rw [volumeMeasure_eq_scaled_hausdorff, Measure.smul_apply, smul_eq_mul, h]
  exact (mul_assoc _ _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! An almost-everywhere chart representative is a representative for
the actual normalized Riemannian measure on the corresponding base open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

/-- Lebesgue almost-everywhere equality in a chart transfers to actual
normalized volume.  No measurability assumption on the representatives is
needed, and the open set need not be contained in the chart target. -/
theorem scalar_chart_representative_ae (g : SmoothMetric M) (c : M)
    (U : Set FourSpace) (hU : IsOpen U) (b : M → ℝ) (F : FourSpace → ℝ)
    (h : (fun z => b ((chartAt FourSpace c).symm z)) =ᵐ[volume.restrict U] F) :
    b =ᵐ[(normalizedVolume g).restrict
      ((chartAt FourSpace c).source ∩ (chartAt FourSpace c) ⁻¹' U)]
      (fun x => F (chartAt FourSpace c x)) := by
  let e := chartAt FourSpace c
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let φ : ChartTarget c → M := fun z => e.symm z.val
  have he : MeasurableEmbedding φ :=
    e.symm.isOpenEmbedding_restrict.measurableEmbedding
  have hfull : ∀ᵐ z ∂(volume : Measure FourSpace),
      z ∈ U → b (e.symm z) = F z :=
    (ae_restrict_iff' hU.measurableSet).mp h
  have hsub : ∀ᵐ z ∂μ, z.val ∈ U → b (e.symm z.val) = F z.val :=
    (ae_restrict_iff_subtype e.open_target.measurableSet).mp
      (ae_restrict_of_ae hfull)
  have hweight : ∀ᵐ z ∂μ.withDensity ρ,
      z.val ∈ U → b (e.symm z.val) = F z.val :=
    hsub.filter_mono (withDensity_absolutelyContinuous μ ρ).ae_le
  have hmap : ∀ᵐ x ∂Measure.map φ (μ.withDensity ρ),
      e x ∈ U → b x = F (e x) := by
    apply he.ae_map_iff.mpr
    filter_upwards [hweight] with z hz
    change e (e.symm z.val) ∈ U → b (e.symm z.val) = F (e (e.symm z.val))
    rwa [e.right_inv z.property]
  have hsource : ∀ᵐ x ∂(normalizedVolume g).restrict e.source,
      e x ∈ U → b x = F (e x) := by
    rw [normalizedVolume_restrict_chart g c]
    exact Measure.ae_smul_measure hmap (normalizedChartFactor g)
  have hbase := (ae_restrict_iff' e.open_source.measurableSet).mp hsource
  apply (ae_restrict_iff' (e.isOpen_inter_preimage hU).measurableSet).mpr
  filter_upwards [hbase] with x hx
  intro hxU
  exact hx hxU.1 hxU.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar first jet and its Dirichlet pairing.  The Hilbert space
below is the closure of smooth first jets, with the value coordinate retained;
no solvability or elliptic estimate is built into its definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable {μ : Measure (FrameBundle g)} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The actual scalar Dirichlet pairing in the frame measure. -/
def smoothScalarDirichlet (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) : ℝ :=
  ∑ i : Fin 4, inner ℝ (smoothScalarGradientL2 d i a) (smoothScalarGradientL2 d i b)

theorem smoothScalarDirichlet_eq_integral (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    smoothScalarDirichlet d a b =
      ∫ e, ∑ i, scalarGradient g a e i * scalarGradient g b e i ∂μ := by
  unfold smoothScalarDirichlet smoothScalarGradientL2
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousMap.inner_toLp, conj_trivial]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with e
    exact mul_comm _ _
  · intro i _
    exact ((actual_scalarGradient_continuous g a.property i).mul
      (actual_scalarGradient_continuous g b.property i)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem smoothScalarDirichlet_green (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    smoothScalarDirichlet d a b = -(∫ e, a.val e.base * scalarLaplacian g b e ∂μ) := by
  rw [smoothScalarDirichlet_eq_integral]
  exact (smoothScalarData d a).scalar_pairing_green (smoothScalarData d b)

theorem smoothScalarDirichlet_symm (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) : smoothScalarDirichlet d a b = smoothScalarDirichlet d b a := by
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported Euclidean test functions inside a chart extend to
genuine global smooth scalar tests, by zero outside that chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarChartLift (c : M) (ψ : FourSpace → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ (chartAt FourSpace c).source then ψ (chartAt FourSpace c x) else 0

omit [IsManifold I4 ∞ M] in
theorem scalarChartLift_on_source (c : M) (ψ : FourSpace → ℝ) {x : M}
    (hx : x ∈ (chartAt FourSpace c).source) :
    scalarChartLift c ψ x = ψ (chartAt FourSpace c x) := by
  simp only [scalarChartLift, ite_eq_left hx]

omit [IsManifold I4 ∞ M] in
theorem scalarChartLift_symm (c : M) (ψ : FourSpace → ℝ) {z : FourSpace}
    (hz : z ∈ (chartAt FourSpace c).target) :
    scalarChartLift c ψ ((chartAt FourSpace c).symm z) = ψ z := by
  rw [scalarChartLift_on_source c ψ ((chartAt FourSpace c).map_target hz),
    (chartAt FourSpace c).right_inv hz]

omit [IsManifold I4 ∞ M] in
theorem scalarChartLift_support (c : M) (ψ : FourSpace → ℝ) :
    support (scalarChartLift c ψ) ⊆ (chartAt FourSpace c).symm '' tsupport ψ := by
  classical
  intro x hx
  by_cases hs : x ∈ (chartAt FourSpace c).source
  · refine ⟨chartAt FourSpace c x, subset_closure ?_, (chartAt FourSpace c).left_inv hs⟩
    simpa only [mem_support, scalarChartLift, ite_eq_left hs] using hx
  · exact False.elim (hx (by simp only [scalarChartLift, ite_eq_right hs]))

theorem scalarChartLift_smooth [T2Space M] (c : M) (ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (scalarChartLift c ψ) := by
  let K := (chartAt FourSpace c).symm '' tsupport ψ
  have hK : IsCompact K := hc.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hs)
  have hKs : K ⊆ (chartAt FourSpace c).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (chartAt FourSpace c).map_target (hs hz)
  intro x
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · have h := hψ.contMDiff.contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hx)
    apply h.congr_of_eventuallyEq
    filter_upwards [(chartAt FourSpace c).open_source.mem_nhds hx] with y hy
    exact scalarChartLift_on_source c ψ hy
  · have hxK : x ∉ K := fun hxK => hx (hKs hxK)
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact notMem_support.mp (fun h => hy (scalarChartLift_support c ψ h))

def scalarChartTest [T2Space M] (c : M) (ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) : SmoothScalar (M := M) :=
  ⟨scalarChartLift c ψ, scalarChartLift_smooth c ψ hψ hc hs⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous mean and its kernel on the actual scalar first-jet
completion.  Mean subtraction changes only the value coordinate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section FirstJet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarH1MeanZero_closed (d : ParallelMetricData g μ) :
    IsClosed (scalarH1MeanZero d : Set (scalarH1 d)) :=
  (scalarH1Mean d).isClosed_ker

theorem scalarH1Value_subtractMean (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1Value d (scalarH1SubtractMean d u) =
      scalarH1Value d u - scalarH1Mean d u • scalarL2One g μ := by
  rw [scalarH1SubtractMean_apply, map_sub, map_smul, scalarH1Value_one]

variable [IsProbabilityMeasure μ]

/-- The mean-subtraction projection with its closed mean-zero codomain. -/
def scalarH1MeanZeroProjection (d : ParallelMetricData g μ) :
    scalarH1 d →L[ℝ] scalarH1MeanZero d :=
  (scalarH1SubtractMean d).codRestrict (scalarH1MeanZero d)
    (fun u => scalarH1Mean_subtractMean d u)

theorem smoothScalarSubtractMean_mean_zero (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    (∫ e, (smoothScalarSubtractMean (μ := μ) a).val e.base ∂μ) = 0 := by
  rw [← scalarH1Mean_smooth d, smoothScalarSubtractMean_toH1,
    scalarH1Mean_subtractMean]

end FirstJet

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local smooth representatives of one actual L2 function agree on
overlaps by full support of Riemannian volume, and hence glue globally. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The gluing uses only the actual full-support volume and local smooth
representatives.  No global smoothness or elliptic premise is assumed. -/
theorem scalar_smooth_representative_of_local (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g))
    (hlocal : ∀ x : M, ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) ∞ f U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] f) :
    ∃ F : SmoothScalar (M := M), F.val =ᵐ[normalizedVolume g] b := by
  let := normalizedVolume_isOpenPosMeasure g
  choose U f hU hx hf hb using hlocal
  let F : M → ℝ := fun x => f x x
  have hagree (x y : M) (hy : y ∈ U x) : F y = f x y := by
    have hb₁ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hb y)
    have hb₂ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hb x)
    have heq : EqOn (f y) (f x) (U y ∩ U x) :=
      Measure.eqOn_open_of_ae_eq (hb₁.symm.trans hb₂) ((hU y).inter (hU x))
        ((hf y).continuousOn.mono inter_subset_left)
        ((hf x).continuousOn.mono inter_subset_right)
    exact heq ⟨hx y, hy⟩
  have hF : ContMDiff I4 𝓘(ℝ, ℝ) ∞ F := by
    intro x
    apply ((hf x).contMDiffAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq
    filter_upwards [(hU x).mem_nhds (hx x)] with y hy
    exact hagree x y hy
  refine ⟨⟨F, hF⟩, ?_⟩
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have heach (x : M) : ∀ᵐ y ∂normalizedVolume g, y ∈ U x → F y = b y := by
    have he := (ae_restrict_iff' (hU x).measurableSet).mp (hb x)
    filter_upwards [he] with y hy
    intro hyU
    exact (hagree x y hyU).trans (hy hyU).symm
  have hfin : ∀ᵐ y ∂normalizedVolume g, ∀ x : s, y ∈ U x → F y = b y :=
    ae_all_iff.mpr (fun x => heach x)
  filter_upwards [hfin] with y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact hy ⟨x, hxs⟩ hyx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compatibility of the weak shifted solution with the actual smooth scalar
Laplacian.  Smooth jets determine the entire Hilbert completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

def smoothScalarLaplacianField (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    C(FrameBundle g, ℝ) :=
  ⟨scalarLaplacian g a,
    continuous_finsetSum _ (fun i _ => actual_scalarHessian_continuous g a.property i i)⟩

def smoothScalarLaplacianL2 (a : SmoothScalar (M := M)) : ScalarL2 g μ :=
  ContinuousMap.toLp 2 μ ℝ (smoothScalarLaplacianField g a)

def smoothScalarShiftedRhs (a : SmoothScalar (M := M)) : ScalarL2 g μ :=
  smoothScalarValueL2 g μ a - smoothScalarLaplacianL2 a

theorem smoothScalarShiftedRhs_pairing (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarShiftedRhs (g := g) (μ := μ) a) (smoothScalarValueL2 g μ b) =
      inner ℝ (smoothScalarValueL2 g μ a) (smoothScalarValueL2 g μ b) +
        smoothScalarDirichlet d a b := by
  rw [smoothScalarShiftedRhs, inner_sub_left]
  have h : inner ℝ (smoothScalarLaplacianL2 (g := g) (μ := μ) a)
      (smoothScalarValueL2 g μ b) = ∫ e, b.val e.base * scalarLaplacian g a e ∂μ := by
    simpa only [conj_trivial] using!
      ContinuousMap.inner_toLp μ (smoothScalarLaplacianField g a) (smoothScalarValue g b)
  rw [h, smoothScalarDirichlet_symm d a b, smoothScalarDirichlet_green]
  exact sub_eq_add_neg _ _

theorem scalarH1_eq_of_smooth_tests (d : ParallelMetricData g μ) (u v : scalarH1 d)
    (h : ∀ a : SmoothScalar (M := M),
      inner ℝ u (smoothScalarToH1 d a) = inner ℝ v (smoothScalarToH1 d a)) : u = v := by
  have hc : IsClosed {w : ScalarJetL2 g μ | inner ℝ u.val w = inner ℝ v.val w} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hs : closure (range (smoothScalarFirstJet d)) ⊆
      {w : ScalarJetL2 g μ | inner ℝ u.val w = inner ℝ v.val w} := by
    apply hc.closure_subset_iff.mpr
    rintro w ⟨a, rfl⟩
    exact h a
  apply ext_inner_right ℝ
  intro w
  exact hs w.property

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exterior and trace tensors of a two-form covariant derivative.
Their norms are independent of the orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormExteriorTensor_apply (A : CovariantCoordinates 3) (i j k : Fin 4) :
    twoFormExteriorTensor A ![i,j,k] =
      twoFormExteriorComponent (fun p q r => A ![p,q,r]) i j k := by
  have hs : ![i,j,k] ∘ Equiv.swap (0 : Fin 3) 1 = ![j,i,k] := by
    funext a
    fin_cases a <;> simp [Equiv.swap_apply_def]
  have hc : ![i,j,k] ∘ (Equiv.swap (0 : Fin 3) 2).trans (Equiv.swap 0 1) = ![k,i,j] := by
    funext a
    fin_cases a <;> simp [Function.comp_def, Equiv.swap_apply_def]
  simp only [twoFormExteriorTensor, Pi.add_apply, Pi.sub_apply, hs, hc,
    twoFormExteriorComponent]

theorem twoFormExteriorTensor_frame (E : Mat4) (A : CovariantCoordinates 3) :
    twoFormExteriorTensor (frameTensor E A) = frameTensor E (twoFormExteriorTensor A) := by
  funext v
  simp only [twoFormExteriorTensor, Pi.add_apply, Pi.sub_apply,
    frameTensor_add, frameTensor_sub, frameTensor_permute]

theorem trace_three_frame (E : Mat4) (A : CovariantCoordinates 3)
    (k : Fin 4) : (∑ i, frameTensor E A ![i,i,k]) =
      ∑ a, ∑ b, ∑ c, (E * Eᵀ) a b * E c k * A ![a,b,c] := by
  simp only [frameTensor_three]
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ i, E a i * E b i * E c k * A ![a,b,c] := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = _ := by
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

theorem twoFormCodiffTensor_frame (E : Mat4) (hE : E * Eᵀ = 1)
    (A : CovariantCoordinates 3) :
    twoFormCodiffTensor (frameTensor E A) = frameTensor E (twoFormCodiffTensor A) := by
  funext v
  have hv : ![v 0] = v := by ext i; fin_cases i; rfl
  rw [← hv]
  change -(∑ i, frameTensor E A ![i,i,v 0]) =
    frameTensor E (twoFormCodiffTensor A) (Fin.cons (v 0) ![])
  rw [trace_three_frame, hE, frameTensor_cons]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, frameTensor_zero,
    twoFormCodiffTensor, Fin.cons_zero]
  have hs (a : Fin 4) :
      (∑ b : Fin 4, ∑ c : Fin 4,
        if a = b then E c (v 0) * A ![a,b,c] else (0 : ℝ)) =
        ∑ c : Fin 4, E c (v 0) * A ![a,a,c] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp
  change -(∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    if a = b then E c (v 0) * A ![a,b,c] else (0 : ℝ)) =
      ∑ c : Fin 4, E c (v 0) * -(∑ a : Fin 4, A ![a,a,c])
  simp only [hs]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]

theorem twoFormDeRhamQuadratic_tensor (A : CovariantCoordinates 3) :
    twoFormDeRhamQuadratic (fun i j k => A ![i,j,k]) =
      (1 / 6 : ℝ) * frameTensorSquareNorm (twoFormExteriorTensor A) +
        frameTensorSquareNorm (twoFormCodiffTensor A) := by
  have he : frameTensorSquareNorm (twoFormExteriorTensor A) =
      ∑ i, ∑ j, ∑ k, twoFormExteriorComponent (fun p q r => A ![p,q,r]) i j k ^ 2 := by
    rw [frameTensorSquareNorm, frameTensorPairing_three]
    simp only [twoFormExteriorTensor_apply, pow_two]
  have hc : frameTensorSquareNorm (twoFormCodiffTensor A) =
      ∑ k, twoFormCodiffComponent (fun p q r => A ![p,q,r]) k ^ 2 := by
    unfold frameTensorSquareNorm frameTensorPairing
    simp only [sum_tensor_indices_cons, Fintype.sum_unique, pow_two]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [he, hc]
  rfl

theorem twoFormDeRhamQuadratic_frame (E : Mat4) (hE : E * Eᵀ = 1)
    (A : CovariantCoordinates 3) :
    twoFormDeRhamQuadratic (fun i j k => frameTensor E A ![i,j,k]) =
      twoFormDeRhamQuadratic (fun i j k => A ![i,j,k]) := by
  rw [twoFormDeRhamQuadratic_tensor, twoFormDeRhamQuadratic_tensor,
    twoFormExteriorTensor_frame, twoFormCodiffTensor_frame E hE,
    frameTensor_norm_orthogonal E hE, frameTensor_norm_orthogonal E hE]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual C4 scalar cutoff used in the heat
parametrix, paired against smooth scalar eigenfunctions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalar_finite_value_derivative (d : ParallelMetricData g μ) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => f ((d.flow i).map s e).base)
      (scalarGradient g f ((d.flow i).map t e) i) t := by
  have h := scalar_finite_parallel_derivative g hf _ t i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) 0 (by omega) ![]
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · beta_reduce
    rw [frameTensor_zero]
    change f ((d.flow i).map s e).base = f ((chartAt FourSpace
      ((d.flow i).map s e).base).symm (chartAt FourSpace
        ((d.flow i).map s e).base ((d.flow i).map s e).base))
    rw [(chartAt FourSpace _).left_inv (mem_chart_source FourSpace _)]
  · rfl

theorem scalar_finite_gradient_derivative (d : ParallelMetricData g μ) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (i j : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => scalarGradient g f ((d.flow i).map s e) j)
      (scalarHessian g f ((d.flow i).map t e) i j) t :=
  scalar_finite_parallel_derivative g hf _ t i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) 1 (by omega) ![j]

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalar_finite_pairing_green (d : ParallelMetricData g μ) {f h : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (hh : ContMDiff I4 𝓘(ℝ, ℝ) 4 h) :
    (∫ e, ∑ i : Fin 4, scalarGradient g f e i * scalarGradient g h e i ∂μ) =
      -(∫ e, f e.base * scalarLaplacian g h e ∂μ) := by
  let fv : C(FrameBundle g, ℝ) := ⟨fun e => f e.base,
    hf.continuous.comp (continuous_frameBase g)⟩
  let fg (i : Fin 4) : C(FrameBundle g, ℝ) :=
    ⟨fun e => scalarGradient g f e i, scalar_finite_gradient_continuous g hf i⟩
  let hg (i : Fin 4) : C(FrameBundle g, ℝ) :=
    ⟨fun e => scalarGradient g h e i, scalar_finite_gradient_continuous g hh i⟩
  let hH (i : Fin 4) : C(FrameBundle g, ℝ) :=
    ⟨fun e => scalarHessian g h e i i, scalar_finite_hessian_continuous g hh i i⟩
  have hi (i : Fin 4) := scalar_flow_green (d := d.toMetricGreenData) i fv (fg i)
    (hg i) (hH i) (scalar_finite_value_derivative d hf i)
      (scalar_finite_gradient_derivative d hh i i)
  have hl (i : Fin 4) : Integrable
      (fun e => scalarGradient g f e i * scalarGradient g h e i) μ :=
    ((fg i).continuous.mul (hg i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : Fin 4) : Integrable (fun e => f e.base * scalarHessian g h e i i) μ :=
    (fv.continuous.mul (hH i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp only [fv, fg, hg, hH, ContinuousMap.coe_mk] at hi
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e => (Finset.mul_sum _ _ _).symm

theorem scalar_finite_laplacian_symmetric (d : ParallelMetricData g μ) {f h : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (hh : ContMDiff I4 𝓘(ℝ, ℝ) 4 h) :
    (∫ e, scalarLaplacian g f e * h e.base ∂μ) =
      ∫ e, f e.base * scalarLaplacian g h e ∂μ := by
  have hfG := scalar_finite_pairing_green d hf hh
  have hhG := scalar_finite_pairing_green d hh hf
  have hgrad : (fun e : FrameBundle g =>
      ∑ i : Fin 4, scalarGradient g f e i * scalarGradient g h e i) =
      fun e => ∑ i : Fin 4, scalarGradient g h e i * scalarGradient g f e i := by
    funext e
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hgrad] at hfG
  have hi : (∫ e, scalarLaplacian g f e * h e.base ∂μ) =
      ∫ e, h e.base * scalarLaplacian g f e ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun e => mul_comm _ _
  linarith only [hfG, hhG, hi]

variable [T3Space M] [CompactSpace M]

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalar_finite_laplacian_continuous {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) : Continuous (scalarLaplacianBase g f) := by
  let := actual_compactFrameBundle g
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  change Continuous (fun e : FrameBundle g => scalarLaplacianBase g f e.base)
  simp_rw [← scalarLaplacian_eq_base]
  exact continuous_finsetSum _ (fun i _ => scalar_finite_hessian_continuous g hf i i)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalar_finite_laplacian_base_symmetric (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {f h : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (hh : ContMDiff I4 𝓘(ℝ, ℝ) 4 h) :
    (∫ x, scalarLaplacianBase g f x * h x ∂normalizedVolume g) =
      ∫ x, f x * scalarLaplacianBase g h x ∂normalizedVolume g := by
  let := actual_compactFrameBundle g
  have hleft : Continuous (fun x => scalarLaplacianBase g f x * h x) :=
    (scalar_finite_laplacian_continuous (g := g) hf).mul hh.continuous
  have hright : Continuous (fun x => f x * scalarLaplacianBase g h x) :=
    hf.continuous.mul (scalar_finite_laplacian_continuous (g := g) hh)
  rw [← (canonicalFrameMeasure_base g o).map_eq,
    integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable hleft.aestronglyMeasurable,
    integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable hright.aestronglyMeasurable]
  simpa only [← scalarLaplacian_eq_base] using scalar_finite_laplacian_symmetric d hf hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth Poincaré estimate passes to the actual first-jet completion.
It makes the Dirichlet form coercive on the closed mean-zero subspace and
therefore supplies a unique mean-zero weak Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

local instance scalarCoercive_h1Space (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1 d) := Submodule.normedSpace (𝕜 := ℝ) (scalarH1 d)

local instance scalarCoercive_meanZeroSpace (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1MeanZero d) :=
  Submodule.normedSpace (𝕜 := ℝ) (scalarH1MeanZero d)

local instance scalarCoercive_h1Inner_r588f22_1 (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1 d) := Submodule.innerProductSpace _
local instance scalarCoercive_meanZeroInner_r588f22_1 (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1MeanZero d) := Submodule.innerProductSpace _
/-- Center the value coordinate before taking closure.  This avoids needing
an independently chosen smooth mean-zero approximation. -/
theorem scalarH1_centered_poincare (d : ParallelMetricData g μ) {K : ℝ}
    (hP : SmoothScalarPoincare d K) (u : scalarH1 d) :
    ‖scalarH1Value d u - scalarH1Mean d u • scalarL2One g μ‖ ^ 2 ≤
      K * ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  let p₀ : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none
  let pᵢ (i : Fin 4) : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)
  let m : ScalarJetL2 g μ →L[ℝ] ℝ := (innerSL ℝ (scalarL2One g μ)).comp p₀
  let S : Set (ScalarJetL2 g μ) := {v |
    ‖p₀ v - m v • scalarL2One g μ‖ ^ 2 ≤ K * ∑ i : Fin 4, ‖pᵢ i v‖ ^ 2}
  have hclosed : IsClosed S := isClosed_le
    ((p₀.continuous.sub (m.continuous.smul continuous_const)).norm.pow 2)
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => (pᵢ i).continuous.norm.pow 2)))
  have hsub : range (smoothScalarFirstJet d) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    change ‖scalarH1Value d (smoothScalarToH1 d a) -
      scalarH1Mean d (smoothScalarToH1 d a) • scalarL2One g μ‖ ^ 2 ≤
      K * ∑ i : Fin 4, ‖scalarH1Gradient d i (smoothScalarToH1 d a)‖ ^ 2
    rw [← scalarH1Value_subtractMean, ← smoothScalarSubtractMean_toH1]
    simpa only [scalarH1Value_smooth, scalarH1Gradient_smooth,
      smoothScalarGradientL2_subtractMean] using
      hP (smoothScalarSubtractMean (μ := μ) a) (smoothScalarSubtractMean_mean_zero d a)
  exact (hclosed.closure_subset_iff.mpr hsub) u.property

theorem scalarH1_poincare (d : ParallelMetricData g μ) {K : ℝ}
    (hP : SmoothScalarPoincare d K) (u : scalarH1 d)
    (hu : scalarH1Mean d u = 0) :
    ‖scalarH1Value d u‖ ^ 2 ≤ K * ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  simpa only [hu, zero_smul, sub_zero] using scalarH1_centered_poincare d hP u

/-- Restrict the scalar value map to the mean-zero Hilbert subspace. -/
def scalarMeanZeroValue (d : ParallelMetricData g μ) :
    scalarH1MeanZero d →L[ℝ] ScalarL2 g μ :=
  (scalarH1Value d).comp (scalarH1MeanZero d).subtypeL

/-- Restrict each of the four actual scalar derivatives to that subspace. -/
def scalarMeanZeroGradient (d : ParallelMetricData g μ) (i : Fin 4) :
    scalarH1MeanZero d →L[ℝ] ScalarL2 g μ :=
  (scalarH1Gradient d i).comp (scalarH1MeanZero d).subtypeL

/-- The bounded Dirichlet bilinear form on the actual mean-zero space. -/
def scalarMeanZeroDirichlet (d : ParallelMetricData g μ) :
    scalarH1MeanZero d →L[ℝ] scalarH1MeanZero d →L[ℝ] ℝ :=
  fourGradientDirichlet (E := scalarH1MeanZero d) (F := ScalarL2 g μ)
    (scalarMeanZeroGradient d)

theorem scalarMeanZeroDirichlet_apply (d : ParallelMetricData g μ)
    (u v : scalarH1MeanZero d) :
    scalarMeanZeroDirichlet d u v =
      ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u.val) (scalarH1Gradient d i v.val) := by
  exact @fourGradientDirichlet_apply (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroSpace d) _ _ (scalarMeanZeroGradient d) u v

theorem scalarMeanZeroDirichlet_self (d : ParallelMetricData g μ)
    (u : scalarH1MeanZero d) :
    scalarMeanZeroDirichlet d u u = ∑ i : Fin 4, ‖scalarH1Gradient d i u.val‖ ^ 2 := by
  rw [scalarMeanZeroDirichlet_apply]
  simp only [real_inner_self_eq_norm_sq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual first-jet completion.  This identifies
the variational equation with the distributional scalar Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem smoothScalarDirichlet_laplacian_pairing (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    smoothScalarDirichlet d a b =
      -(inner ℝ (smoothScalarValueL2 g μ a) (smoothScalarLaplacianL2 (μ := μ) b)) := by
  have h := smoothScalarShiftedRhs_pairing d b a
  rw [smoothScalarShiftedRhs, inner_sub_left,
    smoothScalarDirichlet_symm d b a,
    real_inner_comm (smoothScalarValueL2 g μ a)
      (smoothScalarLaplacianL2 (μ := μ) b)] at h
  linarith

theorem scalarH1_green (d : ParallelMetricData g μ) (u : scalarH1 d)
    (b : SmoothScalar (M := M)) :
    (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (smoothScalarGradientL2 d i b)) =
      -(inner ℝ (scalarH1Value d u) (smoothScalarLaplacianL2 (μ := μ) b)) := by
  let p₀ : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none
  let pᵢ (i : Fin 4) : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)
  let S : Set (ScalarJetL2 g μ) := {v |
    (∑ i : Fin 4, inner ℝ (pᵢ i v) (smoothScalarGradientL2 d i b)) =
      -(inner ℝ (p₀ v) (smoothScalarLaplacianL2 (μ := μ) b))}
  have hclosed : IsClosed S := isClosed_eq
    (continuous_finsetSum _ (fun i _ => (pᵢ i).continuous.inner continuous_const))
    (p₀.continuous.inner continuous_const).neg
  have hsub : range (smoothScalarFirstJet d) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact smoothScalarDirichlet_laplacian_pairing d a b
  exact (hclosed.closure_subset_iff.mpr hsub) u.property

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual exterior derivative of one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoCovariantAlternation_pairing (D A : CovariantCoordinates 2)
    (hA : ∀ i j, A ![j,i] = -A ![i,j]) :
    frameTensorPairing (twoCovariantAlternation D) A =
      2 * ∑ i, ∑ j, D ![i,j] * A ![i,j] := by
  have hsplit : frameTensorPairing (twoCovariantAlternation D) A =
      (∑ i, ∑ j, D ![i,j] * A ![i,j]) - (∑ i, ∑ j, D ![j,i] * A ![i,j]) := by
    unfold frameTensorPairing
    simp only [sum_tensor_indices_cons, Fintype.sum_unique]
    change (∑ i, ∑ j, twoCovariantAlternation D ![i,j] * A ![i,j]) = _
    simp only [twoCovariantAlternation_apply, sub_mul, Finset.sum_sub_distrib]
  have hs : (∑ i, ∑ j, D ![j,i] * A ![i,j]) = -(∑ i, ∑ j, D ![i,j] * A ![i,j]) := by
    rw [Finset.sum_comm]
    have hi (i j : Fin 4) : D ![i,j] * A ![j,i] = -(D ![i,j] * A ![i,j]) := by
      rw [hA i j, mul_neg]
    simp only [hi, Finset.sum_neg_distrib]
  rw [hs] at hsplit
  linarith only [hsplit]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_3
omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormExterior_framed_tensor (u : smoothCovariantFields M 1)
    (e : FrameBundle g) :
    twoFormFramedValue o (smoothOneFormExterior (o := o) u).val e =
      twoCovariantAlternation (covariantFieldFramed g (covariantFieldDerivative g u.val) e) := by
  funext a
  have ha : a = ![a 0,a 1] := by ext i; fin_cases i <;> rfl
  rw [ha]
  exact (smoothOneFormExterior_framed u e _ _).trans (twoCovariantAlternation_apply _ _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual normal Jacobi equation.
The quadratic term uses the Euclidean coordinate pairing. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

theorem MatrixJacobiSolution.index_integral_zero_of_kernel {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ) (c : ℝ)
    (hc : d.J c *ᵥ w = 0) :
    (∫ s in (0 : ℝ)..c, normalIndexDensity (R s) (d.J s *ᵥ w) (d.V s *ᵥ w)) = 0 := by
  rw [d.index_integral_eq_boundary hR w 0 c, hc, d.initial_position]
  simp

end
end PositiveEinsteinFour.Jacobi

end


section

/-! A common chart interval works for every direction and every nearby
initial frame. Compactness is used only for the unit direction sphere. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem unitGeodesic_common_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ δ > (0 : ℝ),
      ∀ e' ∈ U, ∀ q : Directions, ∀ s ∈ Ioo (-δ) δ,
        unitGeodesic g o (unitTangentTurn e' q) s ∈ (chartAt FourSpace c).source := by
  let b : (ℝ × FrameBundle g) × Directions → M :=
    fun z => unitGeodesic g o (unitTangentTurn z.1.2 z.2) z.1.1
  have hb : Continuous b := by
    have harg : Continuous (fun z : (ℝ × FrameBundle g) × Directions =>
        (z.1.1, unitTangentTurn z.1.2 z.2)) :=
      continuous_fst.fst.prodMk
        (continuous_unitTangentTurn.comp (continuous_fst.snd.prodMk continuous_snd))
    exact (continuous_unitTangentBase g).comp ((unitTangentFlowMap_continuous g o).comp harg)
  have hz : ({((0 : ℝ), e)} : Set (ℝ × FrameBundle g)) ×ˢ (univ : Set Directions) ⊆
      b ⁻¹' (chartAt FourSpace c).source := by
    rintro ⟨p, q⟩ ⟨hp, _⟩
    have hp' : p = (0, e) := hp
    subst p
    simpa [b, unitGeodesic_turn_zero] using he
  obtain ⟨T, V, hT, _, h0, hV, hTV⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ ((chartAt FourSpace c).open_source.preimage hb) hz
  have ht : T ∈ 𝓝 ((0 : ℝ), e) := hT.mem_nhds (h0 rfl)
  obtain ⟨I, U, hI, h0I, hU, heU, hIU⟩ := mem_nhds_prod_iff'.mp ht
  obtain ⟨δ, hδ, hδI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds h0I)
  refine ⟨U, hU, heU, δ, hδ, ?_⟩
  intro e' he' q s hs
  have hsI : s ∈ I := hδI (by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hs)
  exact hTV (show ((s, e'), q) ∈ T ×ˢ V from
    ⟨hIU (show (s, e') ∈ I ×ˢ U from ⟨hsI, he'⟩), hV (mem_univ q)⟩)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A zero-ended, piecewise smooth negative-index variation after a conjugate
point.  The action is written as the sum on the two smooth pieces. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

theorem indexEndpointBump_values {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (v : Fin 3 → ℝ) :
    indexEndpointBump c b v 0 = 0 ∧ indexEndpointBump c b v c = v ∧
      indexEndpointBump c b v b = 0 := by
  simp [indexEndpointBump, ne_of_gt hc, ne_of_gt (sub_pos.mpr hcb)]

theorem MatrixJacobiSolution.conjugateIndexAction_eq {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (hsym : ∀ s, (R s).IsSymm)
    (w : Fin 3 → ℝ) {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hJ : d.J c *ᵥ w = 0) (ε : ℝ) :
    conjugateIndexAction d w c b ε =
      ε ^ 2 * (∫ s in (0 : ℝ)..b, normalIndexDensity (R s)
        (indexEndpointBump c b (d.V c *ᵥ w) s)
        (indexEndpointBumpDerivative c b (d.V c *ᵥ w) s)) -
      2 * ε * ((d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w)) := by
  let h := indexEndpointBump c b (d.V c *ᵥ w)
  let k := indexEndpointBumpDerivative c b (d.V c *ᵥ w)
  have hh := indexEndpointBump_continuous c b (d.V c *ᵥ w)
  have hk := indexEndpointBumpDerivative_continuous c b (d.V c *ᵥ w)
  have hi := continuous_normalIndexDensity hR hh hk
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_position_hasDerivAt w s).continuousAt
  have hz : Continuous (fun s => d.V s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_velocity_hasDerivAt w s).continuousAt
  have hvalues := indexEndpointBump_values hc hcb (d.V c *ᵥ w)
  have hcross := d.index_pairing_integral hR w h k
    (indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w)) hk 0 c
  change (∫ s in (0 : ℝ)..c, normalIndexPairing (R s) (d.J s *ᵥ w)
    (d.V s *ᵥ w) (h s) (k s)) = _ at hcross
  have hcross' : (∫ s in (0 : ℝ)..c, normalIndexPairing (R s) (d.J s *ᵥ w)
      (d.V s *ᵥ w) (h s) (k s)) = (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) := by
    simpa only [h, hvalues.1, hvalues.2.1, dotProduct_zero, sub_zero] using hcross
  change (∫ s in (0 : ℝ)..c, normalIndexDensity (R s) (d.J s *ᵥ w - ε • h s)
      (d.V s *ᵥ w - ε • k s)) +
    (∫ s in c..b, normalIndexDensity (R s) (-(ε • h s)) (-(ε • k s))) = _
  rw [index_integral_sub_smul hR hsym hy hz hh hk,
    d.index_integral_zero_of_kernel hR w c hJ, hcross']
  have hright : (∫ s in c..b, normalIndexDensity (R s) (-(ε • h s)) (-(ε • k s))) =
      ε ^ 2 * (∫ s in c..b, normalIndexDensity (R s) (h s) (k s)) := by
    simp_rw [← neg_smul, normalIndexDensity_smul, neg_sq]
    exact intervalIntegral.integral_const_mul _ _
  rw [hright, ← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable 0 c) (hi.intervalIntegrable c b)]
  ring

theorem exists_positive_quadratic_negative {n : ℝ} (hn : 0 < n) (D : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 * D - 2 * ε * n < 0 := by
  let ε := n / (|D| + 1)
  have hd : 0 < |D| + 1 := by positivity
  have he : 0 < ε := div_pos hn hd
  have heq : ε * (|D| + 1) = n := by
    dsimp [ε]
    exact div_mul_cancel₀ n (ne_of_gt hd)
  have hbound : ε * D ≤ ε * |D| := mul_le_mul_of_nonneg_left (le_abs_self D) he.le
  have hsmall : ε * D < n := by nlinarith
  refine ⟨ε, he, ?_⟩
  nlinarith [mul_lt_mul_of_pos_left hsmall he, mul_pos he hn]

theorem MatrixJacobiSolution.exists_negative_conjugate_index {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (hsym : ∀ s, (R s).IsSymm)
    (w : Fin 3 → ℝ) {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hJ : d.J c *ᵥ w = 0) (hV : d.V c *ᵥ w ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ conjugateIndexAction d w c b ε < 0 := by
  have hn : 0 < (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) := by
    have hnonneg : 0 ≤ (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg ((d.V c *ᵥ w) i))
    have hne : (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) ≠ 0 := by
      intro hzero
      exact hV (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨ε, hε, hneg⟩ := exists_positive_quadratic_negative hn
    (∫ s in (0 : ℝ)..b, normalIndexDensity (R s)
      (indexEndpointBump c b (d.V c *ᵥ w) s)
      (indexEndpointBumpDerivative c b (d.V c *ᵥ w) s))
  refine ⟨ε, hε, ?_⟩
  rwa [d.conjugateIndexAction_eq hR hsym w hc hcb hJ]

end
end PositiveEinsteinFour.Jacobi

end


section

/-! Globally C1 extensions of the two smooth pieces of the conjugate-point
test field.  The extensions agree at the conjugate point, so a chart partition
can treat each side separately without differentiating at the corner. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

theorem conjugateBranches_endpoints {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    conjugateLeftField d w c b ε 0 = 0 ∧ conjugateRightField d w c b ε b = 0 := by
  simp [conjugateLeftField, conjugateRightField, indexEndpointBump, d.initial_position]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Normal fields along the actual parallel-frame flow.  Their ordinary
coordinate derivatives and their index densities are derived from the
constructed horizontal ODE, rather than supplied as extra field identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem normalChartField_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : HasDerivAt a (b t) t) :
    HasDerivAt (normalChartField g c e a) (normalChartFieldRate g c e a b t) t := by
  have hE := normalChartFrame_hasDerivAt g c e t hc
  have hentries (i j : Fin 4) : HasDerivAt
      (fun s => frameChartMatrix g c (parallelFrameFlowMap g 0 s e) i j)
      (-(jacobiConnection
        (fun k => connectionMatrix g c k (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
        (fun k => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) k 0) *
          frameChartMatrix g c (parallelFrameFlowMap g 0 t e)) i j) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j
  rw [normalChartFieldRate_eq]
  exact hasDerivAt_parallel_frameVector _ _ _ _ t hentries
    (hasDerivAt_normal_lift a (b t) t ha)

theorem normalChartField_toLp_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : HasDerivAt a (b t) t) :
    HasDerivAt (fun s => WithLp.toLp 2 (normalChartField g c e a s))
      (WithLp.toLp 2 (normalChartFieldRate g c e a b t)) t := by
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt t (normalChartField_hasDerivAt g c e a b t hc ha)
  simpa only [Function.comp_def] using! h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth approximations to radial distance have differential bounded by
the actual metric speed after applying the exponential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular
open scoped Manifold ContDiff _root_.Topology InnerProductSpace

noncomputable section

def smoothRadialNorm (ε : ℝ) (v : FourSpace) : ℝ := Real.sqrt (‖v‖ ^ 2 + ε ^ 2)

theorem smoothRadialNorm_pos (ε : ℝ) (hε : 0 < ε) (v : FourSpace) :
    0 < smoothRadialNorm ε v := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem smoothRadialNorm_bounds (ε : ℝ) (hε : 0 < ε) (v : FourSpace) :
    ‖v‖ ≤ smoothRadialNorm ε v ∧ smoothRadialNorm ε v ≤ ‖v‖ + ε := by
  have hsq : smoothRadialNorm ε v ^ 2 = ‖v‖ ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hp := (smoothRadialNorm_pos ε hε v).le
  constructor <;> nlinarith [norm_nonneg v, sq_nonneg ε]

theorem smoothRadialNorm_hasFDerivAt (ε : ℝ) (hε : 0 < ε) (v : FourSpace) :
    HasFDerivAt (smoothRadialNorm ε)
      ((smoothRadialNorm ε v)⁻¹ • innerSL ℝ v) v := by
  have hpos : 0 < ‖v‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have h := ((hasStrictFDerivAt_norm_sq v).hasFDerivAt.add_const (ε ^ 2)).sqrt hpos.ne'
  have hcoef : (1 / (2 * Real.sqrt (‖v‖ ^ 2 + ε ^ 2))) * 2 =
      (Real.sqrt (‖v‖ ^ 2 + ε ^ 2))⁻¹ := by
    field_simp
  have hD : (1 / (2 * Real.sqrt (‖v‖ ^ 2 + ε ^ 2))) • (2 • innerSL ℝ v) =
      (Real.sqrt (‖v‖ ^ 2 + ε ^ 2))⁻¹ • innerSL ℝ v := by
    ext w
    simp only [two_smul, _root_.smul_apply, _root_.add_apply,
      smul_eq_mul]
    change (1 / (2 * Real.sqrt (‖v‖ ^ 2 + ε ^ 2))) * (⟪v, w⟫_ℝ + ⟪v, w⟫_ℝ) =
      (Real.sqrt (‖v‖ ^ 2 + ε ^ 2))⁻¹ * ⟪v, w⟫_ℝ
    rw [← two_mul, ← mul_assoc, hcoef]
  rw [hD] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Endpoint data and a common chart neighborhood for an actual normal
variation of one geodesic segment.  All endpoint jets come from the same
intrinsic affine curve, even when adjacent segments use different charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def normalEndpointJetData (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    NormalEndpointJetData g e c a := Classical.choice (by
  obtain ⟨δ, hδ, A, A', A'', hA, hA', hA'', hzero, hfirst, hsecond, hder, hreal⟩ :=
    exists_normalEndpointJets g e c hc a
  exact ⟨⟨δ, hδ, A, A', A'', hA, hA', hA'', hzero, hfirst, hsecond, hder,
    fun ε hε => (hreal ε hε).1, fun ε hε => (hreal ε hε).2⟩⟩)

variable [T3Space M] [CompactSpace M]

def normalSegmentPosition (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε t : ℝ) : FourSpace :=
  endpointCorrectedPosition (fun s => chartAt FourSpace c (frameGeodesic g 0 e s))
    (fun s => WithLp.toLp 2 (normalChartField g c e N s)) A B a b ε t

def normalSegmentCurve (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε t : ℝ) : M :=
  (chartAt FourSpace c).symm (normalSegmentPosition g e c N A B a b ε t)

/-- A single positive parameter radius keeps the entire corrected segment
inside its chart and inside both endpoint-jet neighborhoods. -/
theorem normalSegment_common_radius (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ContinuousOn N (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    ∃ δ > 0, δ ≤ A.radius ∧ δ ≤ B.radius ∧ ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈
        (chartAt FourSpace c).target := by
  have hx : ContinuousOn (fun t => chartAt FourSpace c (frameGeodesic g 0 e t)) (Icc a b) :=
    ((frameGeodesic_chart_contDiffOn g 0 e c).mono hc).continuousOn
  have hy : ContinuousOn (fun t => WithLp.toLp 2 (normalChartField g c e N t)) (Icc a b) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (normalChartField_continuousOn g c e N (Icc a b) hc hN)
  obtain ⟨r, hr, hinside⟩ := endpointCorrectedPosition_inside_on
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (fun t => WithLp.toLp 2 (normalChartField g c e N t)) A.position B.position hab.le
    hx hy A.position_continuous B.position_continuous A.position_zero B.position_zero
    (chartAt FourSpace c).target (chartAt FourSpace c).open_target
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  refine ⟨min r (min A.radius B.radius), lt_min hr (lt_min A.radius_pos B.radius_pos),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro ε hε t ht
  apply hinside ε ?_ t ht
  constructor <;> linarith [hε.1, hε.2, min_le_left r (min A.radius B.radius)]

theorem normalSegmentCurve_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b t : ℝ}
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (ht : frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source) :
    normalSegmentCurve g e c N A.position B.position a b 0 t = frameGeodesic g 0 e t := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
  exact (chartAt FourSpace c).left_inv ht

theorem normalSegmentCurve_endpoints (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b ε : ℝ} (hab : a < b)
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : ε ∈ Icc (-A.radius) A.radius) (hB : ε ∈ Icc (-B.radius) B.radius) :
    normalSegmentCurve g e c N A.position B.position a b ε a =
      normalEndpointCurve g (parallelFrameFlowMap g 0 a e) (N a) ε ∧
    normalSegmentCurve g e c N A.position B.position a b ε b =
      normalEndpointCurve g (parallelFrameFlowMap g 0 b e) (N b) ε := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_left _ _ _ _ _ _ _ hab.ne,
    endpointCorrectedPosition_right _ _ _ _ _ _ _ hab.ne]
  exact ⟨A.realizes ε hA, B.realizes ε hB⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The corrected normal segment has the actual Riemannian kinetic energy.
Its initial raw jets are the prescribed normal field and its derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def normalSegmentVelocity (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε t : ℝ) : FourSpace :=
  endpointCorrectedVelocity (fun s => chartAt FourSpace c (frameGeodesic g 0 e s))
    (fun s => WithLp.toLp 2 (normalChartField g c e N s))
    (fun s => WithLp.toLp 2 (geodesicChartVelocity g c e s))
    (fun s => WithLp.toLp 2 (normalChartFieldRate g c e N P s)) A B a b ε t

def normalSegmentEnergy (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε : ℝ) : ℝ :=
  ∫ t in a..b, chartEnergyDensity g c (normalSegmentPosition g e c N A B a b ε t)
    (WithLp.ofLp (normalSegmentVelocity g e c N P A B a b ε t))

theorem normalSegmentCurve_contMDiffOn (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) {a b ε : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A B a b ε t ∈ (chartAt FourSpace c).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (normalSegmentCurve g e c N A B a b ε) (Icc a b) := by
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  apply endpointCorrected_curve_contMDiffOn c _ _ _ _ A B hab ε
  · intro t ht
    exact geodesicChartPosition_hasDerivAt g c e t (hc t ht)
  · intro t ht
    exact normalChartField_toLp_hasDerivAt g c e N P t (hc t ht) (hN t ht)
  · exact (PiLp.continuous_toLp 2 _).comp_continuousOn
      (geodesicChartVelocity_continuousOn g c e (Icc a b) hc)
  · exact (PiLp.continuous_toLp 2 _).comp_continuousOn
      (normalChartFieldRate_continuousOn g c e N P (Icc a b) hc hNc hP)
  · exact hz

theorem normalSegmentEnergy_eq_actual (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) {a b ε : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t)
    (hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A B a b ε t ∈ (chartAt FourSpace c).target) :
    normalSegmentEnergy g e c N P A B a b ε =
      metricCurveEnergy g (normalSegmentCurve g e c N A B a b ε) a b := by
  symm
  apply endpointCorrected_actual_energy g c _ _ _ _ A B hab ε
  · intro t ht
    exact geodesicChartPosition_hasDerivAt g c e t (hc t ht)
  · intro t ht
    exact normalChartField_toLp_hasDerivAt g c e N P t (hc t ht) (hN t ht)
  · exact hz

theorem normalSegmentEnergy_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t)
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    normalSegmentEnergy g e c N P A.position B.position a b 0 = (b - a) / 2 := by
  have href : EqOn (normalSegmentCurve g e c N A.position B.position a b 0)
      (frameGeodesic g 0 e) (Icc a b) :=
    fun t ht => normalSegmentCurve_zero g e c N A B (hc t ht)
  have hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b 0 t ∈
        (chartAt FourSpace c).target := by
    intro t ht
    unfold normalSegmentPosition
    rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
    exact (chartAt FourSpace c).map_source (hc t ht)
  rw [normalSegmentEnergy_eq_actual g e c N P A.position B.position hab hc hN hz,
    metricCurveEnergy_congr g hab.le href, frameGeodesic_energy g 0 e hab]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Time reversal of the actual complete geodesic, using the oriented
frame rotation by minus the identity in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem parallelFrameCurveAt_antipode (g : SmoothMetric M) (γ : ℝ → FrameBundle g)
    (k : Fin 4) (t : ℝ) (h : ParallelFrameCurveAt g γ k (-t)) :
    ParallelFrameCurveAt g (fun s => frameAntipode g (γ (-s))) k t := by
  constructor
  · have hd := h.velocity.scomp t (hasDerivAt_neg t)
    change HasDerivAt (fun s => chartAt FourSpace (γ (-t)).base (γ (-s)).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g (γ (-t)).base
        (frameAntipode g (γ (-t))) r k)) t
    rw [frameAntipode_chart]
    simpa only [Matrix.neg_apply, neg_one_smul, PiLp.neg_apply, Function.comp_apply] using! hd
  · intro i j
    have hd := ((h.parallel i j).comp t (hasDerivAt_neg t)).neg
    change HasDerivAt (fun s => frameChartMatrix g (γ (-t)).base
      (frameAntipode g (γ (-s))) i j)
      (-((∑ r, frameChartMatrix g (γ (-t)).base (frameAntipode g (γ (-t))) r k •
        connectionMatrix g (γ (-t)).base r (chartAt FourSpace (γ (-t)).base (γ (-t)).base)) *
        frameChartMatrix g (γ (-t)).base (frameAntipode g (γ (-t)))) i j) t
    simp only [frameAntipode_chart, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib,
      neg_mul_neg]
    simpa only [Function.comp_apply, Pi.neg_apply, mul_neg_one, neg_neg] using! hd

variable [T3Space M] [CompactSpace M]

theorem parallelFrameFlowMap_antipode (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) (e : FrameBundle g) :
    frameAntipode g (parallelFrameFlowMap g k (-t) e) =
      parallelFrameFlowMap g k t (frameAntipode g e) := by
  let γ := fun s => frameAntipode g (parallelFrameFlowMap g k (-s) e)
  let η := fun s => parallelFrameFlowMap g k s (frameAntipode g e)
  have hc : Continuous γ := (continuous_frameRotate g).comp
    (((parallelFrameFlowMap_curve_continuous g k e).comp continuous_neg).prodMk continuous_const)
  have hd : Continuous η := parallelFrameFlowMap_curve_continuous g k _
  have hγ (s : ℝ) : ParallelFrameCurveAt g γ k s :=
    parallelFrameCurveAt_antipode g _ k s (parallelFrameFlowMap_primitive g k e (-s))
  have hη (s : ℝ) : ParallelFrameCurveAt g η k s := parallelFrameFlowMap_primitive g k _ s
  have hz : γ 0 = η 0 := by simp only [γ, η, neg_zero, parallelFrameFlowMap_zero]
  exact congrFun (intrinsic_parallelFrame_unique_global g γ η k hc hd hγ hη hz) t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual second parameter derivative of the corrected normal-segment energy.
The coordinate jets are supplied by the common intrinsic endpoint curves. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalSegmentEnergy_secondDeriv (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      (∫ t in a..b, chartEnergySecondDensity g c
        (chartAt FourSpace c (frameGeodesic g 0 e t))
        (normalChartField g c e N t) (geodesicChartVelocity g c e t)
        (normalChartFieldRate g c e N P t)
        (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) 0 := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have h := endpointCorrected_energy_secondDerivOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hδ hab.le
    hx hy hv hw A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn
    (fun ε hε => (A.derivative ε (ha ε hε)).1)
    (fun ε hε => (B.derivative ε (hb ε hε)).1)
    (fun ε hε => (A.derivative ε (ha ε hε)).2)
    (fun ε hε => (B.derivative ε (hb ε hε)).2) hz
  have hA0 : A.position 0 = x a := A.position_zero
  have hB0 : B.position 0 = x b := B.position_zero
  have hA1 : A.first 0 = y a := A.first_zero
  have hB1 : B.first 0 = y b := B.first_zero
  have hX (t : ℝ) := endpointCorrectedPosition_zero x y A.position B.position a b t hA0 hB0
  have hY (t : ℝ) := endpointCorrectedParameter_zero y A.first B.first a b t hA1 hB1
  have hV (t : ℝ) := endpointCorrectedVelocity_zero x y v w A.position B.position a b t hA0 hB0
  have hW (t : ℝ) := endpointCorrectedMixed_zero y w A.first B.first a b t hA1 hB1
  simpa only [hX, hY, hV, hW, x, y, v, w, WithLp.ofLp_toLp,
    normalSegmentEnergy, normalSegmentPosition, normalSegmentVelocity] using! h

theorem normalSegmentEnergy_first_differentiable (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (normalSegmentEnergy g e c N P A.position B.position a b) ε := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have hcont := endpointCorrected_energy_continuousOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hx hy hv hw
    A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn hz
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)] with ε hε
  apply HasDerivAt.differentiableAt
  apply intervalIntegral_hasDerivAt_rectangle
    (fun ε t => chartEnergyDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t)))
    (fun ε t => chartEnergyFirstDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b ε t))
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t))
      (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b ε t)))
    hab.le hε hcont.1 hcont.2.1
  intro s hs t ht
  apply chartEnergy_firstJet_hasDerivAt
  · exact hz s ⟨hs.1.le, hs.2.le⟩ t ht
  · simpa only [WithLp.toLp_ofLp] using endpointCorrectedPosition_parameter x y
      A.position B.position A.first B.first a b s t
      (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt s (endpointCorrectedVelocity_parameter x y v w
        A.position B.position A.first B.first a b s t
        (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Nonnegativity of the normal index on a finite chart partition of an
actual minimizing geodesic.  The competitor curves and their endpoint jets
are constructed, rather than assumed as a second-variation input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem normalEndpointCurve_zero (g : SmoothMetric M) (e : FrameBundle g) (ε : ℝ) :
    normalEndpointCurve g e 0 ε = e.base := by
  have hz : (Fin.cons (0 : ℝ) (0 : Fin 3 → ℝ) : Fin 4 → ℝ) = 0 := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [normalEndpointCurve, normalEndpointDirection, hz, Matrix.mulVec_zero,
    WithLp.toLp_zero, endpointChartLine, smul_zero, add_zero]
  exact (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kernel of the actual smooth scalar Laplacian.  The proof uses
the actual parallel-flow Green formula, full support of base volume, and
constancy along the complete geodesics.  No elliptic kernel theorem is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The squared norm of the scalar differential on the base. -/
def scalarDirichletDensity (g : SmoothMetric M) (a : M → ℝ) (c : M) : ℝ :=
  frameTensorSquareNorm (frameTensor (canonicalFrame g c).matrix
    (covariantDerivative g c (scalarCoordinates a c) (chartAt FourSpace c c)))

theorem scalarDirichletDensity_eq_frame (g : SmoothMetric M) (a : M → ℝ)
    (e : FrameBundle g) :
    scalarDirichletDensity g a e.base = ∑ i, scalarGradient g a e i ^ 2 := by
  unfold scalarDirichletDensity
  rw [frameTensor_norm_same_base (canonicalFrame g e.base) e.frame,
    scalar_tensor_square]
  rfl

theorem scalarDirichletDensity_nonneg (g : SmoothMetric M) (a : M → ℝ) (c : M) :
    0 ≤ scalarDirichletDensity g a c := by
  rw [scalarDirichletDensity_eq_frame g a (⟨c, canonicalFrame g c⟩ : FrameBundle g)]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

variable [T3Space M] [CompactSpace M]

theorem scalarDirichletDensity_continuous (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) : Continuous (scalarDirichletDensity g a) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  change Continuous (fun e : FrameBundle g => scalarDirichletDensity g a e.base)
  simp_rw [scalarDirichletDensity_eq_frame]
  exact continuous_finsetSum _ (fun i _ => (actual_scalarGradient_continuous g ha i).pow 2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric Jacobian formula in every initial direction. An oriented
rotation of the initial frame contributes determinant one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem orientedEuclidean_det (Q : OrientedOrthogonalFour) :
    LinearMap.det (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det (Matrix.toEuclideanLin Q.val) = 1
  rw [LinearMap.det_toLpLin 2]
  exact (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Translation along the actual parallel flow is controlled by the scalar
Dirichlet energy.  The bound survives closure of smooth first jets, so a weak
scalar with zero gradient is invariant under each parallel flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

section Generic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The `L²` isometry obtained by translating an actual scalar field along
one parallel flow. -/
def scalarFlowTranslation (d : ParallelMetricData g μ) (i : Fin 4) (t : ℝ) :
    ScalarL2 g μ →L[ℝ] ScalarL2 g μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ ((d.flow i).map t)
    ((d.flow i).preserves t)).toContinuousLinearMap

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalarFlowTranslation_norm (d : ParallelMetricData g μ) (i : Fin 4)
    (t : ℝ) (f : ScalarL2 g μ) : ‖scalarFlowTranslation d i t f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f ((d.flow i).preserves t)

def scalarTranslatedField (d : ParallelMetricData g μ) (i : Fin 4)
    (t : ℝ) (f : C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => f ((d.flow i).map t e), f.continuous.comp ((d.flow i).continuous_slice t)⟩

theorem scalarFlowTranslation_toLp (d : ParallelMetricData g μ)
    (i : Fin 4) (t : ℝ) (f : C(FrameBundle g, ℝ)) :
    scalarFlowTranslation d i t (ContinuousMap.toLp 2 μ ℝ f) =
      ContinuousMap.toLp 2 μ ℝ (scalarTranslatedField d i t f) := by
  apply Lp.ext
  have hcomp := ((d.flow i).preserves t).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 μ ℝ f) ((d.flow i).preserves t), hcomp,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (scalarTranslatedField d i t f)]
    with e h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

theorem smoothScalar_flow_translation_bound (d : ParallelMetricData g μ)
    (i : Fin 4) (hzero : ∀ e, (d.flow i).map 0 e = e)
    (a : SmoothScalar (M := M)) (t : ℝ) :
    ‖scalarFlowTranslation d i t (smoothScalarValueL2 g μ a) -
      smoothScalarValueL2 g μ a‖ ≤ |t| * ‖smoothScalarGradientL2 d i a‖ := by
  let F : ℝ → C(FrameBundle g, ℝ) := fun r =>
    scalarTranslatedField d i r (smoothScalarValue g a)
  let G : ℝ → C(FrameBundle g, ℝ) := fun r =>
    scalarTranslatedField d i r (smoothScalarGradient d i a)
  have hG : Continuous (fun p : ℝ × FrameBundle g => G p.1 p.2) :=
    (actual_scalarGradient_continuous g a.property i).comp (d.flow i).continuous
  have hd (r : ℝ) : HasDerivAt F (G r) r := by
    apply Averages.continuousField_hasDerivAt_of_joint hG
    intro s e
    exact actual_scalarValue_parallel_derivative g a.property
      (fun u => (d.flow i).map u e) s i (d.curve_continuous i e).continuousAt
      (d.parallelCurve i s e)
  let L : C(FrameBundle g, ℝ) →L[ℝ] ScalarL2 g μ := ContinuousMap.toLp 2 μ ℝ
  have hdL (r : ℝ) : HasDerivAt (fun s => L (F s)) (L (G r)) r :=
    L.hasFDerivAt.comp_hasDerivAt r (hd r)
  have hn (r : ℝ) : ‖L (G r)‖ = ‖smoothScalarGradientL2 d i a‖ := by
    rw [show L (G r) = scalarFlowTranslation d i r (smoothScalarGradientL2 d i a) from
      (scalarFlowTranslation_toLp d i r (smoothScalarGradient d i a)).symm]
    exact scalarFlowTranslation_norm d i r _
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun r _ => (hdL r).hasDerivWithinAt)
    (fun r _ => (hn r).le) convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  have hF0 : F 0 = smoothScalarValue g a := by
    ext e
    change a.val ((d.flow i).map 0 e).base = a.val e.base
    rw [hzero]
  have hFt : L (F t) = scalarFlowTranslation d i t (smoothScalarValueL2 g μ a) :=
    (scalarFlowTranslation_toLp d i t (smoothScalarValue g a)).symm
  rw [hF0, hFt] at h
  simpa only [L, smoothScalarValueL2, LinearMap.comp_apply, sub_zero,
    Real.norm_eq_abs, mul_comm] using! h

end Generic

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The L² translation bound as a scalar oscillation integral, averaged over
the actual spherical directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff BigOperators ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem smoothScalar_flow_oscillation_bound (d : ParallelMetricData g μ)
    (i : Fin 4) (hzero : ∀ e, (d.flow i).map 0 e = e)
    (a : SmoothScalar (M := M)) (t : ℝ) :
    (∫⁻ e, ENNReal.ofReal ((a.val ((d.flow i).map t e).base - a.val e.base) ^ 2) ∂μ) ≤
      ENNReal.ofReal (t ^ 2 * ‖smoothScalarGradientL2 d i a‖ ^ 2) := by
  let F := scalarTranslatedField d i t (smoothScalarValue g a) - smoothScalarValue g a
  have hi : Integrable (fun e => F e ^ 2) μ :=
    (F.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫⁻ e, ENNReal.ofReal (F e ^ 2) ∂μ) =
      ENNReal.ofReal (‖ContinuousMap.toLp 2 μ ℝ F‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun e => sq_nonneg (F e)))]
    congr 1
    rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards [] with e
    simp only [conj_trivial, pow_two]
  change (∫⁻ e, ENNReal.ofReal (F e ^ 2) ∂μ) ≤ _
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have h := smoothScalar_flow_translation_bound d i hzero a t
  have hF : ContinuousMap.toLp 2 μ ℝ F =
      scalarFlowTranslation d i t (smoothScalarValueL2 g μ a) - smoothScalarValueL2 g μ a := by
    dsimp only [F]
    rw [map_sub, ← scalarFlowTranslation_toLp]
    rfl
  rw [hF]
  calc
    _ ≤ (|t| * ‖smoothScalarGradientL2 d i a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mpr h
    _ = _ := by rw [mul_pow, sq_abs]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarOscillation_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def scalarGeodesicOscillation (g : SmoothMetric M) (a : SmoothScalar (M := M))
    (t : ℝ) (e : FrameBundle g) : ℝ≥0∞ :=
  ENNReal.ofReal ((a.val (parallelFrameFlowMap g 0 t e).base - a.val e.base) ^ 2)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarGeodesicOscillation_joint_continuous (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) :
    Continuous (fun p : ℝ × FrameBundle g => scalarGeodesicOscillation g a p.1 p.2) :=
  ENNReal.continuous_ofReal.comp
    ((((a.property.continuous.comp (continuous_frameBase g)).comp
      (parallelFrameFlowMap_continuous g 0)).sub
        ((a.property.continuous.comp (continuous_frameBase g)).comp continuous_snd)).pow 2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global scalar pair oscillations are bounded by radial flow oscillations.
The measure comparison and all curves here are those of the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def scalarRadialOscillation (g : SmoothMetric M) (a : SmoothScalar (M := M))
    (e : FrameBundle g) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) Real.pi, scalarGeodesicOscillation g a r e

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarRadialOscillation_measurable (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) : Measurable (scalarRadialOscillation g a) :=
  ((scalarGeodesicOscillation_joint_continuous g a).measurable.comp
    measurable_swap).lintegral_prod_right'

theorem scalarRadialOscillation_integral (g : SmoothMetric M)
    (o : FrameOrientation g) (a : SmoothScalar (M := M)) :
    (∫⁻ e, scalarRadialOscillation g a e ∂canonicalFrameMeasure g o) =
      ∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
        scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o :=
  lintegral_lintegral_swap
    ((scalarGeodesicOscillation_joint_continuous g a).measurable.comp measurable_swap).aemeasurable

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the flow translation estimate over the bounded
radial interval gives a global pair-oscillation energy estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarPairEnergy_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalize the geometric pair estimate and express its left side as
the variance of an actual scalar function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance scalarNormalizedPair_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def scalarPairConstant (g : SmoothMetric M) (C : ℝ) : ℝ≥0∞ :=
  (volumeMeasure g univ)⁻¹ * (riemannianChartFactor * polarAngularMass * ENNReal.ofReal C) *
    ENNReal.ofReal (Real.pi ^ 3)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem scalarPairConstant_ne_top (g : SmoothMetric M) (C : ℝ) :
    scalarPairConstant g C ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (actual_finitePositiveVolume g).positive.ne'
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) polarAngularMass_ne_top)
        ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

end
end PositiveEinsteinFour.Geometry
end


section

/-! The geometric pair estimate gives an actual mean-zero Poincaré
inequality for smooth scalars. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance scalarSmoothPoincare_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothScalar_value_norm_sq (g : SmoothMetric M) (o : FrameOrientation g)
    (a : SmoothScalar (M := M)) :
    ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 =
      ∫ e, (a.val e.base) ^ 2 ∂canonicalFrameMeasure g o := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothScalarValue g a))
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothScalarValue g a)) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with e
  change a.val e.base * a.val e.base = (a.val e.base) ^ 2
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unconditional weak Poisson solvability for the actual metric.  The
Poincaré constant comes from the exponential-map pair estimate.  The value
of the solution is a scalar on the base manifold, and its equation holds
against every element of the actual first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem smoothScalar_centered_orthogonal_one (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarValueL2 g μ (smoothScalarSubtractMean (μ := μ) a))
      (scalarL2One g μ) = 0 := by
  rw [real_inner_comm]
  change scalarH1Mean d (smoothScalarToH1 d (smoothScalarSubtractMean (μ := μ) a)) = 0
  rw [scalarH1Mean_smooth]
  exact smoothScalarSubtractMean_mean_zero d a

end General

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth representative of a weak scalar Poisson solution satisfies the
pointwise geometric Poisson equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def smoothScalarLaplacian (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    SmoothScalar (M := M) :=
  ⟨scalarLaplacianBase g a, scalarLaplacianBase_smooth g a.property⟩

theorem smoothScalarLaplacian_valueL2 (g : SmoothMetric M)
    (μ : Measure (FrameBundle g)) [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (a : SmoothScalar (M := M)) :
    smoothScalarValueL2 g μ (smoothScalarLaplacian g a) =
      smoothScalarLaplacianL2 (μ := μ) a := by
  change ContinuousMap.toLp 2 μ ℝ (smoothScalarValue g (smoothScalarLaplacian g a)) =
    ContinuousMap.toLp 2 μ ℝ (smoothScalarLaplacianField g a)
  congr 1
  ext e
  exact (scalarLaplacian_eq_base g a e).symm

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarStrong_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarStrong_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The distributional Poisson equation in metric chart measure.
Its coordinate density is derived from Riemannian volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function Filter
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I4 ∞ M] [MeasurableSpace M] [BorelSpace M] in
theorem scalarChartLift_tsupport (c : M) (ψ : FourSpace → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    tsupport (scalarChartLift c ψ) ⊆ (chartAt FourSpace c).source := by
  have hK : IsCompact ((chartAt FourSpace c).symm '' tsupport ψ) :=
    hc.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hs)
  apply (closure_minimal (scalarChartLift_support c ψ) hK.isClosed).trans
  rintro _ ⟨z, hz, rfl⟩
  exact (chartAt FourSpace c).map_target (hs hz)

section Compact

variable [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
  [PreconnectedSpace M]

local instance scalarChartIntegral_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end Compact
end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar energy controls coordinate derivatives in a chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarGradient_chart (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : ChartTarget c) (i : Fin 4) :
    scalarGradient g a (chartGramSection g c 1 (by simp) z) i =
      ∑ j, chartGramMatrix g c 1 z j i *
        partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) j z := by
  have hc := iteratedScalarDerivative_transition g ha c ((chartAt FourSpace c).symm z)
    1 z z.property (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  have h : frameTensor (chartGramMatrix g c 1 z)
      (iteratedScalarDerivative g a c 1 z) ![i] =
      scalarGradient g a (chartGramSection g c 1 (by simp) z) i := by
    rw [hc, ← frameTensor_mul]
    rfl
  rw [← h]
  change frameTensor (chartGramMatrix g c 1 z) (iteratedScalarDerivative g a c 1 z)
    (Fin.cons i (fun k : Fin 0 => Fin.elim0 k)) = _
  rw [frameTensor_cons]
  apply Finset.sum_congr rfl
  intro j _
  rw [frameTensor_zero]
  congr 1
  exact scalarCoordinate_gradient g a c z j

theorem scalar_covector_bound (E G : Mat4)
    (hE : IsUnit E.det) (hG : Eᵀ * G * E = 1)
    (p : Fin 4 → ℝ) (i : Fin 4) :
    p i ^ 2 ≤ G i i * ∑ j, (∑ k, E k j * p k) ^ 2 := by
  let H := E⁻¹
  let q := Eᵀ *ᵥ p
  have hp : Hᵀ *ᵥ q = p := by
    dsimp only [H, q]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv E hE, Matrix.transpose_one, Matrix.one_mulVec]
  have hmetric : Hᵀ * H = G := by
    have h := congrArg (fun B : Mat4 => Hᵀ * B * H) hG
    have hEH : E * H = 1 := Matrix.mul_nonsing_inv E hE
    calc
      Hᵀ * H = Hᵀ * 1 * H := by simp
      _ = Hᵀ * (Eᵀ * G * E) * H := h.symm
      _ = (E * H)ᵀ * G * (E * H) := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = G := by rw [hEH, Matrix.transpose_one]; simp
  have hnorm : ∑ j, H j i ^ 2 = G i i := by
    have h := congrFun (congrFun hmetric i) i
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have hpi : (∑ j, H j i * q j) = p i := congrFun hp i
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => H j i) q
  rw [hpi, hnorm] at h
  exact h

theorem scalarCoordinate_gradient_sq_le (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : ChartTarget c) (i : Fin 4) :
    (partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z) ^ 2 ≤
      metricInChart g c z i i * scalarDirichletDensity g a ((chartAt FourSpace c).symm z) := by
  let E := chartGramMatrix g c 1 z
  have hE : IsUnit E.det := by
    apply isUnit_iff_ne_zero.mpr
    intro he
    have hn := congrArg Matrix.det (chartGramMatrix_normalizes g c 1 (by simp) z)
    rw [Matrix.det_one] at hn
    change (Eᵀ * metricInChart g c z * E).det = 1 at hn
    simp only [Matrix.det_mul, Matrix.det_transpose, he, zero_mul, mul_zero] at hn
    exact zero_ne_one hn
  have h := scalar_covector_bound E (metricInChart g c z) hE
    (chartGramMatrix_normalizes g c 1 (by simp) z)
    (fun j => partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) j z) i
  have henergy := scalarDirichletDensity_eq_frame g a (chartGramSection g c 1 (by simp) z)
  simp_rw [scalarGradient_chart g ha c z] at henergy
  change scalarDirichletDensity g a ((chartAt FourSpace c).symm z) = _ at henergy
  rwa [← henergy] at h

theorem scalarCoordinate_gradient_sq_le_on_compact (g : SmoothMetric M)
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : M → ℝ), ContMDiff I4 𝓘(ℝ, ℝ) ∞ a →
      ∀ z ∈ K, (partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z) ^ 2 ≤
        C * scalarDirichletDensity g a ((chartAt FourSpace c).symm z) := by
  have hG : ContinuousOn (fun z => metricInChart g c z i i) K :=
    fun z hz => (metricInChart_contDiffAt g c z (hKt hz) i i).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hG).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro a ha z hz
  have hbound : metricInChart g c z i i ≤ max C 0 := by
    calc
      _ ≤ ‖metricInChart g c z i i‖ := le_abs_self _
      _ ≤ C := hC _ ⟨z, hz, rfl⟩
      _ ≤ max C 0 := le_max_left _ _
  exact (scalarCoordinate_gradient_sq_le g ha c ⟨z, hKt hz⟩ i).trans
    (mul_le_mul_of_nonneg_right hbound (scalarDirichletDensity_nonneg g a _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic energy controls the local coordinate L² differential.
These estimates are uniform over the smooth scalars generating H¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartEnergy_frameCompact_r588f22_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartEnergy_baseProbability
def scalarEnergyRoot (g : SmoothMetric M) (a : SmoothScalar (M := M)) : C(M, ℝ) :=
  ⟨fun x => Real.sqrt (scalarDirichletDensity g a x),
    Real.continuous_sqrt.comp (scalarDirichletDensity_continuous g a.property)⟩

def scalarEnergyRootL2 (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarEnergyRoot g a)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalarCoordinate_gradient_abs_le (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (i : Fin 4) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ (a : M → ℝ), ContMDiff I4 𝓘(ℝ, ℝ) ∞ a →
      ∀ z ∈ K, (partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z) ^ 2 ≤
        A * scalarDirichletDensity g a ((chartAt FourSpace c).symm z))
    (a : SmoothScalar (M := M)) {z : FourSpace} (hz : z ∈ K) :
    |partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z| ≤
      Real.sqrt A * (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z) := by
  have h := hbound a a.property z hz
  have hsA := Real.sq_sqrt hA
  have hsD := Real.sq_sqrt (scalarDirichletDensity_nonneg g a ((chartAt FourSpace c).symm z))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hsA, hsD]
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate integration by parts only needs smoothness near the compact
test support. Thus the arbitrary values of an inverse chart outside its
target never enter the local weak derivative identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem scalar_local_product_integrable (f q : FourSpace → ℝ)
    (hq : Continuous q) (hc : HasCompactSupport q)
    (hf : ∀ z ∈ tsupport q, ContinuousAt f z) :
    Integrable (fun z => f z * q z) volume := by
  have ht : tsupport (fun z => f z * q z) ⊆ tsupport q :=
    tsupport_mul_subset_right
  have hp : Continuous (fun z => f z * q z) := by
    apply continuous_of_tsupport
    intro z hz
    exact (hf z (ht hz)).mul hq.continuousAt
  exact hp.integrable_of_hasCompactSupport hc.mul_left

theorem scalar_local_integration_by_parts (f ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hf : ∀ z ∈ tsupport ψ, ContDiffAt ℝ ∞ f z) (i : Fin 4) :
    (∫ z, f z * partialDeriv ψ i z) = -(∫ z, partialDeriv f i z * ψ z) := by
  have hDψ : ContDiff ℝ ∞ (fun z => partialDeriv ψ i z) :=
    (hψ.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
      (contDiff_const (c := coordinateVector i))
  have hsupport : tsupport (fun z => partialDeriv ψ i z) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ (coordinateVector i)
  have hcD : HasCompactSupport (fun z => partialDeriv ψ i z) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hDfψ : Integrable (fun z => partialDeriv f i z * ψ z) volume := by
    apply scalar_local_product_integrable _ ψ hψ.continuous hc
    intro z hz
    exact (((hf z hz).fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).continuousAt
  have hfDψ : Integrable (fun z => f z * partialDeriv ψ i z) volume :=
    scalar_local_product_integrable f _ hDψ.continuous hcD
      (fun z hz => (hf z (hsupport hz)).continuousAt)
  have hfψ : Integrable (fun z => f z * ψ z) volume :=
    scalar_local_product_integrable f ψ hψ.continuous hc
      (fun z hz => (hf z hz).continuousAt)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDfψ hfDψ hfψ
    (fun z hz => (hf z hz).differentiableAt (by simp))
    (fun z _ => hψ.differentiable (by simp) z)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_chart_integration_by_parts (a : SmoothScalar (M := M)) (c : M)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    (∫ z, a.val ((chartAt FourSpace c).symm z) * partialDeriv ψ i z) =
      -(∫ z, partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z * ψ z) :=
  scalar_local_integration_by_parts _ ψ hψ hc
    (fun z hz => scalarCoordinates_contDiffAt a.property c z (hs hz) (fun j => Fin.elim0 j)) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The extended coordinate derivative is the weak derivative of the actual
chart representative, verified against genuine compact smooth tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def scalarCompactTestL2 (K : Set FourSpace) (ψ : FourSpace → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : Lp ℝ 2 (volume.restrict K) :=
  ((hψ.memLp_of_hasCompactSupport hc).restrict K).toLp ψ

theorem scalarCompactTestL2_coe (K : Set FourSpace) (ψ : FourSpace → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    scalarCompactTestL2 K ψ hψ hc =ᵐ[volume.restrict K] ψ :=
  MemLp.coeFn_toLp _

def scalarCompactDerivativeL2 (K : Set FourSpace) (ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (i : Fin 4) :
    Lp ℝ 2 (volume.restrict K) :=
  scalarCompactTestL2 K (fun z => partialDeriv ψ i z)
    (((hψ.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
      (contDiff_const (c := coordinateVector i))).continuous)
    (hc.fderiv_apply ℝ (coordinateVector i))

theorem scalar_real_L2_pairing {K : Set FourSpace}
    (u v : Lp ℝ 2 (volume.restrict K)) :
    inner ℝ u v = ∫ z in K, u z * v z := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Multiplying a local L² representative by a compact cutoff gives a
genuine global L² function, independent of its values off the local set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

theorem scalarLocalL2_mul_integrable {K : Set FourSpace}
    (f : Lp ℝ 2 (volume.restrict K)) (q : FourSpace → ℝ)
    (hq : Continuous q) (hc : HasCompactSupport q) :
    Integrable (fun z => f z * q z) (volume.restrict K) :=
  (Lp.memLp f).integrable_mul ((hq.memLp_of_hasCompactSupport (p := 2) hc).restrict K)

end
end PositiveEinsteinFour.Geometry
end


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

/-! Real components of the actual complex distributional test pairing.
Only the compactly localized source must be smooth and integrable. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)

theorem scalarComplexSource_pairing_component (s : V → ℝ) (L : ℂ →L[ℝ] ℝ)
    (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : ∀ x ∈ tsupport (φ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) s x) (κ : ℝ) :
    L (∫ x, φ x * ((κ * s x : ℝ) : ℂ)) =
      κ * ∫ x, s x * L (φ x) := by
  let F := scalarLocalSourceSchwartz φ (fun x => ((κ * s x : ℝ) : ℂ)) hc
    (fun x hx => Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiffAt_const.mul (hs x hx)))
  have hi : Integrable (fun x => φ x * ((κ * s x : ℝ) : ℂ)) volume := F.integrable
  rw [← L.integral_comp_comm hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_comm (φ x), ← Complex.real_smul, L.map_smul]
  change (κ * s x) * L (φ x) = κ * (s x * L (φ x))
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The density-weighted unknown in the coordinate Poisson equation has
the same genuine local H¹ regularity as the intrinsic solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set TemperedDistribution
open scoped Manifold ContDiff _root_.Topology SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance weightedCoordinates_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Poisson equation tested against compact coordinate
functions, with the volume density absorbed into the same H1 solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

local instance weightedTests_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The same weighted H1 representative satisfies the actual geometric
equation after the invertible frozen-frame change of coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance rescaledTests_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Poisson equation tested against compact coordinate
functions, with the volume density absorbed into the same H1 solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

local instance weightedL2Tests_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The same weighted H1 representative satisfies the actual geometric
equation after the invertible frozen-frame change of coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance rescaledL2Tests_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L⁴ Sobolev representative is the same actual base function as its L² representative of the intrinsic first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_7
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance sobolevRepresentative_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance sobolevRepresentative_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Lp representatives and convergence in the subcritical range.
The inclusion uses the same almost-everywhere function; the convergence
statement combines small L² norm with a bounded L⁴ norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_13
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance subcriticalEmbedding_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance subcriticalEmbedding_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and the invertible affine rescaling
in the local smooth representative of the actual Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance unweighting_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The subcritical Sobolev operator on the Hilbert space whose squared
norm is the exact normalized energy in the manuscript. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance sobolevExtremal_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global smooth representatives of the actual intrinsic weak Poisson
solutions, obtained from the proved local coordinate regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance poissonRegularity_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance poissonRegularity_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Existence of an extremizer for the actual subcritical scalar Sobolev
operator, using compactness and the exact weighted Hilbert norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance variationalMinimum_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The absolute value of a subcritical extremizer belongs to the actual
energy space and has the same minimum energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance scalarNonnegative_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete shifted scalar resolvent supplies the local elliptic chain.
No regularity of its L2 input is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance resolventChain_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak minimum equation becomes the pointwise geometric Euler
equation once its actual representative is smooth and positive. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarSmoothEuler_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp subcritical scalar inequality from the actual normalized
minimum, once its positive smooth representative has been established. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

local instance scalarSubcriticalBound_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine scalar heat operator lifts boundedly to continuous functions
on the compact manifold. Closedness of its graph follows from the L2 identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ≥0) (ht : 0 < t)

local instance scalarHeatContinuous_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Riesz representatives of scalar heat evaluation. The columns are
actual L2 functions, with a uniform bound over the compact manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ≥0) (ht : 0 < t)

local instance scalarColumn_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Trace summability follows from the actual bounded scalar heat evaluation
map and integration of Bessel's inequality over normalized volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance scalarTrace_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

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

/-! The exterior/codifferential energy is a continuous nonnegative scalar
on the base. Its vanishing detects actual smooth harmonic forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormDeRhamDensity (o : FrameOrientation g) (u : M → TwoFormFour) (x : M) : ℝ :=
  twoFormDeRhamQuadratic (fun i j k =>
    twoFormFramedCovariantDerivative o u ⟨x,o.frame x⟩ ![i,j,k])

theorem twoFormDeRhamDensity_eq_frame (u : M → TwoFormFour) (e : FrameBundle g) :
    twoFormDeRhamDensity o u e.base = twoFormDeRhamQuadratic
      (fun i j k => twoFormFramedCovariantDerivative o u e ![i,j,k]) := by
  let P := (o.frame e.base).changeMatrix e.frame
  have hP : P * Pᵀ = 1 := mul_eq_one_comm.mp ((o.frame e.base).changeMatrix_orthogonal e.frame)
  have hd : twoFormFramedCovariantDerivative o u e =
      frameTensor P (twoFormFramedCovariantDerivative o u ⟨e.base,o.frame e.base⟩) := by
    unfold twoFormFramedCovariantDerivative
    rw [← frameTensor_mul, (o.frame e.base).mul_changeMatrix e.frame]
  rw [hd, twoFormDeRhamQuadratic_frame P hP]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the first covariant derivatives of actual
smooth one-forms, and their Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormGreenCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic codifferential density and the four-dimensional Hodge
splitting of the actual de Rham energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormCodiffDensity (u : smoothTwoForms o) : M → ℝ :=
  covariantFieldNormSq g (smoothTwoFormCodifferentialField u).val

theorem twoFormCodiffDensity_eq_frame (u : smoothTwoForms o) (e : FrameBundle g) :
    twoFormCodiffDensity u e.base =
      frameTensorSquareNorm (twoFormCodiffTensor (twoFormFramedCovariantDerivative o u.val e)) :=
  (covariantFieldNormSq_eq_frame (smoothTwoFormCodifferentialField u).val e).trans
    (congrArg frameTensorSquareNorm (smoothTwoFormCodifferentialField_framed u e))

theorem twoFormCodiffDensity_continuous (u : smoothTwoForms o) :
    Continuous (twoFormCodiffDensity u) :=
  (smoothTwoFormCodifferentialField u).property.continuous_normSq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differentiated codifferential and the actual exact dδ term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormDDelta (u : smoothTwoForms o) : smoothTwoForms o :=
  smoothOneFormExterior (smoothTwoFormCodifferentialField u)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth one-form divergence has mean zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormDivergenceCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential bilinear form and the global Hodge energy splitting. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_12
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_1
omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothTwoFormCodifferential_continuous (u : smoothTwoForms o) (k : Fin 4) :
    Continuous (fun e => smoothTwoFormCodifferential u e k) := by
  have h := (continuous_apply ![k]).comp
    ((smoothTwoFormCodifferentialField u).property.continuous_framed (g := g))
  exact h.congr (fun e => smoothTwoFormCodifferentialField_component u e k)

theorem twoFormCodiffProduct_integrable (u v : smoothTwoForms o) :
    Integrable (fun e => ∑ k, smoothTwoFormCodifferential u e k *
      smoothTwoFormCodifferential v e k) (canonicalFrameMeasure g o) :=
  integrable_finsetSum _ (fun k _ =>
    ((smoothTwoFormCodifferential_continuous u k).mul
      (smoothTwoFormCodifferential_continuous v k)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

def twoFormCodiffPairing (u v : smoothTwoForms o) : ℝ :=
  ∫ e, ∑ k, smoothTwoFormCodifferential u e k *
    smoothTwoFormCodifferential v e k ∂canonicalFrameMeasure g o

theorem twoFormCodiffPairing_comm (u v : smoothTwoForms o) :
    twoFormCodiffPairing u v = twoFormCodiffPairing v u := by
  unfold twoFormCodiffPairing
  apply integral_congr_ae
  filter_upwards [] with e
  simp only [mul_comm]

theorem twoFormCodiffPairing_add_left (u v w : smoothTwoForms o) :
    twoFormCodiffPairing (u + v) w = twoFormCodiffPairing u w + twoFormCodiffPairing v w := by
  unfold twoFormCodiffPairing
  simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  exact integral_add (twoFormCodiffProduct_integrable u w) (twoFormCodiffProduct_integrable v w)

theorem twoFormCodiffPairing_self (u : smoothTwoForms o) :
    twoFormCodiffPairing u u = ∫ x, twoFormCodiffDensity u x ∂normalizedVolume g := by
  have hi := (twoFormCodiffDensity_continuous u).integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  unfold twoFormCodiffPairing
  apply integral_congr_ae
  filter_upwards [] with e
  rw [twoFormCodiffDensity_eq_frame u e, twoFormCodiffTensor_squareNorm]
  apply Finset.sum_congr rfl
  intro k _
  change smoothTwoFormCodifferential u e k * smoothTwoFormCodifferential u e k =
    smoothTwoFormCodifferential u e k ^ 2
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive Ricci curvature kills the actual closed and coclosed
smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormBochnerCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem oneForm_valueSquare_integrable (u : smoothCovariantFields M 1) (j : Fin 4) :
    Integrable (fun e => covariantFieldFramed g u.val e ![j] ^ 2)
      (canonicalFrameMeasure g o) := by
  have hc : Continuous (fun e => covariantFieldFramed g u.val e ![j] ^ 2) :=
    ((continuous_apply _).comp (u.property.continuous_framed (g := g))).pow 2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem oneForm_secondPair_integrable (u : smoothCovariantFields M 1) (i j : Fin 4) :
    Integrable (fun e => covariantFieldFramed g u.val e ![j] *
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,i,j]) (canonicalFrameMeasure g o) := by
  have hDu : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
  have hDDu : CovariantFieldSmooth (covariantFieldDerivative g
      (covariantFieldDerivative g u.val)) := hDu.derivative
  have hc : Continuous (fun e => covariantFieldFramed g u.val e ![j] *
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,i,j]) :=
    ((continuous_apply _).comp (u.property.continuous_framed (g := g))).mul
      ((continuous_apply _).comp (hDDu.continuous_framed (g := g)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar differential and minus divergence are adjoint. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance scalarOneFormCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential squares to zero in degrees two and one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.codifferentialBaseProbability
theorem smoothScalar_eq_zero_of_square_integral (f : SmoothScalar (M := M))
    (hf : (∫ e, f.val e.base ^ 2 ∂canonicalFrameMeasure g o) = 0) : f = 0 := by
  let _ := normalizedVolume_isOpenPosMeasure g
  have hc : Continuous (fun x => f.val x ^ 2) := f.property.continuous.pow 2
  have hi := hc.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  have hb : (∫ x, f.val x ^ 2 ∂normalizedVolume g) = 0 :=
    (canonicalFrameMeasure_integral_base g o _ hi).symm.trans hf
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f.val x)) hi).mp hb
  have he : (fun x => f.val x ^ 2) = 0 := Measure.eq_of_ae_eq ha hc continuous_const
  apply Subtype.ext
  funext x
  exact sq_eq_zero_iff.mp (congrFun he x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The degree-one Hodge Laplacian is the actual dδ+δd operator.
Its symmetry and nonnegative energy follow from the geometric adjoints. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormHodgeLaplacian_apply (u : smoothCovariantFields M 1) :
    smoothOneFormHodgeLaplacian (o := o) u =
      smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) u) -
        smoothScalarDifferential g (smoothOneFormDivergence g u) := rfl

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance oneFormHodge_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def smoothOneFormHodgeEnergy (u v : smoothCovariantFields M 1) : ℝ :=
  smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) (smoothOneFormExterior (o := o) v) +
    ∫ x, oneFormDivergence g u x * oneFormDivergence g v x ∂normalizedVolume g

omit [CompactSpace M] [Nonempty M] in
theorem smoothOneFormHodgeEnergy_comm (u v : smoothCovariantFields M 1) :
    smoothOneFormHodgeEnergy (o := o) u v = smoothOneFormHodgeEnergy (o := o) v u := by
  unfold smoothOneFormHodgeEnergy
  rw [smoothTwoFormL2Inner_comm]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => mul_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative from actual scalar H1 to actual one-form L2.
The extension is made along the dense range of smooth first jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_13
def scalarFirstJetRangeInclusion (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    LinearMap.range (smoothScalarFirstJet d) →ₗᵢ[ℝ] scalarH1 d where
  toLinearMap :=
    { toFun := fun u => ⟨u.val, Submodule.le_topologicalClosure _ u.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' _ := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive Ricci curvature eliminates the kernel of the actual
degree-one Hodge Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormKernel_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The geometric Hodge Laplacian splits as dδ + *dδ*. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCodiffPairing_add_right (u v w : smoothTwoForms o) :
    twoFormCodiffPairing u (v + w) = twoFormCodiffPairing u v + twoFormCodiffPairing u w := by
  rw [twoFormCodiffPairing_comm, twoFormCodiffPairing_add_left,
    twoFormCodiffPairing_comm v u, twoFormCodiffPairing_comm w u]

theorem smoothTwoFormL2Inner_add_right (u v w : smoothTwoForms o) :
    smoothTwoFormL2Inner u (v + w) = smoothTwoFormL2Inner u v + smoothTwoFormL2Inner u w := by
  rw [smoothTwoFormL2Inner_comm, smoothTwoFormL2Inner_add,
    smoothTwoFormL2Inner_comm v u, smoothTwoFormL2Inner_comm w u]

theorem smoothTwoFormL2Inner_hodge_left (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormHodge o u) v =
      smoothTwoFormL2Inner u (smoothTwoFormHodge o v) := by
  have h := (smoothL2Hodge (o := o)).inner_map_map
    (u : SmoothL2TwoForm o) (smoothL2Hodge (v : SmoothL2TwoForm o))
  change smoothTwoFormL2Inner (smoothTwoFormHodge o u)
    (smoothTwoFormHodge o (smoothTwoFormHodge o v)) =
      smoothTwoFormL2Inner u (smoothTwoFormHodge o v) at h
  rw [smoothTwoFormHodge_involutive o v] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closedness is exactly vanishing of the Hodge-dual codifferential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormCodifferentialField_eq_zero_iff (u : smoothTwoForms o) :
    smoothTwoFormCodifferentialField u = 0 ↔ smoothTwoFormCodifferential u = 0 := by
  constructor
  · intro hu
    funext e k
    rw [← smoothTwoFormCodifferentialField_component, hu]
    simp [covariantFieldFramed_eq, frameTensor]
  · intro hu
    apply Subtype.ext
    apply covariantField_eq_of_framed (g := g)
    intro e
    funext a
    have ha : a = ![a 0] := by ext i; fin_cases i; rfl
    rw [ha, smoothTwoFormCodifferentialField_component, hu]
    simp [covariantFieldFramed_eq, frameTensor]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual infinite spectral kernel has the expected integrated
diagonal trace. Absolute convergence justifies both exchanges. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

def twoFormFiberTrace : (TwoFormFour →L[ℝ] TwoFormFour) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ TwoFormFour).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

theorem twoFormFiberTrace_apply (A : TwoFormFour →L[ℝ] TwoFormFour) :
    twoFormFiberTrace A = LinearMap.trace ℝ TwoFormFour A.toLinearMap := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic Hodge-signed diagonal trace of the actual heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

def twoFormFiberSignedTrace : (TwoFormFour →L[ℝ] TwoFormFour) →L[ℝ] ℝ :=
  twoFormFiberTrace.comp ((ContinuousLinearMap.compL ℝ TwoFormFour TwoFormFour TwoFormFour)
    twoFormHodge.toLinearIsometry.toContinuousLinearMap)

theorem twoFormFiberSignedTrace_rankOne (a b : TwoFormFour) :
    twoFormFiberSignedTrace (InnerProductSpace.rankOne ℝ a b) = inner ℝ b (twoFormHodge a) := by
  have he : twoFormHodge.toLinearIsometry.toContinuousLinearMap.comp
      (InnerProductSpace.rankOne ℝ a b) = InnerProductSpace.rankOne ℝ (twoFormHodge a) b := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul]
    rfl
  change twoFormFiberTrace (twoFormHodge.toLinearIsometry.toContinuousLinearMap.comp _) = _
  rw [he, twoFormFiberTrace_apply, InnerProductSpace.trace_rankOne]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed spectral diagonal as the Gram sum of its six columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff Manifold _root_.Topology NNReal

noncomputable section

theorem twoFormHodge_inner_coordinates (a : TwoFormFour) :
    inner ℝ a (twoFormHodge a) =
      ∑ i, ∑ j, twoFormHodgeMatrix i j * (a i * a j) := by
  rw [← twoFormHodgeMatrix_apply a]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative of the global scalar parametrix is a
compact C4 function, represented in the same scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarTime_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

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

/-! The actual compact scalar parametrix satisfies the forced heat ODE
in every eigenmode. Its forcing is its genuine time-minus-Laplacian residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarEvolution_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The forcing in the spectral scalar ODE is the actual compactly
supported local parametrix residual, with no domain or operator premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarResidual_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time continuity of the actual scalar cutoff and its residual
in the global scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarContinuity_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar forcing has an O(t) L2 bound and a continuous
zero extension. All local coefficient conditions are realized geometrically. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarGlobalResidual_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


