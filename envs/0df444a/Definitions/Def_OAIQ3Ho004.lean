-- Prove2me | Definitions.Def_OAIQ3Ho004
-- name    : OAIQ3Ho004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T05:09:36.097366+00:00
-- url     : https://prove2.me/theorems/849a64bd-e695-45cb-aee0-dd9ce58f3378
-- title:
--   Definitions bundle OAIQ3Ho004 of the split of OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 38 definitions and 13 theorems. The definitions and types are `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.physicalSolution`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution`, `OAI.StrictHotSpots.Conformal.chartPull`, `OAI.StrictHotSpots.Conformal.measurableChart`, `OAI.StrictHotSpots.Conformal.transportH10`, `OAI.StrictHotSpots.Conformal.weightedValue`, `OAI.StrictHotSpots.H1.lipschitzMul`, `OAI.StrictHotSpots.H1.smoothMul`, `OAI.StrictHotSpots.H10.dilation`, `OAI.StrictHotSpots.Hodge.D`, `OAI.StrictHotSpots.Hodge.TangentWeak`, `OAI.StrictHotSpots.Hodge.WeakCurl`, `OAI.StrictHotSpots.Hodge.WeakCurlZero`, `OAI.StrictHotSpots.Hodge.axisL`, `OAI.StrictHotSpots.Hodge.boundaryDefect`, `OAI.StrictHotSpots.Hodge.c`, `OAI.StrictHotSpots.Hodge.coordinateL`, `OAI.StrictHotSpots.Hodge.curlL`, `OAI.StrictHotSpots.Hodge.divergenceL`, `OAI.StrictHotSpots.Hodge.jFunctional`, `OAI.StrictHotSpots.Hodge.partialL`, `OAI.StrictHotSpots.Hodge.residual`, `OAI.StrictHotSpots.Hodge.rot`, `OAI.StrictHotSpots.Hodge.rotL`, `OAI.StrictHotSpots.Hodge.skewEnergy`, `OAI.StrictHotSpots.Hodge.vectorForm`, `OAI.StrictHotSpots.Hodge.vectorValue`, `OAI.StrictHotSpots.PhysicalHelmholtz.correction`, `OAI.StrictHotSpots.PhysicalHelmholtz.extension`, `OAI.StrictHotSpots.PhysicalHelmholtz.forcing`, `OAI.StrictHotSpots.PhysicalHelmholtz.instNormedAddCommGroupSubtypeH1AmbientMemSubmoduleRealH1H10`, `OAI.StrictHotSpots.PhysicalHelmholtz.zeroPair`, `OAI.StrictHotSpots.PlaneGreen.variationalOperator`, `OAI.StrictHotSpots.SubcriticalExtension.WeakPotential`, `OAI.StrictHotSpots.closedGradientTrace`, `OAI.StrictHotSpots.closedTraceSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HotSpots, in whole or in part: [`HotSpots_BoundaryEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/BoundaryEnergy.lean), [`HotSpots_Conformal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Conformal.lean), [`HotSpots_Dirichlet`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Dirichlet.lean), [`HotSpots_GreenOperator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/GreenOperator.lean), [`HotSpots_Hodge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Hodge.lean), [`HotSpots_Multiplier`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplier.lean), [`HotSpots_Potentials`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Potentials.lean), [`HotSpots_Pullback`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean), [`HotSpots_Riemann`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Riemann.lean), [`HotSpots_TraceRank`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/TraceRank.lean), [`HotSpots_VectorEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean).
--
--   **Imports.** It imports the published bundle `Def_HotSpots`; the bundles `OAIQ3Ho002` and `OAIQ3Ho003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_nonneg`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_identity`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_tendsto`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_closed_ae`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_form`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_mul_tendsto`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_weak`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_smooth_multiplier_kernel`, `OAI.StrictHotSpots.Hodge.vectorForm_nonneg`, `OAI.StrictHotSpots.Hodge.vector_equality_interior_pointwise`, `OAI.StrictHotSpots.PlaneGreen.boundarySolution_weak`, `OAI.StrictHotSpots.PlaneGreen.value_K_of_trace`, `OAI.StrictHotSpots.closedTraceSpace_local_rank` and `OAI.StrictHotSpots.closedTraceSpace_rank`; the proofs of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.boundary_gradient_integral_zero`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_nonneg`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_identity`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_tendsto`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.operator_norm_lt_one`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_closed_ae`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_form`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_mul_tendsto`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_weak`, `OAI_StrictHotSpots_Conformal_ClosedDiskChart_smooth_multiplier_kernel`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical`, `OAI.StrictHotSpots.H10.minimum`, `OAI.StrictHotSpots.Hodge.vectorForm_nonneg`, `OAI.StrictHotSpots.Hodge.vector_equality_interior_pointwise`, `OAI.StrictHotSpots.PlaneGreen.boundarySolution_energy`, `OAI.StrictHotSpots.PlaneGreen.boundarySolution_weak`, `OAI.StrictHotSpots.PlaneGreen.fullBoundaryR_symm`, `OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding`, `OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support`, `OAI.StrictHotSpots.PlaneGreen.value_K_of_trace`, `OAI.StrictHotSpots.closedTraceSpace_local_rank` and `OAI.StrictHotSpots.closedTraceSpace_rank`.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HotSpots at commit adc7f12

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
import Definitions.Def_OAIQ3Ho003

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def variationalOperator : Lp ℝ 2 (volume.restrict disk) →L[ℝ] Lp ℝ 2 (volume.restrict disk) :=
  @DirichletOperator.green (H10 diskOpen) (Lp ℝ 2 (volume.restrict disk))
    (H10.normedAddCommGroup diskOpen) (H10.innerProductSpace diskOpen)
    (H10.completeSpace diskOpen) inferInstance inferInstance inferInstance
    (H10.energy diskOpen) (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen)

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Dirichlet
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section BoundedCompactEmbeddingCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.H10
open DiskH10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

def dilation : H10 hΩ →L[ℝ] H10 PlaneGreen.diskOpen :=
  ((smoothTestToH10 PlaneGreen.diskOpen).comp (dilateTest hR hb)).extendOfNorm (smoothTestToH10 hΩ)

end StrictHotSpots.H10
end BoundedCompactEmbeddingCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section SubcriticalUniquenessScalarSupportLayer

open Set MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.SubcriticalExtension
variable {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict Ω)


def WeakPotential (F : H1 Ω) : Prop := ∀ v : H10 ho,
  inner ℝ (H1.grad F) (H10.grad ho v) =
    inner ℝ (observe hC hν F) (H10.weightedValue ho hC hν v)

end StrictHotSpots.SubcriticalExtension
end SubcriticalUniquenessScalarSupportLayer

end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalH10





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

def transportH10 : H10 e.open_source →L[ℝ] H10 e.open_target :=
  ((smoothTestToH10 e.open_target).comp (transportTest e he)).extendOfNorm
    (smoothTestToH10 e.open_source)

end StrictHotSpots.Conformal
end
end ConformalH10

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)



def measurableChart : CoordinatePlane → CoordinatePlane :=
  (chart_aemeasurable e d).mk e

lemma measurableChart_ae : measurableChart e d =ᵐ[chartMeasure e d] e :=
  (chart_aemeasurable e d).ae_eq_mk.symm

lemma measurableChart_preserving
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) :
    MeasurePreserving (measurableChart e d) (chartMeasure e d) (volume.restrict e.target) := by
  refine ⟨(chart_aemeasurable e d).measurable_mk,?_⟩
  exact (Measure.map_congr (measurableChart_ae e d)).trans (map_chartMeasure e d hd)

def chartPull (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) :
    Lp ℝ 2 (volume.restrict e.target) →ₗᵢ[ℝ] Lp ℝ 2 (chartMeasure e d) :=
  Lp.compMeasurePreservingₗᵢ ℝ (measurableChart e d) (measurableChart_preserving e d hd)

end StrictHotSpots.Conformal
end
end ConformalMeasure

section ConformalWeightedValue





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal
variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)
variable (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)


def weightedValue : H10 e.open_source →L[ℝ] Lp ℝ 2 (chartMeasure e d) :=
  (chartPull e d hd).toContinuousLinearMap.comp
    ((H10.value e.open_target).comp (transportH10 e he))

end StrictHotSpots.Conformal
end
end ConformalWeightedValue


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section




section PlaneDifferentialInteriorSupportLayer

open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge
abbrev c (i : Fin 2) (x : Plane) : ℝ := inner ℝ x (e i)

def rot : Plane →L[ℝ] Plane :=
  (innerSL ℝ (e 0)).smulRight (e 1) - (innerSL ℝ (e 1)).smulRight (e 0)

abbrev D (i : Fin 2) (φ : Plane → ℝ) := directionalDerivative φ (e i)
end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer


section WeakHodgeRegularityInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge

def WeakCurlZero (Ω : Set Plane) (Z : Plane → Plane) : Prop :=
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x in Ω, inner ℝ (Z x) (rot (gradient φ x))) = 0

end StrictHotSpots.Hodge

end WeakHodgeRegularityInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Hodge
attribute [-instance] _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section

section HodgeOrthogonalityInteriorSupportLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Hodge

def rotL (Ω : Set Plane) : V2 Ω →L[ℝ] V2 Ω := rot.compLpL 2 (volume.restrict Ω)

end Hodge
end StrictHotSpots

end HodgeOrthogonalityInteriorSupportLayer


section HodgeProjectionInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

def jFunctional {Ω : Set Plane} (ho : IsOpen Ω) (X : Lp Plane 2 (volume.restrict Ω)) :
    H10 ho →L[ℝ] ℝ := (innerSL ℝ X).comp ((rotL Ω).comp (H10.grad ho))
end StrictHotSpots.Hodge

end HodgeProjectionInteriorSupportLayer


section HodgeResidualInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

def residual {Ω : Set Plane} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (X : V2 Ω) (v : N1 hb) (j : H10 ho) : V2 Ω :=
  X - N1.grad hb v - rotL Ω (H10.grad ho j)

end StrictHotSpots.Hodge

end HodgeResidualInteriorSupportLayer


section HodgeVectorEnergyInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Hodge

def WeakCurl {Ω : Set Plane} (ho : IsOpen Ω) (X : Lp Plane 2 (volume.restrict Ω))
    (G : Lp ℝ 2 (volume.restrict Ω)) : Prop :=
  ∀ j : H10 ho, inner ℝ X (rotL Ω (H10.grad ho j)) = -inner ℝ G (H10.value ho j)

end StrictHotSpots.Hodge

end HodgeVectorEnergyInteriorSupportLayer


end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Riemann
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalPotential





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane) (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)

include hd in
lemma chartMeasure_univ : chartMeasure e d univ = volume e.target := by
  have hh := congrArg (fun ν : Measure Plane => ν univ) (map_chartMeasure e d hd)
  rw [Measure.map_apply_of_aemeasurable (chart_aemeasurable e d) MeasurableSet.univ] at hh
  simpa only [preimage_univ,Measure.restrict_apply_univ] using hh

include hd in
lemma chartMeasure_finite (hb : Bornology.IsBounded e.target) :
    IsFiniteMeasure (chartMeasure e d) :=
  ⟨(chartMeasure_univ e d hd).trans_lt hb.measure_lt_top⟩


include hd in
lemma potentialMeasure_finite (μ : ℝ) (hb : Bornology.IsBounded e.target) :
    IsFiniteMeasure (potentialMeasure e d μ) := by
  let := chartMeasure_finite e d hd hb
  exact Measure.smul_finite (chartMeasure e d) ENNReal.ofReal_ne_top

end StrictHotSpots.Conformal
end
end ConformalPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Pullback
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualPotential

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.Conformal
open DiskH10

namespace ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma potential_finite (hb : Bornology.IsBounded Ω) : IsFiniteMeasure c.potential :=
  potentialMeasure_finite c.e c.d c.deriv _ (c.target_eq.symm ▸ hb)



end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section
section H1SmoothMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots



namespace H1
variable {Ω : Set Plane} {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω))
    (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω))

def smoothMul (u : H1 Ω) : H1 Ω :=
  ((H1.hasH1Gradient u).mul_smooth hb hb0 hb1).toH1

end H1
end StrictHotSpots
end H1SmoothMultiplierActualCompatibleLayer

section NullBoundaryFormActualCompatibleLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


def skewEnergy (u v : H1 Ω) : ℝ := inner ℝ (H1.grad u) (rotL Ω (H1.grad v))




def boundaryDefect (X Y : Fin 2 → H1 Ω) : ℝ :=
  -skewEnergy (X 0) (Y 1)+skewEnergy (X 1) (Y 0)

end StrictHotSpots.Hodge
end NullBoundaryFormActualCompatibleLayer

section VectorSobolevActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


def coordinateL (Ω : Set Plane) (i : Fin 2) : V2 Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (innerSL ℝ (e i)).compLpL 2 (volume.restrict Ω)


def axisL (Ω : Set Plane) (i : Fin 2) : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] V2 Ω :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).compLpL 2 (volume.restrict Ω)

def partialL (i : Fin 2) (u : H1 Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  coordinateL Ω i (H1.grad u)

def vectorValue (X : Fin 2 → H1 Ω) : V2 Ω :=
  axisL Ω 0 (H1.value (X 0))+axisL Ω 1 (H1.value (X 1))
def divergenceL (X : Fin 2 → H1 Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  partialL 0 (X 0)+partialL 1 (X 1)
def curlL (X : Fin 2 → H1 Ω) : Lp ℝ 2 (volume.restrict Ω) :=
  partialL 0 (X 1)-partialL 1 (X 0)

end StrictHotSpots.Hodge
end VectorSobolevActualCompatibleLayer

section VectorDefectEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

def vectorForm (μ : ℝ) (X Y : Fin 2 → H1 Ω) : ℝ :=
  inner ℝ (divergenceL X) (divergenceL Y)+inner ℝ (curlL X) (curlL Y)-
    μ*inner ℝ (vectorValue X) (vectorValue Y)

end StrictHotSpots.Hodge
end VectorDefectEnergyActualCompatibleLayer

section TangentVectorClassActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


def TangentWeak (X : Fin 2 → H1 Ω) : Prop :=
  WeakNormalDiv (vectorValue X) (divergenceL X)

end StrictHotSpots.Hodge
end TangentVectorClassActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
end
end ActualVectorSupport

section ActualScalarEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

def physicalSolution {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) : H1 Ω :=
  (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1+
    (show H1 Ω from (transportH10 c.diskMap c.diskMap_inverse_smooth
      (c.datumCorrection hb hs hμ hw hl)).val)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualScalarEnergy

section ActualVectorEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Laplacian
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)


def scalarSolution {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) : H1 Ω :=
  c.physicalSolution hb hs hμ.le hw (c.datumTrace_lipschitz hb hs hw).choose_spec

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualVectorEnergy

section SmoothPhysicalMultiplier

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)



def multipliedGradient {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) : Fin 2 → H1 Ω := fun i =>
  c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ
    (hb.contDiffOn.mul (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)))

end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothPhysicalMultiplier


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzH1

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots


lemma planeApproxBump_rOut_tendsto :
    Tendsto (fun n => (planeApproxBump n).rOut) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma planeApproxBump_ratio (n : ℕ) :
    (planeApproxBump n).rOut ≤ 2*(planeApproxBump n).rIn := by
  dsimp only [planeApproxBump]
  have h : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  norm_num



lemma HasH1Gradient.mul_lipschitz {Ω : Set Plane} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {u : Plane → ℝ} {g : Plane → Plane}
    (hu : HasH1Gradient Ω u g) {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b) :
    HasH1Gradient Ω (fun x => b x*u x) (fun x => b x • g x+u x • gradient b x) := by
  let bn := fun n => ambientSmooth (planeApproxBump n) b
  have hbn (n : ℕ) : ContDiff ℝ ∞ (bn n) := ambientSmooth_smooth _ hb
  have hbl (n : ℕ) : LipschitzWith L (bn n) := ambientSmooth_lipschitz _ hb
  have hb0 := continuous_closure_memLp_top ho hΩ hb.continuous.continuousOn
  have hb1 := lipschitz_gradient_memLp_top (Ω:=Ω) hb
  have hn0 (n : ℕ) := continuous_closure_memLp_top ho hΩ (hbl n).continuous.continuousOn
  have hn1 (n : ℕ) := lipschitz_gradient_memLp_top (Ω:=Ω) (hbl n)
  have hf (n : ℕ) := hu.mul_smooth (hbn n) (hn0 n) (hn1 n)
  have hv : MemLp (fun x => b x*u x) 2 (volume.restrict Ω) := hu.1.mul' hb0
  have hg : MemLp (fun x => b x • g x+u x • gradient b x) 2 (volume.restrict Ω) :=
    (hu.2.1.smul hb0).add (hb1.smul hu.1)
  obtain ⟨C,hC,hbd⟩ := ambientSmooth_uniform_bound hΩ hb
  have ht (x : Plane) : Tendsto (fun n => bn n x) atTop (𝓝 (b x)) :=
    ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb x
  have hgt : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => gradient (bn n) x)
      atTop (𝓝 (gradient b x)) :=
    ae_restrict_of_ae (ambientSmooth_gradient_tendsto planeApproxBump_rOut_tendsto
      (Eventually.of_forall planeApproxBump_ratio) hb)
  apply HasH1Gradient.of_tendsto_L2 hf hv hg
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).1) hv
      (hu.1.norm.const_mul C)
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (ht x).mul_const (u x)
  · apply L2VectorLimits.tendsto_toLp_of_dominated (fun n => (hf n).2.1) hg
      ((hu.2.1.norm.const_mul C).add (hu.1.norm.const_mul (L:ℝ)))
    · filter_upwards [] with n
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      calc
        _ ≤ ‖bn n x • g x‖+‖u x • gradient (bn n) x‖ := norm_add_le _ _
        _ = ‖bn n x‖*‖g x‖+‖u x‖*‖gradient (bn n) x‖ := by rw [norm_smul,norm_smul]
        _ ≤ C*‖g x‖+‖u x‖*(L:ℝ) := add_le_add
          (mul_le_mul_of_nonneg_right (hbd n x hx) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (lipschitz_gradient_bound (hbl n) x) (norm_nonneg _))
        _ = _ := by simp only [Pi.add_apply]; ring
    · filter_upwards [hgt] with x hx
      exact ((ht x).smul_const (g x)).add (tendsto_const_nhds.smul hx)

namespace H1
variable {Ω : Set Plane} (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    {b : Plane → ℝ} {L : ℝ≥0} (hb : LipschitzWith L b)

def lipschitzMul (u : H1 Ω) : H1 Ω :=
  ((H1.hasH1Gradient u).mul_lipschitz ho hΩ hb).toH1

end H1

end StrictHotSpots
end
end LipschitzH1

section PhysicalHelmholtz

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PhysicalHelmholtz
variable {Ω : Set Plane} (ho : IsOpen Ω)
local instance instNormedAddCommGroupSubtypeH1AmbientMemSubmoduleRealH1H10 : NormedAddCommGroup (H10 ho) := H10.normedAddCommGroup ho
local instance instCompleteSpaceSubtypeH1AmbientMemSubmoduleRealH1H10 : CompleteSpace (H10 ho) := H10.completeSpace ho

attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1H10
attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1
def zeroPair (μ : ℝ) : H10 ho →L[ℝ] H10 ho →L[ℝ] ℝ := by
  let a : H10 ho →L[ℝ] H1 Ω →L[ℝ] ℝ := (pair μ).comp (incl ho)
  let b : H1 Ω →L[ℝ] H10 ho →L[ℝ] ℝ := ContinuousLinearMap.flip (E := H10 ho) (F := H1 Ω) a
  exact b.comp (incl ho)

lemma zeroPair_apply (μ : ℝ) (u v : H10 ho) : zeroPair ho μ u v =
    inner ℝ (H10.grad ho u) (H10.grad ho v)-μ*inner ℝ (H10.value ho u) (H10.value ho v) := rfl

lemma zeroPair_self (μ : ℝ) (v : H10 ho) : zeroPair ho μ v v=
    ‖H10.grad ho v‖^2-μ*‖H10.value ho v‖^2 :=
  (zeroPair_apply ho μ v v).trans (congrArg₂ (fun a b : ℝ => a-μ*b)
    (real_inner_self_eq_norm_sq (H10.grad ho v))
    (real_inner_self_eq_norm_sq (H10.value ho v)))

attribute [local instance] OAI.StrictHotSpots.PhysicalHelmholtz.instInnerProductSpaceRealSubtypeH1AmbientMemSubmoduleH1H10
lemma zeroPair_coercive (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) :
    @IsCoercive (H10 ho) (H10.normedAddCommGroup ho).toSeminormedAddCommGroup
      (H10.innerProductSpace ho).toNormedSpace (zeroPair ho μ) := by
  obtain ⟨C,hC,hE⟩ := H10.energy_coercive ho hb
  have hL : 0 < L := lt_of_le_of_lt hμ hl
  have hρ : 0 < 1-μ/L := sub_pos.mpr ((div_lt_one hL).mpr hl)
  refine ⟨(1-μ/L)*C,mul_pos hρ hC,fun v => ?_⟩
  have hv : C*‖v‖*‖v‖ ≤ ‖H10.grad ho v‖^2 :=
    (hE v).trans_eq (by rw [H10.energy_apply,real_inner_self_eq_norm_sq])
  exact (subcritical_numeric hμ hl hv (hD v)).trans_eq
    (zeroPair_self ho μ v).symm

def forcing (μ : ℝ) : H1 Ω →L[ℝ] H10 ho →L[ℝ] ℝ := by
  let a : H10 ho →L[ℝ] H1 Ω →L[ℝ] ℝ := (pair μ).flip.comp (incl ho)
  let b : H1 Ω →L[ℝ] H10 ho →L[ℝ] ℝ := ContinuousLinearMap.flip (E := H10 ho) (F := H1 Ω) a
  exact -b

def correction (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) :
    H1 Ω →L[ℝ] H10 ho :=
  (zeroPair_coercive ho hb hμ hl hD).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    ((InnerProductSpace.toDual ℝ (H10 ho)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (forcing ho μ))

def extension (hb : Bornology.IsBounded Ω) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hl : μ < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2) :
    H1 Ω →L[ℝ] H1 Ω :=
  ContinuousLinearMap.id ℝ (H1 Ω)+(incl ho).comp (correction ho hb hμ hl hD)

end StrictHotSpots.PhysicalHelmholtz
end
end PhysicalHelmholtz

section PhysicalMultiplierLimit

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)


def lipschitzMultipliedGradient {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) : Fin 2 → H1 Ω := fun i =>
  PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
    (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (eigenGradientField hΩ hu i))

end StrictHotSpots.Conformal.ClosedDiskChart

end
end PhysicalMultiplierLimit


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedTraceRank

noncomputable section
open Set Function Module
open scoped Topology
namespace StrictHotSpots
open HilbertMultipliers


def closedGradientTrace {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 →ₗ[ℝ] (Circle → Plane) where
  toFun J s := J.val.2 ⟨c.circleBoundaryHomeomorph s,(c.circleBoundaryHomeomorph s).property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def closedTraceSpace {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Submodule ℝ (Circle → Plane) := (closedGradientTrace c hΩ).range

end StrictHotSpots
end
end ClosedTraceRank



end OAI
end


