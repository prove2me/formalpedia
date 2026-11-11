-- Prove2me | Definitions.Def_OAIQ232A025
-- name    : OAIQ232A025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:20:01.902368+00:00
-- url     : https://prove2.me/theorems/a5e08342-1660-4c05-a0df-2c538545b366
-- title:
--   Definitions bundle OAIQ232A025 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 17 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_HopfGradient`, `BiholderTransport_Convexity_ParametricShortLowerEnvelope`, `BiholderTransport_Coordinates_ActiveCompact`, `BiholderTransport_Coordinates_ActiveHull`, `BiholderTransport_Coordinates_CompactConfigurations`, `BiholderTransport_Coordinates_CutCharacterization`, `BiholderTransport_Coordinates_ExpLocalBounds`, `BiholderTransport_Coordinates_ExpVertical`, `BiholderTransport_Coordinates_MetricLocalGrowth`, `BiholderTransport_Coordinates_SplitLogInjective`, `BiholderTransport_CostGeometry_PrecutExtension`, `BiholderTransport_Geodesics_BranchExtension`, `BiholderTransport_Geodesics_SprayDistanceBound`, `BiholderTransport_Volume_ExponentialJacobian`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A022` and `OAIQ232A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A027` and `OAIQ232A028`; the proofs of `OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit`, `OAI.WeakMTWTransport.cTransform_ae_active_before_cut`, `OAI.WeakMTWTransport.cTransform_ae_normal_quadraticExpansion`, `OAI.WeakMTWTransport.exists_true_center_jet_gain` and `OAI.WeakMTWTransport.exists_true_center_limit`.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A022
import Definitions.Def_OAIQ232A023

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayDistanceBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma closure_injectivityDomain (x : M) :
    closure (injectivityDomain (n := n) x) = minimizingVectors x := by
  apply subset_antisymm
  · exact closure_minimal (injectivityDomain_subset_minimizingVectors x) (isClosed_minimizingVectors x)
  · intro p hp
    apply closure_mono (s := openSegment ℝ 0 p) ?_ (segment_subset_closure_openSegment (right_mem_segment ℝ 0 p))
    rintro q ⟨a,b,ha,hb,hab,rfl⟩
    rw [smul_zero,zero_add]
    exact contracted_minimizer_mem_injectivityDomain hp hb (by linarith)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveHull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma nonempty_activeLogs {v : M → ℝ} (hv : Continuous v) (x : M) :
    (activeLogs (n := n) v x).Nonempty := by
  let : Nonempty M := ⟨x⟩
  obtain ⟨y,hy⟩ := cTransform_gap_zero hv x
  obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) x y
  exact ⟨p,hp,by simpa only [he] using hy⟩

lemma isCompact_activeLogs {v : M → ℝ} (hv : Continuous v) (x : M) :
    IsCompact (activeLogs (n := n) v x) := by
  have hc : Continuous (fun p : TangentSpace 𝓘(ℝ,Model n) x =>
      contactGap (cTransform v) v x (riemannianExp x p)) := by
    exact (continuous_const.add ((continuous_cost_right x).comp (continuous_riemannianExp x))).add
      (hv.comp (continuous_riemannianExp x))
  exact (isCompact_minimizingVectors x).inter_right (isClosed_eq hc continuous_const)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_MetricLocalGrowth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma metric_local_growth_of_normal {f : M → ℝ} {x : M} {b : ℝ}
    (h : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      b*‖v‖^2≤f (riemannianExp x v)-f x) :
    ∀ᶠ z in 𝓝 x, b*dist x z^2≤f z-f x := by
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp h
  filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
  obtain ⟨v,hv,he⟩ := exists_minimizing_vector (n := n) x z
  have hd : ‖v‖=dist x z := by simpa only [minimizingVectors,mem_ofPred_eq,he] using hv.symm
  have hh := hball (y := v) (by simpa only [Metric.mem_ball,dist_zero_right,hd,dist_comm] using hz)
  simpa only [he,hd] using hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma isCompact_total_activeLogs {v : M → ℝ} (hv : Continuous v) :
    IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs (n := n) v z.1} := by
  cases isEmpty_or_nonempty M with
  | inl h =>
      have he : {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs (n := n) v z.1}=∅ := by
        ext z
        exact isEmptyElim z.1
      rw [he]
      exact isCompact_empty
  | inr h =>
      have hc : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
          contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2)) := by
        have hp : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
          FiberBundle.continuous_proj _ _
        have he := (contMDiff_riemannianExp (n := n) (M := M)).continuous
        exact (((continuous_cTransform hv).comp hp).add
          (((hp.dist he).pow 2).div_const 2)).add (hv.comp he)
      exact (isCompact_total_minimizingVectors (n := n) (M := M)).inter_right
        (isClosed_eq hc continuous_const)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CutCharacterization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma mem_injectivityDomain_of_nonconjugate_unique {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p))
    (hu : ∀ q ∈ minimizingVectors x, riemannianExp x q=riemannianExp x p → q=p) :
    p ∈ injectivityDomain x := by
  apply interior_minimizingVectors_subset x
  apply interior_of_compact_unique_fiber (isCompact_minimizingVectors x)
    (continuous_riemannianExp x) (exists_minimizing_vector x) hu
  obtain ⟨U,hU,hpU,hinj⟩ := joint_exp_locally_injective_of_nonconjugate ⟨x,p⟩ hp
  let I := fun q : TangentSpace 𝓘(ℝ,Model n) x => (⟨x,q⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hI : Continuous I := FiberBundle.continuous_totalSpaceMk (Model n) _ x
  refine ⟨I ⁻¹' U,hU.preimage hI,hpU,?_⟩
  intro a ha b hb he
  exact TotalSpace.mk_injective x (hinj ha hb (Prod.ext rfl he))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_BranchExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_branch_agrees_on_minimizing
    {z : TangentBundle 𝓘(ℝ,Model n) M} {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (z.1,riemannianExp z.1 z.2))
    (hagree : ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
      (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G) :
    ∀ᶠ r in 𝓝 z, r.2 ∈ minimizingVectors r.1 →
      cost r.1 (riemannianExp r.1 r.2) = G (r.1,riemannianExp r.1 r.2) := by
  let F := fun r : TangentBundle 𝓘(ℝ,Model n) M => (r.1, riemannianExp r.1 r.2)
  have hF : Continuous F := (FiberBundle.continuous_proj _ _).prodMk contMDiff_riemannianExp.continuous
  have hGc : ∀ᶠ q in 𝓝 (F z), ContinuousAt G q := by
    have H := (contMDiffAt_iff_contMDiffAt_nhds
      (by norm_num : (1 : WithTop ℕ∞) ≠ (↑(⊤:ℕ∞) : WithTop ℕ∞))).mp
        (hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    exact H.mono (fun q hq => hq.continuousAt)
  filter_upwards [eventually_eventually_nhds.mpr hagree,hF.continuousAt.eventually hGc] with r hr hc hmin
  have hrcl : r.2 ∈ closure (injectivityDomain r.1) := by rwa [closure_injectivityDomain]
  have : NeBot (𝓝[injectivityDomain r.1] r.2) := mem_closure_iff_nhdsWithin_neBot.mp hrcl
  have hi : Continuous (fun p : TangentSpace 𝓘(ℝ,Model n) r.1 =>
      (⟨r.1,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    FiberBundle.continuous_totalSpaceMk (Model n) _ r.1
  have heq : (fun p => cost r.1 (riemannianExp r.1 p)) =ᶠ[𝓝[injectivityDomain r.1] r.2]
      (fun p => G (r.1,riemannianExp r.1 p)) := by
    filter_upwards [(hi.continuousAt.eventually hr).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with p hp hpID
    exact (hp hpID).self_of_nhds
  have he : Continuous (fun p : TangentSpace 𝓘(ℝ,Model n) r.1 => (r.1,riemannianExp r.1 p)) :=
    continuous_const.prodMk (contMDiff_riemannianExp_fiber (n := n) r.1).continuous
  change ContinuousAt G (r.1,riemannianExp r.1 r.2) at hc
  have hg : ContinuousAt (fun p : TangentSpace 𝓘(ℝ,Model n) r.1 =>
      G (r.1,riemannianExp r.1 p)) r.2 := hc.comp (f := fun p : TangentSpace 𝓘(ℝ,Model n) r.1 =>
        (r.1,riemannianExp r.1 p)) (he.continuousAt (x := r.2))
  apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[injectivityDomain r.1] r.2)
    (((continuous_cost_right r.1).comp
      (contMDiff_riemannianExp_fiber (n := n) r.1).continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) heq

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_PrecutExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma scaled_injectivityDomain_of_le {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t S : ℝ} (hS : 0<S) (ht : 0≤t) (htS : t≤S) (hp : S • p ∈ injectivityDomain x) :
    t • p ∈ injectivityDomain x := by
  rcases eq_or_lt_of_le ht with h0 | ht0
  · rw [←h0,zero_smul]
    exact zero_mem_injectivityDomain x
  rcases eq_or_lt_of_le htS with he | hlt
  · rwa [he]
  have hh := contracted_minimizer_mem_injectivityDomain (injectivityDomain_subset_minimizingVectors x hp)
    (div_pos ht0 hS) ((div_lt_one hS).mpr hlt)
  simpa only [smul_smul,div_mul_cancel₀ _ hS.ne'] using hh

end WeakMTWTransport

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CompactConfigurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CompactConfigurations
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma isCompact_active_coordinates {v : M → ℝ} (hv : Continuous v)
    {a : M} {K : Set M} (hK : IsCompact K)
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source) :
    IsCompact ((extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
        {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K}) := by
  have hk : IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M |
      z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K} :=
    (isCompact_total_activeLogs hv).inter_right
      (hK.isClosed.preimage (FiberBundle.continuous_proj _ _))
  apply hk.image_of_continuousOn
  apply (continuousOn_extChartAt _).mono
  intro z hz
  exact (tangent_chart_source_iff _ z).mpr (hKa hz.2)

end CompactConfigurations

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_HopfGradient
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hopfLax_derivative_of_minimizer {u : M → ℝ} (hu : Continuous u)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1)
    (heq : hopfLax t u (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 =
      u x+cost x (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) := by
  let w : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let z := sprayFlow t w
  obtain ⟨ε,hε,hεt,_,_,Hε⟩ := exists_two_short_legs x p ht
    (show t<t+1 by linarith) zero_lt_one
  have hshort := (Filter.Eventually.self_of_nhds Hε).2.2.2
  let a := (sprayFlow (t-ε) w).1
  let G : M → ℝ := fun y => u x+cost x a/(t-ε)+cost a y/ε
  have hG : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) G z.1 (innerSL ℝ z.2) := by
    have H := (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ))
      (u x+cost x a/(t-ε)) z.1).add (hshort.const_smul ε⁻¹)
    have heD : 0+ε⁻¹ • innerSL ℝ (ε • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) =
        innerSL ℝ z.2 := by
      ext v
      simp only [zero_add,_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,
        real_inner_smul_left]
      dsimp [z,w]
      field_simp
    replace H := H.congr_mfderiv heD
    have heG : G = ((fun _ => u x+cost x a/(t-ε)) +
        ε⁻¹ • fun y => dist (sprayFlow (t-ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 y^2/2) := by
      funext y
      dsimp [G,cost,a,w]
      ring
    rw [heG]
    exact H
  have hmin : dist x z.1=t*‖p‖ := by
    dsimp [z,w]
    rw [←riemannianExp_smul,minimizingVectors_smul hp ht.le ht1,norm_smul,
      Real.norm_eq_abs,abs_of_pos ht]
  have hleft : dist x a=(t-ε)*‖p‖ :=
    sprayFlow_minimizing_prefix w (sub_pos.mpr hεt).le (by linarith) hmin
  have hright : dist a z.1=ε*‖p‖ := by
    have H := sprayFlow_minimizing_subinterval w (sub_pos.mpr hεt).le (by linarith) hmin
    simpa only [sub_sub_cancel] using H
  have hcontact : hopfLax t u z.1=G z.1 := by
    rw [heq]
    dsimp [G,cost]
    rw [hmin,hleft,hright]
    field_simp
    ring
  have hle : ∀ y, hopfLax t u y≤G y := by
    intro y
    have H := cost_divided_triangle_two_times x a y (sub_pos.mpr hεt) hε
    rw [sub_add_cancel] at H
    exact (hopfLax_le hu t y x).trans (by dsimp [G] <;> linarith)
  exact hd.hasMFDerivAt.congr_mfderiv
    ((upper_contact_mfderiv hd hG.mdifferentiableAt (Filter.Eventually.of_forall hle) hcontact).trans hG.mfderiv)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ParametricShortLowerEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma scalar_normal_remainder {v : M → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    {φ : ℝ → ℝ} {x : M} {l : ℝ} (hφ : HasDerivAt φ l (v x)) :
    (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      φ (v (riemannianExp x h))-φ (v x)-l*(v (riemannianExp x h)-v x))
      =o[𝓝 0] (fun h => ‖h‖) := by
  have ht : Tendsto (fun h : TangentSpace 𝓘(ℝ,Model n) x => v (riemannianExp x h))
      (𝓝 0) (𝓝 (v x)) := by
    simpa only [Function.comp_def,riemannianExp_zero] using (hv.continuous.comp (continuous_riemannianExp (n := n) x)).continuousAt.tendsto (x := 0)
  have hO : (fun h : TangentSpace 𝓘(ℝ,Model n) x => v (riemannianExp x h)-v x)
      =O[𝓝 0] (fun h => ‖h‖) := by
    apply IsBigO.of_bound (L:ℝ)
    filter_upwards [] with h
    have H := hv.dist_le_mul (riemannianExp x h) x
    have H1 := mul_le_mul_of_nonneg_left (dist_riemannianExp_le x h) L.coe_nonneg
    rw [dist_comm x] at H1
    simpa only [Real.dist_eq,Real.norm_eq_abs,abs_norm] using H.trans H1
  simpa only [Function.comp_def,smul_eq_mul,mul_comm] using
    (hφ.isLittleO.comp_tendsto ht).trans_isBigO hO

omit [Nonempty M] in
lemma scalar_normalSubdifferential_inv {v : M → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) {φ : ℝ → ℝ} {x : M} {l : ℝ}
    (hφ : HasDerivAt φ l (v x)) (hl : 0<l)
    {r : TangentSpace 𝓘(ℝ,Model n) x}
    (hr : r∈normalSubdifferential (fun y => φ (v y)) x) :
    l⁻¹ • r∈normalSubdifferential v x := by
  intro ε hε
  have hres := scalar_normal_remainder (n := n) hv hφ
  filter_upwards [hr (l*ε/2) (by positivity),hres.bound (by positivity : 0<l*ε/2)] with h hh hR
  simp only [Real.norm_eq_abs,abs_norm] at hR
  have hR' := (abs_le.mp hR).2
  have H : inner ℝ r h-l*ε*‖h‖≤l*(v (riemannianExp x h)-v x) := by
    linarith only [hh,hR']
  have HI := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hl.le)
  simpa only [real_inner_smul_left,mul_sub,←mul_assoc,inv_mul_cancel₀ hl.ne',
    one_mul] using HI

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitLogInjective
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SplitLogInjective
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefix_log_fderiv_injective {x y : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ} (ht : t≠0)
    (hleft : t • p∈injectivityDomain x)
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q p)
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a)) :
    Function.Injective (fderiv ℝ q p) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  apply (injective_iff_map_eq_zero (fderiv ℝ q p)).mpr
  intro v hv
  have he := (contMDiff_riemannianExp_fiber y (q p)).mdifferentiableAt (by simp)
  have hD := he.hasMFDerivAt.comp p hq.hasFDerivAt.hasMFDerivAt
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 p] (fun a : X => riemannianExp x (t • a)) := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hE := hD'.mfderiv
  have hV : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (fun a : X => riemannianExp x (t • a)) p v=0 := by
    rw [hE]
    change mfderiv 𝓘(ℝ,Y) 𝓘(ℝ,Model n) (riemannianExp y) (q p) (fderiv ℝ q p v)=0
    rw [hv]
    exact map_zero _
  have hscale : HasFDerivAt (fun a : X => t • a) (t • ContinuousLinearMap.id ℝ X) p :=
    (t • ContinuousLinearMap.id ℝ X).hasFDerivAt
  have hExp := ((contMDiff_riemannianExp_fiber x (t • p)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp p hscale.hasMFDerivAt
  have hEV := congrArg (fun L : X →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp x (t • p)) => L v) hExp.mfderiv
  have hW : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) (t • p) (t • v)=0 :=
    hEV.symm.trans hV
  rw [exp_mfderiv_apply_eq_coordinate] at hW
  have htv : t • v=0 := (riemannianExp_interior_nonconjugate hleft)
    (hW.trans (map_zero _).symm)
  exact (smul_eq_zero.mp htv).resolve_left ht

end SplitLogInjective
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ExponentialJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExponentialJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteExponentialJacobian_r8309c9_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma expJacobian_pos_of_injectivityDomain {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) : 0<expJacobian (n := n) x p := by
  apply lt_of_le_of_ne (expJacobian_nonneg x p)
  apply Ne.symm
  rw [expJacobian_ne_zero_iff]
  have hcoord := mfderiv_comp p (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,Model n)) (mem_chart_source (Model n) (riemannianExp x p)))
    ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv,mfderiv_extChartAt_self] at hcoord
  change fderiv ℝ _ p=mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
    𝓘(ℝ,Model n) (riemannianExp x) p at hcoord
  simp only [Function.comp_def] at hcoord
  erw [←hcoord]
  exact riemannianExp_interior_nonconjugate hp

end ExponentialJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpVertical
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpVertical
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateEndpointVertical_injective {c : TangentBundle 𝓘(ℝ,Model n) M}
    (hc : c.2∈injectivityDomain c.1) : Function.Injective (coordinateEndpointVertical c c) := by
  let X := TangentSpace 𝓘(ℝ,Model n) c.1
  let Y := TangentSpace 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
  let U := (trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1)
  let V := (trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2))
  have hU : c.1∈U.baseSet := mem_baseSet_trivializationAt (Model n) _ c.1
  have hV : riemannianExp c.1 c.2∈V.baseSet := mem_baseSet_trivializationAt (Model n) _ _
  have hE := (expJacobian_ne_zero_iff (n := n) c.1 c.2).mp
    (expJacobian_pos_of_injectivityDomain hc).ne'
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  let u : X := U.symmL ℝ c.1 w
  have huw : U.continuousLinearMapAt ℝ c.1 u=w := U.continuousLinearMapAt_symmL hU w
  have heq := coordinateEndpointVertical_apply c c (mem_extChartAt_source c)
    (mem_extChartAt_source _) u
  rw [huw,hw] at heq
  have hz : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp c.1) c.2 u=0 := by
    have h := congrArg (V.symmL ℝ (riemannianExp c.1 c.2)) heq.symm
    rw [V.symmL_continuousLinearMapAt hV,map_zero] at h
    exact h
  have hu : u=0 := hE (hz.trans (map_zero _).symm)
  rw [←huw,hu,map_zero]

end ExpVertical
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpLocalBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpLocalBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventually_exp_differential_bounds {c : TangentBundle 𝓘(ℝ,Model n) M}
    (hc : c.2∈injectivityDomain c.1) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 c,
      ∀ v : TangentSpace 𝓘(ℝ,Model n) z.1,
      l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖≤u*‖v‖ := by
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let U := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let V := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  obtain ⟨l,u,hl,hu,hlu⟩ := eventually_injective_operator_bounds
    (coordinateEndpointVertical_continuousAt c) (coordinateEndpointVertical_injective hc)
  obtain ⟨CU,hCU,hUb⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  obtain ⟨DU,hDU,hUib⟩ := eventually_norm_symmL_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  obtain ⟨CV,hCV,hVb⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  obtain ⟨DV,hDV,hVib⟩ := eventually_norm_symmL_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2)
  have hproj : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
    (Bundle.contMDiff_proj (n := ∞) (IB := 𝓘(ℝ,Model n)) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).continuous
  have hE := (contMDiff_riemannianExp (n := n) (M := M)).continuous.continuousAt (x := c)
  have hsource := extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  have htarget := hE.eventually (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) (riemannianExp c.1 c.2))
  refine ⟨l/(DU*CV),DV*u*CU,div_pos hl (mul_pos hDU hCV),
    mul_pos (mul_pos hDV hu) hCU,?_⟩
  filter_upwards [hlu,hsource,htarget,hproj.continuousAt.eventually hUb,
    hproj.continuousAt.eventually hUib,hE.eventually hVb,hE.eventually hVib]
    with z hz hzs hzt hzU hzUi hzV hzVi
  have hzUs : z.1∈U.baseSet := by
    simpa only [U,TangentBundle.trivializationAt_baseSet,extChartAt_source]
      using (tangent_chart_source_iff c z).mp hzs
  have hzVs : riemannianExp z.1 z.2∈V.baseSet := by
    dsimp only [V]
    rw [TangentBundle.trivializationAt_baseSet]
    rw [extChartAt_source] at hzt
    exact hzt
  exact operator_bounds_through_charts (U.continuousLinearMapAt ℝ z.1) (U.symmL ℝ z.1)
    (V.continuousLinearMapAt ℝ (riemannianExp z.1 z.2)) (V.symmL ℝ (riemannianExp z.1 z.2))
    (coordinateEndpointVertical c z)
    (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2)
    (U.symmL_continuousLinearMapAt hzUs) (V.symmL_continuousLinearMapAt hzVs)
    (coordinateEndpointVertical_apply c z hzs hzt)
    hl hu hCU hDU hCV hDV hzU.le hzUi.le hzV.le hzVi.le hz

end ExpLocalBounds
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpCompactBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma compact_exp_differential_bounds {K : Set (TangentBundle 𝓘(ℝ,Model n) M)}
    (hK : IsCompact K) (hI : ∀ z∈K, z.2∈injectivityDomain z.1) :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ z∈K, ∀ v : TangentSpace 𝓘(ℝ,Model n) z.1,
      l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) z.2 v‖≤u*‖v‖ := by
  apply compact_local_positive_bounds hK
  · intro r R b B hr hrR hbB z hz v
    exact ⟨(mul_le_mul_of_nonneg_right hrR (norm_nonneg v)).trans (hz v).1,
      (hz v).2.trans (mul_le_mul_of_nonneg_right hbB (norm_nonneg v))⟩
  · exact fun z hz => eventually_exp_differential_bounds (hI z hz)

end ExpCompactBounds
end WeakMTWTransport

end

end

end

end OAI
end


