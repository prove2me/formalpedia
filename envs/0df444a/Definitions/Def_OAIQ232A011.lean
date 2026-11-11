-- Prove2me | Definitions.Def_OAIQ232A011
-- name    : OAIQ232A011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:47:09.2599+00:00
-- url     : https://prove2.me/theorems/cb38a9e3-98be-4914-a2c6-445d01713879
-- title:
--   Definitions bundle OAIQ232A011 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 62 declarations of OpenAI's Lean: 23 definitions and 39 theorems. The definitions and types are `OAI.WeakMTWTransport.NormalAlexandrovContact`, `OAI.WeakMTWTransport.Phase`, `OAI.WeakMTWTransport.activeConfiguration`, `OAI.WeakMTWTransport.activeCoordinates`, `OAI.WeakMTWTransport.activeLimitDualGroup`, `OAI.WeakMTWTransport.activeLimitDualSpace`, `OAI.WeakMTWTransport.centerRowParameter`, `OAI.WeakMTWTransport.chartContactRelation`, `OAI.WeakMTWTransport.chartCostCovector`, `OAI.WeakMTWTransport.chartGradientVector`, `OAI.WeakMTWTransport.chartJacobian`, `OAI.WeakMTWTransport.chartJetMatrix`, `OAI.WeakMTWTransport.chartRay`, `OAI.WeakMTWTransport.chartTestContact`, `OAI.WeakMTWTransport.coordinateContact`, `OAI.WeakMTWTransport.coordinateEndpoint`, `OAI.WeakMTWTransport.coordinateEndpointVertical`, `OAI.WeakMTWTransport.expJacobian`, `OAI.WeakMTWTransport.frameMetric`, `OAI.WeakMTWTransport.movingNormalCost`, `OAI.WeakMTWTransport.movingPrefixChart`, `OAI.WeakMTWTransport.scalarCostSupport`, `OAI.WeakMTWTransport.scaledNormalEnvelope`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_CompactSmoothGrowth`, `BiholderTransport_Calculus_HopfGradient`, `BiholderTransport_Calculus_ScalarFamily`, `BiholderTransport_Contact_ActiveContinuationLocal`, `BiholderTransport_Contact_CenterSupport`, `BiholderTransport_Contact_CenterSupportFamily`, `BiholderTransport_Contact_ContactDerivative`, `BiholderTransport_Contact_ContactRelationChart`, `BiholderTransport_Contact_ContactStationarity`, `BiholderTransport_Contact_CoordinateScalarSupport`, `BiholderTransport_Contact_LocalCEMS`, `BiholderTransport_Contact_LocalCEMS2`, `BiholderTransport_Contact_SmoothTestPDE`, `BiholderTransport_Contact_SubgradientUpper`, `BiholderTransport_Convexity_CompactConvexHullFinite`, `BiholderTransport_Convexity_EnvelopeData`, `BiholderTransport_Convexity_UniformEnvelope`, `BiholderTransport_Coordinates_ActiveCompact`, `BiholderTransport_Coordinates_ActiveHullUniform`, `BiholderTransport_Coordinates_ActiveUniformGrowth`, `BiholderTransport_Coordinates_ChartCostJets`, `BiholderTransport_Coordinates_ChartGradientMap`, `BiholderTransport_Coordinates_CompactConfigurations`, `BiholderTransport_Coordinates_GraphCoordinates`, `BiholderTransport_Coordinates_ManifoldMinimum`, `BiholderTransport_Coordinates_NormalCoordinates3`, `BiholderTransport_Coordinates_NormalSubdifferential`, `BiholderTransport_Coordinates_PoleCoordinates`, `BiholderTransport_Coordinates_SplitLogInjective`, `BiholderTransport_Geodesics_GeodesicBasics`, `BiholderTransport_Geodesics_InjectivityOpen`, `BiholderTransport_LinearAlgebra_ChartTrueMatrix`, `BiholderTransport_LinearAlgebra_ContactDifferential`, `BiholderTransport_LocalFlow_CotangentFlow`, `BiholderTransport_Regularity_ActualParameter`, `BiholderTransport_Regularity_CenterRayLimit`, `BiholderTransport_Regularity_EuclideanUpper`, `BiholderTransport_Regularity_FrameMetric`, `BiholderTransport_Regularity_MaximumActiveLimits`, `BiholderTransport_Regularity_MovingPrefix`, `BiholderTransport_Volume_IntrinsicJacobian`, `BiholderTransport_Volume_UniformJacobian`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A000`, `OAIQ232A001`, `OAIQ232A004` and `OAIQ232A005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A016`; the statements `OAI.WeakMTWTransport.continuous_expJacobian`, `OAI.WeakMTWTransport.exists_uniform_center_support_pullback` and `OAI.WeakMTWTransport.moving_center_sequential_semibound`.
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
import Definitions.Def_OAIQ232A000
import Definitions.Def_OAIQ232A001
import Definitions.Def_OAIQ232A004
import Definitions.Def_OAIQ232A005

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_CompactSmoothGrowth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter
open scoped Topology ContDiff

lemma compact_smooth_data_transverse_growth
    {P Q E : Type*} [TopologicalSpace P] [CompactSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Q → ι → E → ℝ) (d : P → Q) (hd : Continuous d) (w : P → ι → ℝ)
    (hw : ∀ a i, 0 ≤ w a i) (hsum : ∀ a, ∑ i, w a i = 1)
    (hwc : ∀ i, Continuous (fun a => w a i))
    (hf : ∀ a i, ContDiffAt ℝ ∞ (fun q : Q × E => F q.1 i q.2) (d a,0))
    (hf0 : ∀ a i, F (d a) i 0 = 0)
    (hmean : ∀ a v, ∑ i, w a i * fderiv ℝ (F (d a) i) 0 v = 0)
    (hpos : ∀ a v, ‖v‖ = 1 → (∀ i, fderiv ℝ (F (d a) i) 0 v ≤ 0) →
      0 < ∑ i, w a i * fderiv ℝ (fderiv ℝ (F (d a) i)) 0 v v) :
    ∃ b > 0, ∀ᶠ h : E in 𝓝 0, ∀ a : P, ∃ i, b * ‖h‖^2 ≤ F (d a) i h := by
  have hc : Continuous (fun q : E × P => (d q.2,q.1)) :=
    (hd.comp continuous_snd).prodMk continuous_fst
  have hF : ∀ a i, ∀ᶠ q : E × P in 𝓝 (0,a), ContDiffAt ℝ 2 (F (d q.2) i) q.1 := by
    intro a i
    have H := ((hf a i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hc.continuousAt.tendsto.eventually H] with q hq
    exact hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
  have hD : ∀ a i, ContinuousAt (fun q : E × P =>
      fderiv ℝ (fderiv ℝ (F (d q.2) i)) q.1) (0,a) := by
    intro a i
    exact (ContDiffAt.partial_snd_fderiv_two (f := fun q => F q i) (hf a i)).continuousAt.comp
      (x := (0,a)) (f := fun q : E × P => (d q.2,q.1)) hc.continuousAt
  apply compact_finite_smooth_transverse_growth (fun a => F (d a)) w hw hsum hwc hF hf0
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (ContDiffAt.partial_snd_fderiv (f := fun q => F q i) (hf a i)).continuousAt.comp
      (x := a) (f := fun a => (d a,(0:E))) (hd.continuousAt.prodMk continuousAt_const)
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (hD a i).comp (x := a) (f := fun a => ((0:E),a))
      (continuousAt_const.prodMk continuousAt_id)
  · exact hD
  · exact hmean
  · exact hpos

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ManifoldMinimum
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma upper_contact_mfderiv {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x)
    (hg : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) g x)
    (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y) (heq : f x=g x) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x=mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) g x := by
  have hmin : IsLocalMin (fun y => g y-f y) x := by
    filter_upwards [hle] with y hy
    change g x-f x ≤ g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := IsLocalMin.mfderiv_eq_zero hmin (hg.sub hf)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (g-f) x = 0 at H
  rw [mfderiv_sub hg hf] at H
  exact (sub_eq_zero.mp H).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicBasics
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

omit [IsManifold 𝓘(ℝ, Model n) ∞ M] in
lemma zero_mem_injectivityDomain (x : M) : (0 : TangentSpace 𝓘(ℝ, Model n) x) ∈ injectivityDomain x := by
  refine ⟨2, by norm_num, ?_⟩
  simp

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_InjectivityOpen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma interior_minimizingVectors_subset (x : M) :
    interior (minimizingVectors (n := n) x) ⊆ injectivityDomain x := by
  intro p hp
  have h : {a : ℝ | a • p ∈ minimizingVectors (n := n) x} ∈ 𝓝 (1:ℝ) := by
    have H := (continuous_id.smul continuous_const : Continuous (fun a : ℝ => a • p))
    apply H.continuousAt.preimage_mem_nhds
    change minimizingVectors (n := n) x ∈ 𝓝 ((1:ℝ) • p)
    simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hp
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp h
  let a := 1+δ/2
  have ha : 1<a := by dsimp [a] <;> linarith
  have hpa : a • p ∈ minimizingVectors (n := n) x := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    dsimp [a]
    rw [add_sub_cancel_left,abs_of_pos (by positivity : 0<δ/2)]
    linarith
  refine ⟨a,ha,?_⟩
  change dist x (riemannianExp x (a • p)) = a*‖p‖
  change dist x (riemannianExp x (a • p)) = ‖a • p‖ at hpa
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one ha)] using hpa

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalSubdifferential
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

namespace WeakMTWTransport

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma convex_normalSubdifferential (u : M → ℝ) (x : M) :
    Convex ℝ (normalSubdifferential (n := n) u x) := by
  intro p hp q hq a b ha hb hab ε hε
  filter_upwards [hp ε hε,hq ε hε] with h hh hk
  calc
    inner ℝ (a • p+b • q) h-ε*‖h‖ =
        a*(inner ℝ p h-ε*‖h‖)+b*(inner ℝ q h-ε*‖h‖) := by
      simp only [inner_add_left,real_inner_smul_left,mul_sub]
      have he := congrArg (fun r : ℝ => r*(ε*‖h‖)) hab
      nlinarith [he]
    _ ≤ a*(u (riemannianExp x h)-u x)+b*(u (riemannianExp x h)-u x) :=
      add_le_add (mul_le_mul_of_nonneg_left hh ha) (mul_le_mul_of_nonneg_left hk hb)
    _ = u (riemannianExp x h)-u x := by rw [←add_mul,hab,one_mul]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActiveContinuationLocal
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma smooth_lower_support_mem_normalSubdifferential {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {g : TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hg : HasFDerivAt g (innerSL ℝ p) 0)
    (hs : ∀ᶠ h in 𝓝 0, g h-g 0≤u (riemannianExp x h)-u x) :
    p ∈ normalSubdifferential (n := n) u x := by
  intro ε hε
  filter_upwards [hasFDerivAt_affine_lower_support hg ε hε,hs] with h hh hk
  exact hh.trans hk

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

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_hull_norm_le_diam {v : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    ‖p‖≤Metric.diam (univ : Set M) := by
  have hs : activeLogs (n := n) v x ⊆
      Metric.closedBall (0 : TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M)) := by
    intro q hq
    rw [Metric.mem_closedBall,dist_zero_right,←hq.1]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (convexHull_min hs (convex_closedBall _ _)) hp

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_CompactConvexHullFinite
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

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

namespace WeakMTWTransport
lemma isCompact_convexHull_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  classical
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let F := fun (m : ℕ) (q : Convexity.StdSimplex ℝ (Fin m) × (Fin m → S)) =>
    ∑ i, q.1.weights i • (q.2 i).1
  have hF : ∀ m, Continuous (F m) := by
    intro m
    dsimp [F]
    apply continuous_finsetSum
    intro i _
    exact ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst).smul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  let C := fun m => range (F m)
  have hC : ∀ m, IsCompact (C m) := fun m => isCompact_range (hF m)
  have heq : convexHull ℝ S = ⋃ m≤Module.finrank ℝ E+1, C m := by
    ext x
    constructor
    · intro hx
      obtain ⟨ι,inst,z,w,hz,hi,hw,hsum,hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      let : Fintype ι := inst
      let e := Fintype.equivFin ι
      have hcard : Fintype.card ι≤Module.finrank ℝ E+1 :=
        hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      refine mem_iUnion₂.mpr ⟨Fintype.card ι,hcard,?_⟩
      let v : Convexity.StdSimplex ℝ (Fin (Fintype.card ι)) := {
        weights := Finsupp.equivFunOnFinite.symm (fun index => w (e.symm index))
        nonneg := fun index => (hw (e.symm index)).le
        total := by simpa [Finsupp.sum_fintype, e.symm.sum_comp] using hsum }
      let a : Fin (Fintype.card ι) → S := fun i => ⟨z (e.symm i),hz (mem_range_self _)⟩
      refine ⟨(v,a),?_⟩
      dsimp [F,v,a]
      exact (e.symm.sum_comp (fun i => w i • z i)).trans hx
    · intro hx
      obtain ⟨m,_,q,rfl⟩ := mem_iUnion₂.mp hx
      exact (convex_convexHull ℝ S).sum_mem (fun i _ => q.1.weights_nonneg i)
        q.1.total_of_fintype
        (fun i _ => subset_convexHull ℝ S (q.2 i).2)
  rw [heq]
  exact (finite_le_nat _).isCompact_biUnion (fun m _ => hC m)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SubgradientUpper
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma normalSubdifferential_directional_le {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈normalSubdifferential u x)
    (h : TangentSpace 𝓘(ℝ,Model n) x) {K : ℝ}
    (hK : ∀ᶠ t : ℝ in 𝓝 0, 0≤t → u (riemannianExp x (t • h))-u x≤K*t) :
    inner ℝ p h≤K := by
  by_contra hn
  have hdiff : 0 < inner ℝ p h-K := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (inner ℝ p h-K)/(2*(‖h‖+1))
  have hn1 : 0<‖h‖+1 := by positivity
  have hε : 0<ε := div_pos hdiff (mul_pos (by norm_num) hn1)
  have he : ε*(2*(‖h‖+1))=inner ℝ p h-K := div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hn1))
  have hc : Tendsto (fun t : ℝ => t • h) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t • h) 0 := continuousAt_id.smul continuousAt_const
    simpa only [zero_smul] using hc.tendsto
  have H := (hc.eventually (hp ε hε)).and hK
  obtain ⟨δ,hδ,Hδ⟩ := Metric.eventually_nhds_iff.mp H
  have ht : 0<δ/2 := by positivity
  have hh := Hδ (y := δ/2) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using (show δ/2<δ by linarith))
  have hb := hh.1.trans (hh.2 ht.le)
  rw [inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hb
  have hb' : (inner ℝ p h-ε*‖h‖)*(δ/2)≤K*(δ/2) := by nlinarith [hb]
  have Hbad := (mul_le_mul_iff_left₀ ht).mp hb'
  nlinarith [mul_pos hε hn1]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates3
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

section
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
lemma movingNormal_eq {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) (h : Model n) :
    movingNormal a (b,h) = riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) h) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  have hx : x ∈ (chartAt (Model n) a).source := by
    simpa only [x,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  change riemannianExp x (tangentCoordChange 𝓘(ℝ,Model n) a x x h) = _
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

lemma movingNormal_zero {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) :
    movingNormal a (b,0) = (extChartAt 𝓘(ℝ,Model n) a).symm b := by
  rw [movingNormal_eq hb,map_zero,riemannianExp_zero]

def movingNormalCost (a : M) (b p h : Model n) : ℝ :=
  cost (movingNormal a (b,h)) (movingNormal a (b,p))

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EnvelopeData
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
  {ι : Type*} [Fintype ι]

def scaledNormalEnvelope (a : M) (s : ℝ) (q : EnvelopeData (Model n) ι) (i : ι)
    (h : Model n) : ℝ :=
  (movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) h -
    movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) 0) -
  (q.2.2 / s) * (movingNormalCost a q.1.1 (s • q.1.2 i) h -
    movingNormalCost a q.1.1 (s • q.1.2 i) 0)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma scaledNormalEnvelope_zero (a : M) (s : ℝ) (q : EnvelopeData (Model n) ι) (i : ι) :
    scaledNormalEnvelope a s q i 0 = 0 := by simp [scaledNormalEnvelope]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_UniformEnvelope
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

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartFiberInverse_injective {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) :
    Function.Injective (chartFiberInverse a b) := by
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm b ∈ e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  rw [show (chartFiberInverse a b : Model n → _) =
      (e.continuousLinearEquivAt ℝ _ hx).symm from (e.symm_continuousLinearEquivAt_eq hx).symm]
  exact (e.continuousLinearEquivAt ℝ _ hx).symm.injective

end WeakMTWTransport

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

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma tangent_chart_symm_eq {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) (p : Model n) :
    (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm (b,p) =
      ⟨(extChartAt 𝓘(ℝ,Model n) a).symm b, chartFiberInverse a b p⟩ := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  have hx : x ∈ (chartAt (Model n) a).source := by
    simpa only [x,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  change (⟨x,tangentCoordChange 𝓘(ℝ,Model n) a x x p⟩ : TangentBundle 𝓘(ℝ,Model n) M) = _
  congr 1
  rw [chartFiberInverse,TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mem_active_coordinates {v : M → ℝ} {a : M} {K : Set M}
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source)
    {b p : Model n}
    (h : (b,p) ∈ (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
        {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K}) :
    b ∈ (extChartAt 𝓘(ℝ,Model n) a).target ∧
    chartFiberInverse a b p ∈ activeLogs v ((extChartAt 𝓘(ℝ,Model n) a).symm b) ∧
    (extChartAt 𝓘(ℝ,Model n) a).symm b ∈ K := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  obtain ⟨z,hz,he⟩ := h
  have hzS : z ∈ χ.source := (tangent_chart_source_iff _ z).mpr (hKa hz.2)
  have hbp : (b,p) ∈ χ.target := by
    rw [←he]
    exact χ.map_source hzS
  have hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target :=
    (tangent_chart_target_iff _ (b,p)).mp hbp
  have hzinv : χ.symm (b,p) = z := by
    rw [←he]
    exact χ.left_inv hzS
  have heq : (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,
      chartFiberInverse a b p⟩ : TangentBundle 𝓘(ℝ,Model n) M) = z := by
    exact (tangent_chart_symm_eq hb p).symm.trans hzinv
  refine ⟨hb,?_⟩
  have hh := congrArg (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
    z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K) heq
  exact hh.mpr hz

end CompactConfigurations

lemma compact_common_base_configurations {E : Type*} [TopologicalSpace E] [T2Space E]
    {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (E×E)} (hC : IsCompact C)
    (T : ℝ) :
    IsCompact {q : EnvelopeData E ι | (∀ i, (q.1.1, q.1.2 i) ∈ C) ∧
      (∀ i, 0 ≤ q.2.1 i) ∧ (∑ i, q.2.1 i = 1) ∧ q.2.2 ∈ Icc 0 T} := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let Q := {z : (ι → C) × (Convexity.StdSimplex ℝ ι × Icc (0:ℝ) T) |
    ∀ i, (z.1 i).1.1 = (z.1 i₀).1.1}
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hQ : IsCompact Q := by
    have he : Q = ⋂ i, {z : (ι → C) × (Convexity.StdSimplex ℝ ι × Icc (0:ℝ) T) |
        (z.1 i).1.1 = (z.1 i₀).1.1} := by ext; simp [Q]
    rw [he]
    exact (isClosed_iInter (fun i => isClosed_eq
      (continuous_fst.comp (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)))
      (continuous_fst.comp (continuous_subtype_val.comp ((continuous_apply i₀).comp continuous_fst))))).isCompact
  let F : ((ι → C) × (Convexity.StdSimplex ℝ ι × Icc (0:ℝ) T)) → EnvelopeData E ι :=
    fun z => (((z.1 i₀).1.1, fun i => (z.1 i).1.2),(z.2.1.weights,z.2.2.1))
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have he : F '' Q = {q : EnvelopeData E ι | (∀ i, (q.1.1, q.1.2 i) ∈ C) ∧
      (∀ i, 0 ≤ q.2.1 i) ∧ (∑ i, q.2.1 i = 1) ∧ q.2.2 ∈ Icc 0 T} := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,z.2.1.weights_nonneg,z.2.1.total_of_fintype,z.2.2.2⟩
      intro i
      change ((z.1 i₀).1.1,(z.1 i).1.2) ∈ C
      rw [←hz i]
      exact (z.1 i).2
    · rintro ⟨hc,hw,hsum,ht⟩
      let weights : Convexity.StdSimplex ℝ ι := {
        weights := Finsupp.equivFunOnFinite.symm q.2.1
        nonneg index := by simpa using hw index
        total := by simpa [Finsupp.sum_fintype] using hsum }
      refine ⟨(fun i => ⟨(q.1.1,q.1.2 i),hc i⟩,weights,⟨q.2.2,ht⟩),?_,?_⟩
      · intro i
        rfl
      · rfl
  rw [←he]
  exact hQ.image hF

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveUniformGrowth
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

def activeCoordinates (v : M → ℝ) (a : M) (K : Set M) : Set (Model n × Model n) :=
  (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
      {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K}

def activeConfiguration (v : M → ℝ) (a : M) (K : Set M) (T : ℝ) (ι : Type*) [Fintype ι] :=
  {q : EnvelopeData (Model n) ι | (∀ i, (q.1.1,q.1.2 i) ∈ activeCoordinates v a K) ∧
    (∀ i, 0 ≤ q.2.1 i) ∧ (∑ i, q.2.1 i = 1) ∧ q.2.2 ∈ Icc 0 T}

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveHullUniform
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

section
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingNormal_chart {a x : M} (hx : x ∈ (extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      tangentCoordChange 𝓘(ℝ,Model n) x a x p) = riemannianExp x p := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hs : (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) ∈ χ.source :=
    (tangent_chart_source_iff _ _).mpr hx
  change riemannianExp (χ.symm (χ ⟨x,p⟩)).1 (χ.symm (χ ⟨x,p⟩)).2 = _
  rw [χ.left_inv hs]

lemma movingNormal_trivialization {a x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p) =
        riemannianExp x p := by
  have hx' : x ∈ (chartAt (Model n) a).source := by simpa only [extChartAt_source] using hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx']
  exact movingNormal_chart hx p

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_EuclideanUpper
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
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma exists_hopfLax_minimizer {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z : M) :
    ∃ x, hopfLax t u z = u x+cost x z/t ∧
      ∀ a, u x+cost x z/t ≤ u a+cost a z/t := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hu.add ((continuous_cost_left z).div_const t)).continuousOn
  have hmin : ∀ a, u x+cost x z/t ≤ u a+cost a z/t := fun a => hx (mem_univ a)
  refine ⟨x,le_antisymm ?_ ?_,hmin⟩
  · exact csInf_le ⟨_,by rintro _ ⟨a,rfl⟩; exact hmin a⟩ ⟨x,rfl⟩
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨a,rfl⟩; exact hmin a)

lemma hopfLax_le {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z x : M) :
    hopfLax t u z ≤ u x+cost x z/t := by
  obtain ⟨a,ha,hmin⟩ := exists_hopfLax_minimizer hu t z
  rw [ha]
  exact hmin x

lemma hopfLax_eq_of_min {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z x : M)
    (hmin : ∀ a, u x+cost x z/t ≤ u a+cost a z/t) :
    hopfLax t u z = u x+cost x z/t := by
  apply le_antisymm (hopfLax_le hu t z x)
  obtain ⟨a,ha,_⟩ := exists_hopfLax_minimizer hu t z
  rw [ha]
  exact hmin a

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartCostJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner _root_.OAI.WeakMTWTransport.riemannianExp_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartCost_jet_continuous {a y : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,y)) :
    ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ (chartCost a q.2)) q.1) (z,y) ∧
    ∀ᶠ q : Model n×M in 𝓝 (z,y), ContDiffAt ℝ 2 (chartCost a q.2) q.1 := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let d := extChartAt 𝓘(ℝ,Model n) y
  let F : Model n → Model n → ℝ := fun b z => cost (χ.symm z) (d.symm b)
  have hdy : d.symm (d y)=y := d.left_inv (mem_extChartAt_source y)
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×Model n => χ.symm q.2) (d y,z) :=
    ((contMDiffWithinAt_extChartAt_symm_target a hz).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hz)).comp (d y,z) contDiffAt_snd.contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×Model n => d.symm q.1) (d y,z) :=
    ((contMDiffWithinAt_extChartAt_symm_target y
      (d.map_source (mem_extChartAt_source y))).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (d.map_source (mem_extChartAt_source y)))).comp
      (d y,z) contDiffAt_fst.contMDiffAt
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (d y,z) := by
    have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (χ.symm z,d.symm (d y)) := by simpa only [hdy] using hc
    exact (hc'.comp (d y,z) (hA.prodMk hB)).contDiffAt
  have hchart : ContinuousAt d y := continuousAt_extChartAt y
  have hq : ContinuousAt (fun q : Model n×M => (d q.2,q.1)) (z,y) :=
    (hchart.comp (x := (z,y)) (f := fun q : Model n×M => q.2) continuousAt_snd).prodMk continuousAt_fst
  have hnear : ∀ᶠ q : Model n×M in 𝓝 (z,y), q.2∈d.source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  have heq : ∀ᶠ q : Model n×M in 𝓝 (z,y), F (d q.2)=chartCost a q.2 := by
    filter_upwards [hnear] with q hq
    funext w
    dsimp [F,chartCost,χ]
    rw [d.left_inv hq]
  constructor
  · have H := (ContDiffAt.partial_snd_fderiv_two hF).continuousAt.comp
      (x := (z,y)) (f := fun q : Model n×M => (d q.2,q.1)) hq
    apply H.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    change fderiv ℝ (fderiv ℝ (chartCost a q.2)) q.1 =
      fderiv ℝ (fderiv ℝ (F (d q.2))) q.1
    rw [hq]
  · have H := (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hq.tendsto.eventually H,heq] with q hq he
    have H' := hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
    change ContDiffAt ℝ 2 (F (d q.2)) q.1 at H'
    rw [he] at H'
    exact H'

end

open Set Filter
open scoped Topology

lemma compact_eventually_fiberwise_bound {A X T F : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [T2Space X] [TopologicalSpace T]
    [NormedAddCommGroup F]
    {K : Set A} (hK : IsCompact K) {f : A → X} (hf : Continuous f)
    {g : T → X} {t : T} (hg : ContinuousAt g t) {h : T×A → F}
    (hh : ∀ a∈K, f a=g t → ContinuousAt h (t,a)) :
    ∃ B>0, ∀ᶠ s in 𝓝 t, ∀ a∈K, f a=g s → ‖h (s,a)‖≤B := by
  let S := K∩{a | f a=g t}
  have hS : IsCompact S := hK.inter_right (isClosed_eq hf continuous_const)
  have hcont : ContinuousOn (fun a => h (t,a)) S := by
    intro a ha
    exact ((hh a ha.1 ha.2).comp
      (x := a) (f := fun a => (t,a)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨max C 0+1,by positivity,?_⟩
  apply compact_eventually_fiberwise hK hf hg
  intro a ha he
  have haS : a∈S := ⟨ha,he⟩
  have hlt : ‖h (t,a)‖< max C 0+1 := lt_of_le_of_lt ((hC a haS).trans (le_max_left _ _)) (lt_add_one _)
  exact ((hh a ha he).norm.eventually_lt continuousAt_const hlt).mono (fun _ h => h.le)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_HopfGradient
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

omit [CompactSpace M] [Nonempty M] in
lemma cost_divided_triangle_two_times (x y z : M) {s t : ℝ} (hs : 0 < s) (ht : 0<t) :
    cost x z/(s+t) ≤ cost x y/s+cost y z/t := by
  have hst : 0 < s+t := add_pos hs ht
  have ha : 0 < s/(s+t) := div_pos hs hst
  have ha1 : s/(s+t)<1 := (div_lt_one hst).mpr (lt_add_of_pos_right s ht)
  have H := div_le_div_of_nonneg_right (divided_cost_triangle x y z ha ha1) hst.le
  calc
    _ ≤ _ := H
    _ = _ := by
      have he : 1-s/(s+t)=t/(s+t) := by field_simp <;> ring
      rw [he]
      field_simp

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mdifferentiableAt_of_chart_differentiable {f : M → ℝ} {x : M}
    (hd : DifferentiableAt ℝ (fun y => f ((extChartAt 𝓘(ℝ,Model n) x).symm y))
      (extChartAt 𝓘(ℝ,Model n) x x)) :
    MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x := by
  have H := hd.hasFDerivAt.hasMFDerivAt.comp x
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,Model n))
      (show x∈(chartAt (Model n) x).source from mem_chart_source _ _)).hasMFDerivAt
  apply (H.congr_of_eventuallyEq ?_).mdifferentiableAt
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) x] with y hy
  simp only [Function.comp_apply,(extChartAt 𝓘(ℝ,Model n) x).left_inv hy]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma riemannianGradient_eq_of_derivative {f : M → ℝ} {x : M}
    {v : TangentSpace 𝓘(ℝ,Model n) x}
    (h : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x (innerSL ℝ v)) :
    riemannianGradient (n := n) f x=v := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  rw [riemannianGradient,h.mfderiv]
  exact (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).symm_apply_apply v

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma modifiedScalar_contDiff {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B) (α D : ℝ) :
    ContDiff ℝ ∞ (modifiedScalar α D B) :=
  contDiff_snd.add (contDiff_fst.mul (hB.comp ((contDiff_snd.sub contDiff_const).div_const D)))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupport
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

def scalarCostSupport (φ : ℝ → ℝ) (v0 : ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x) (s : ℝ) (y : M) : ℝ :=
  φ (v0+cost x (riemannianExp x (s • p))/s-cost y (riemannianExp x (s • p))/s)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CoordinateScalarSupport
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

section
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateScalarSupport_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (v s : ℝ) (p z : Model n) (φ : ℝ → ℝ) :
    coordinateScalarSupport a φ (((v,s),(b,p)),z)=
      scalarCostSupport φ v ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p) s
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
  simp only [coordinateScalarSupport,scalarCostSupport,movingNormal_eq hb,map_smul]

lemma coordinateScalarSupport_self (a : M) (v s : ℝ) (b p : Model n) (φ : ℝ → ℝ) :
    coordinateScalarSupport a φ (((v,s),(b,p)),b)=φ v := by
  simp only [coordinateScalarSupport,add_sub_cancel_right]

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingPrefix
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

def movingPrefixChart (a c : M) (t : ℝ) (b p : Model n) : Model n :=
  extChartAt 𝓘(ℝ,Model n) c (movingPrefix a t b p)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingPrefix_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (t : ℝ) (p : Model n) :
    movingPrefix a t b p=riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
      (t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p) := by
  rw [movingPrefix,movingNormal_eq hb,map_smul]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_GraphCoordinates
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
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma graph_coordinate_reconstruction {a : M} {q : TangentBundle 𝓘(ℝ,Model n) M}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q),
      chartFiberInverse a (graphBaseCoordinate a q) (graphVelocityCoordinate a q)⟩ :
        TangentBundle 𝓘(ℝ,Model n) M)=q := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hs : q∈χ.source := (tangent_chart_source_iff _ _).mpr hq
  have hb : (χ q).1∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (tangent_chart_target_iff _ _).mp (χ.map_source hs)
  have H := χ.left_inv hs
  rw [tangent_chart_symm_trivialization hb] at H
  exact H

lemma movingPrefix_graph_coordinates {a : M} {q : TangentBundle 𝓘(ℝ,Model n) M}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).source) (t : ℝ) :
    movingPrefix a t (graphBaseCoordinate a q) (graphVelocityCoordinate a q)=
      riemannianExp q.1 (t • q.2) := by
  simp only [graphBaseCoordinate]
  rw [movingPrefix_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hq)]
  exact congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 (t • z.2))
    (graph_coordinate_reconstruction hq)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
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

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma hasMFDerivAt_riemannianGradient {f : M → ℝ} {x : M}
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x
      (innerSL ℝ (riemannianGradient (n := n) f x)) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  apply hd.hasMFDerivAt.congr_mfderiv
  exact ((InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).apply_symm_apply _).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def chartGradientVector (a : M) (z : Model n) (L : Model n →L[ℝ] ℝ) :
    TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm z) :=
  (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
    ((extChartAt 𝓘(ℝ,Model n) a).symm z) ((riemannianCoordinateMetric a z).inverse L)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateBackward_eq_exp_chartGradient {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) (L : Model n →L[ℝ] ℝ) :
    coordinateBackward a (-1,z,L)=riemannianExp
      ((extChartAt 𝓘(ℝ,Model n) a).symm z) (chartGradientVector a z L) := by
  rw [coordinateBackward,neg_neg,one_smul,movingNormal_eq hz]
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupportFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev centerRowParameter (c : M) (v : M → ℝ) (γ l : ℝ) (x r : Model n) :=
  (γ,((v ((extChartAt 𝓘(ℝ,Model n) c).symm x),(1+l)/2),(x,r)))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDerivative
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateContact (a b : M) (q : Model n × (Model n →L[ℝ] ℝ)) : Model n :=
  extChartAt 𝓘(ℝ,Model n) b (coordinateBackward a (-1,q.1,q.2))

end ContactDerivative
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactRelationChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section ContactRelationChart
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

def chartContactRelation (a b : M) (u v : M → ℝ) (T : Set M)
    (z q : Model n) : Prop :=
  q∈(extChartAt 𝓘(ℝ,Model n) b).target ∧
  (extChartAt 𝓘(ℝ,Model n) b).symm q∈T ∧
  contactGap u v ((extChartAt 𝓘(ℝ,Model n) a).symm z)
    ((extChartAt 𝓘(ℝ,Model n) b).symm q)=0

end ContactRelationChart
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SmoothTestPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section SmoothTestPDE
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def chartTestContact (a b : M) (φ : Model n → ℝ) (w : Model n) : Model n :=
  coordinateContact a b (w,fderiv ℝ φ w)

end SmoothTestPDE
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactStationarity
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

def chartCostCovector (a b : M) (q : Model n×Model n) : Model n →L[ℝ] ℝ :=
  fderiv ℝ (chartCost a ((extChartAt 𝓘(ℝ,Model n) b).symm q.2)) q.1

end ContactStationarity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_LocalCEMS
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def NormalAlexandrovContact (v : M → ℝ) (x : M)
    (p : TangentSpace 𝓘(ℝ,Model n) x)
    (A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) : Prop :=
  p∈activeLogs (n := n) v x ∧ p∈injectivityDomain x ∧
  (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
  HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDifferential
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_UniformJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteExpJac (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def expJacobian (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  (show TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p) from
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp (n := n) x) p).toLinearMap.normDet

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_IntrinsicJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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
section IntrinsicJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteIntrinsicJacobian (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def chartJacobian (a x : M) : ℝ :=
  let F : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a) x
  F.toLinearMap.normDet

end IntrinsicJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_LocalCEMS2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section LocalCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_2 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

end LocalCEMS
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitLogInjective
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
section ExpCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateEndpoint (c : TangentBundle 𝓘(ℝ,Model n) M) (q : Model n×Model n) : Model n :=
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
    (riemannianExp (χ.symm q).1 (χ.symm q).2)

def coordinateEndpointVertical (c z : TangentBundle 𝓘(ℝ,Model n) M) : Model n →L[ℝ] Model n :=
  (fderiv ℝ (coordinateEndpoint c)
    (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c z)).comp (inr ℝ (Model n) (Model n))

end ExpCoordinates
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameMetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def frameMetric (a:M) (b:Model n) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (movingPrefixEnergy a 1 b)) 0

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ChartTrueMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def chartJetMatrix (a c:M) (b q:Model n) (p:Model n →L[ℝ] ℝ)
    (A:Model n →L[ℝ] Model n →L[ℝ] ℝ) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  frameMetric a b+secondJetPullback p A (fderiv ℝ (movingPrefixChart a c 1 b) q)
    (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 b)) q)

end ChartTrueMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_CotangentFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev Phase (n:ℕ) := Model n × (Model n →L[ℝ] ℝ)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter Manifold Bundle
open scoped Topology ContDiff

section CompactEnvelopes
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma continuous_modifiedDatum {v : M → ℝ} (hv : Continuous v) (a D b : ℝ)
    {B : ℝ → ℝ} (hB : Continuous B) : Continuous (modifiedDatum v a D b B) :=
  hv.add (continuous_const.mul (hB.comp ((hv.sub continuous_const).div_const D)))

end CompactEnvelopes

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterRayLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CenterRayLimit
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

def chartRay (c:M) (b r:Model n) : TangentBundle 𝓘(ℝ,Model n) M :=
  ⟨(extChartAt 𝓘(ℝ,Model n) c).symm b,chartFiberInverse c b r⟩

end CenterRayLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumActiveLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumActiveLimits
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ}
  {α D bminus bplus : ℝ}
  {Bc Bo : ℝ → ℝ}
  {hmtw : WeakMTW (n := n) (M := M)}
  {hv : Continuous v}
  {ho : Continuous Bo}
  {a c : M}
  {N : Set (Model n)}

local instance activeLimitDualGroup : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance activeLimitDualSpace : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance

end MaximumActiveLimits
end WeakMTWTransport

end
end

end OAI
end


