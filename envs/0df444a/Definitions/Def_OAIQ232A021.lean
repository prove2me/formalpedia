-- Prove2me | Definitions.Def_OAIQ232A021
-- name    : OAIQ232A021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:03:07.468819+00:00
-- url     : https://prove2.me/theorems/2881e5d7-895a-4d81-b54f-8110247391e7
-- title:
--   Definitions bundle OAIQ232A021 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 23 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_LocalCostGradient`, `BiholderTransport_Calculus_LocalMetricGradient`, `BiholderTransport_Coordinates_ExpNonconjugacy`, `BiholderTransport_Coordinates_JointNormalChart`, `BiholderTransport_Geodesics_GeodesicExistence`, `BiholderTransport_Geodesics_MetricCurveLocal`, `BiholderTransport_Geodesics_MetricCurveSpeed`, `BiholderTransport_Geodesics_MetricGeodesicLift`, `BiholderTransport_Geodesics_ShortGradient`, `BiholderTransport_Geodesics_SprayDistanceBound`, `BiholderTransport_Geodesics_SprayMinimizing`, `BiholderTransport_LocalFlow_LocalMetricNormal`, `BiholderTransport_LocalFlow_NormalFlow`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A010`, `OAIQ232A014` and `OAIQ232A019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A022` and `OAIQ232A023`.
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
import Definitions.Def_OAIQ232A010
import Definitions.Def_OAIQ232A014
import Definitions.Def_OAIQ232A019

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_LocalMetricNormal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma riemannian_normal_chart_dist_lower
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {c : M}
    (hmetric : ∀ z ∈ S, ∀ u v : E, g z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) v))
    {Ψ W : ℝ × E → E} {r : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hW : ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (himg : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo (-r) r)
    (hΨ0 : ∀ v ∈ Metric.ball 0 r, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 r, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) (hτnonneg : 0 ≤ τ)
    (e : OpenPartialHomeomorph E E) (hef : (e : E → E) = fun v => Ψ (τ,v))
    (hes : 0 ∈ e.source) (hesub : e.source ⊆ Metric.ball 0 r)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {a y : M} (he0 : e 0 = extChartAt 𝓘(ℝ,E) c a)
    {δ : ℝ} (hball : Metric.ball a δ ⊆
      (extChartAt 𝓘(ℝ,E) c).source ∩ (extChartAt 𝓘(ℝ,E) c) ⁻¹' e.target)
    (hdist : dist a y < δ) :
    τ * Real.sqrt (g x (e.symm (extChartAt 𝓘(ℝ,E) c y))
      (e.symm (extChartAt 𝓘(ℝ,E) c y))) ≤ dist a y := by
  apply riemannian_local_dist_lower_bound (I := 𝓘(ℝ,E)) hball hdist
  intro γ hγ hγ0 hγ1 hγimg
  let η : ℝ → E := (extChartAt 𝓘(ℝ,E) c) ∘ γ
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (n := 1) (x := c)).comp hγ (fun t ht => by
        change γ t ∈ (chartAt E c).source
        simpa only [extChartAt_source] using (hγimg ht).1))
  have hηimg : MapsTo η (Icc 0 1) e.target := fun t ht => (hγimg ht).2
  have hηS : ∀ t ∈ Icc 0 1, η t ∈ S := by
    intro t ht
    have hh := himg τ hτ (e.symm (η t)) (hesub (e.map_target (hηimg ht)))
    have hval := congrFun hef (e.symm (η t))
    rw [←hval,e.right_inv (hηimg ht)] at hh
    exact hh
  have hb := coordinate_normal_chart_radial_bound hS hg hpos hsym hΨ hW himg hode
    h0 hΨ0 hW0 hτ hτnonneg e hef hes hesub hed hei (by norm_num : (0:ℝ) ≤ 1)
    hη hηimg (by simp only [η,Function.comp_apply,hγ0,he0])
  have hlen := coordinate_path_length hγ (fun t ht => (hγimg ht).1) g (by
    intro t ht u v
    have hh := hmetric (η t) (hηS t ht) u v
    have hinner := congrArg (fun z : M =>
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ z u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ z v))
        ((extChartAt 𝓘(ℝ,E) c).left_inv (hγimg ht).1)
    exact hh.trans hinner)
  rw [hlen]
  simpa only [η,Function.comp_apply,hγ1] using hb

lemma riemannian_coordinate_normal_chart_dist
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {c : M} (hSto : S ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hmetric : ∀ z ∈ S, ∀ u v : E, g z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) v))
    {Ψ W : ℝ × E → E} {r : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hW : ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (himg : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {a y : M} (h0 : 0 ∈ Ioo (-r) r)
    (hΨ0 : ∀ v ∈ Metric.ball 0 r, Ψ (0,v) = extChartAt 𝓘(ℝ,E) c a)
    (hW0 : ∀ v ∈ Metric.ball 0 r, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) (hτnonneg : 0 ≤ τ)
    (e : OpenPartialHomeomorph E E) (hef : (e : E → E) = fun v => Ψ (τ,v))
    (he0 : e 0 = extChartAt 𝓘(ℝ,E) c a)
    (hes : 0 ∈ e.source) (hesub : e.source ⊆ Metric.ball 0 r)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {δ : ℝ} (hball : Metric.ball a δ ⊆
      (extChartAt 𝓘(ℝ,E) c).source ∩ (extChartAt 𝓘(ℝ,E) c) ⁻¹' e.target)
    (hdist : dist a y < δ) :
    dist a y = τ * Real.sqrt (g (extChartAt 𝓘(ℝ,E) c a)
      (e.symm (extChartAt 𝓘(ℝ,E) c y)) (e.symm (extChartAt 𝓘(ℝ,E) c y))) := by
  apply le_antisymm _ (riemannian_normal_chart_dist_lower hS hg hpos hsym hmetric
    hΨ hW himg hode h0 hΨ0 hW0 hτ hτnonneg e hef hes hesub hed hei he0 hball hdist)
  have hδ : 0 < δ := dist_nonneg.trans_lt hdist
  have ha := hball (Metric.mem_ball_self hδ)
  have hy := hball (show y ∈ Metric.ball a δ by simpa only [Metric.mem_ball,dist_comm] using hdist)
  let v := e.symm (extChartAt 𝓘(ℝ,E) c y)
  have hv : v ∈ Metric.ball 0 r := hesub (e.map_target hy.2)
  let η : ℝ → E := fun t => Ψ (t,v)
  have hη : ContDiffOn ℝ ∞ η (Ioo (-r) r) :=
    hΨ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => ⟨ht,hv⟩)
  have hsub : Icc 0 τ ⊆ Ioo (-r) r := fun t ht => ⟨h0.1.trans_le ht.1,ht.2.trans_lt hτ.2⟩
  have hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1
      ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) (Icc 0 τ) :=
    (contMDiffOn_extChartAt_symm (n := 1) c).comp
      (contMDiffOn_iff_contDiffOn.mpr ((hη.mono hsub).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
      (fun t ht => hSto (himg t (hsub ht) v hv))
  have hγ0 : ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) 0 = a := by
    simp only [Function.comp_apply,η,hΨ0 v hv,(extChartAt 𝓘(ℝ,E) c).left_inv ha.1]
  have hγτ : ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) τ = y := by
    have heq := congrFun hef v
    simp only [Function.comp_apply,η,←heq,v,e.right_inv hy.2,
      (extChartAt 𝓘(ℝ,E) c).left_inv hy.1]
  have hh := riemannianEDist_le_pathELength (I := 𝓘(ℝ,E)) hγ hγ0 hγτ hτnonneg
  rw [←IsRiemannianManifold.out,edist_dist] at hh
  have hlen := coordinate_flow_path_length hS hg hpos hsym hSto hmetric hη
    (fun t ht => himg t ht v hv) (fun t ht => hode t ht v hv) hτnonneg hτ.2
  rw [hlen] at hh
  have hc : 0 ≤ τ * Real.sqrt (g (extChartAt 𝓘(ℝ,E) c a) v v) := mul_nonneg hτnonneg (Real.sqrt_nonneg _)
  have hh' : ENNReal.ofReal (dist a y) ≤
      ENNReal.ofReal (τ * Real.sqrt (g (extChartAt 𝓘(ℝ,E) c a) v v)) := by
    simpa only [η,hΨ0 v hv,hW0 v hv] using hh
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp hh'

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_JointNormalChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_uniform_metric_normal_coordinates (a : M) :
    ∃ δ r τ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < τ ∧ τ < r ∧
    ∃ Φ : ℝ × (E × E) → E × E,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r) ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r, Φ (0,z) = z) ∧
      (∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r,
        (Φ (t,z)).1 ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
        HasDerivAt (fun q => Φ (q,z))
          (coordinateGeodesicField (riemannianCoordinateMetric a) (Φ (t,z))) t) ∧
      (e : (E × E) → (E × E)) = (fun z => (z.1,(Φ (τ,z)).1)) ∧
      e.source ⊆ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (Metric.ball a δ ⊆ (extChartAt 𝓘(ℝ,E) a).source) ∧
      (∀ b ∈ Metric.ball a δ, (extChartAt 𝓘(ℝ,E) a b,0) ∈ e.source) ∧
      (∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
        (extChartAt 𝓘(ℝ,E) a b,extChartAt 𝓘(ℝ,E) a y) ∈ e.target) ∧
      (∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ, ∀ v : E,
        (extChartAt 𝓘(ℝ,E) a b,v) ∈ e.source →
        (Φ (τ,(extChartAt 𝓘(ℝ,E) a b,v))).1 = extChartAt 𝓘(ℝ,E) a y →
        dist b y = τ * Real.sqrt (riemannianCoordinateMetric a
          (extChartAt 𝓘(ℝ,E) a b) v v)) := by
  let c := extChartAt 𝓘(ℝ,E) a
  let g := riemannianCoordinateMetric (E := E) a
  have hS : IsOpen c.target := isOpen_extChartAt_target a
  have hg : ContDiffOn ℝ ∞ g c.target := contDiffOn_riemannianCoordinateMetric a
  have hpos : ∀ x ∈ c.target, ∀ v : E, v ≠ 0 → 0 < g x v v :=
    fun _ hx _ hv => riemannianCoordinateMetric_positive hx hv
  have hsym : ∀ x ∈ c.target, ∀ u v : E, g x u v = g x v u :=
    fun x _ u v => riemannianCoordinateMetric_symm a x u v
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hode,τ,hτ,hτr,e,he,hes,hesub,hed,hei⟩ :=
    exists_joint_smooth_normal_chart hS hg hpos hsym (mem_extChartAt_target a)
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have hepres : ∀ z : E × E, (e z).1 = z.1 := by
    intro z
    rw [he]
  have hzero : ∀ x ∈ Metric.ball (c a) r, (Φ (τ,(x,0))).1 = x := by
    intro x hx
    have hz : (x,(0:E)) ∈ Metric.ball (c a,0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hx hr
    have hz0 := hΦ0 (x,0) hz
    have hh := coordinate_geodesic_zero_velocity
      (fun t ht => (hg.contDiffAt (hS.mem_nhds (hode t ht (x,0) hz).1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (fun t ht => metricDual_isInvertible _ (hpos _ (hode t ht (x,0) hz).1))
      (fun t ht => hpos _ (hode t ht (x,0) hz).1)
      (fun t ht => hsym _ (hode t ht (x,0) hz).1)
      (fun t ht => (hode t ht (x,0) hz).2) h0
      (show (Φ (0,(x,0))).2 = 0 from congrArg Prod.snd hz0) ht
    exact hh.1.trans (congrArg Prod.fst hz0)
  have hediag : e (c a,0) = (c a,c a) := by
    rw [he]
    exact Prod.ext rfl (hzero _ (Metric.mem_ball_self hr))
  have hat : (c a,c a) ∈ e.target := hediag ▸ e.map_source hes
  have hc : ContinuousAt c a := continuousAt_extChartAt a
  have hn₁ : {p : M × M | p.1 ∈ c.source ∧ p.2 ∈ c.source} ∈ 𝓝 (a,a) :=
    inter_mem (continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a)))
      (continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a)))
  have hn₂ : {p : M × M | (c p.1,0) ∈ e.source} ∈ 𝓝 (a,a) :=
    ((hc.comp continuousAt_fst).prodMk continuousAt_const).preimage_mem_nhds
      (e.open_source.mem_nhds hes)
  have hn₃ : {p : M × M | (c p.1,c p.2) ∈ e.target} ∈ 𝓝 (a,a) :=
    ((hc.comp continuousAt_fst).prodMk (hc.comp continuousAt_snd)).preimage_mem_nhds
      (e.open_target.mem_nhds hat)
  obtain ⟨R,hR,hgood⟩ := Metric.mem_nhds_iff.mp (inter_mem hn₁ (inter_mem hn₂ hn₃))
  have hgood' : ∀ b ∈ Metric.ball a R, ∀ y ∈ Metric.ball a R,
      b ∈ c.source ∧ y ∈ c.source ∧ (c b,0) ∈ e.source ∧ (c b,c y) ∈ e.target := by
    intro b hb y hy
    have hh := hgood (show (b,y) ∈ Metric.ball (a,a) R by
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hb hy)
    exact ⟨hh.1.1,hh.1.2,hh.2.1,hh.2.2⟩
  let δ := R/4
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hδR : δ < R := by dsimp [δ] <;> linarith
  have hballR : Metric.ball a δ ⊆ Metric.ball a R := Metric.ball_subset_ball hδR.le
  refine ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,?_,he,hesub,hed,hei,?_,?_,?_,?_⟩
  · intro t ht z hz
    exact ⟨(hode t ht z hz).1,(hode t ht z hz).2.1.prodMk (hode t ht z hz).2.2⟩
  · intro b hb
    exact (hgood' b (hballR hb) a (Metric.mem_ball_self hR)).1
  · intro b hb
    exact (hgood' b (hballR hb) a (Metric.mem_ball_self hR)).2.2.1
  · intro b hb y hy
    exact (hgood' b (hballR hb) y (hballR hy)).2.2.2
  · intro b hb y hy v hv hval
    let f := fiberwiseHomeomorph e hepres (c b)
    have hbg := hgood' b (hballR hb) a (Metric.mem_ball_self hR)
    have hcb : c b ∈ Metric.ball (c a) r := by
      exact (max_lt_iff.mp (show max (dist (c b) (c a)) (dist (0:E) 0) < r
        from hesub hbg.2.2.1)).1
    have hball : ∀ w ∈ Metric.ball (0:E) r, (c b,w) ∈ Metric.ball (c a,0) r := by
      intro w hw
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hcb hw
    have hΦb : ContDiffOn ℝ ∞ (fun z : ℝ × E => Φ (z.1,(c b,z.2)))
        (Ioo (-r) r ×ˢ Metric.ball 0 r) :=
      hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
        (fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
    have hf : (f : E → E) = (fun w => (Φ (τ,(c b,w))).1) := by
      funext w
      change (e (c b,w)).2 = _
      rw [he]
    have hfb : Metric.ball b (2*δ) ⊆ c.source ∩ c ⁻¹' f.target := by
      intro z hz
      have hzR : z ∈ Metric.ball a R := by
        have ht' := dist_triangle z b a
        have hb' : dist b a < δ := hb
        have hz' : dist z b < 2*δ := hz
        change dist z a < R
        dsimp [δ] at *
        linarith
      have hh := hgood' b (hballR hb) z hzR
      exact ⟨hh.2.1,hh.2.2.2⟩
    have hby : dist b y < 2*δ := by
      have ht' := dist_triangle b a y
      have hb' : dist b a < δ := hb
      have hy' : dist a y < δ := by simpa only [Metric.mem_ball,dist_comm] using hy
      linarith
    have hnorm := riemannian_coordinate_normal_chart_dist hS hg hpos hsym (Subset.refl _)
      (fun _ _ _ _ => rfl) hΦb.fst hΦb.snd
      (fun t ht w hw => (hode t ht (c b,w) (hball w hw)).1)
      (fun t ht w hw => (hode t ht (c b,w) (hball w hw)).2) h0
      (fun w hw => (congrArg Prod.fst (hΦ0 (c b,w) (hball w hw)) : _ = c b))
      (fun w hw => congrArg Prod.snd (hΦ0 (c b,w) (hball w hw))) ht hτ.le f hf
      (by rw [hf]; exact hzero _ hcb) hbg.2.2.1
      (fun w hw => (max_lt_iff.mp (show max (dist (c b) (c a)) (dist w 0) < r
        from hesub hw)).2)
      (fiberwiseHomeomorph_contDiffOn hepres (c b) hed)
      (fiberwiseHomeomorph_symm_contDiffOn hepres (c b) hei) hfb hby
    have hv' : f.symm (c y) = v := by
      have hfval : f v = c y := by rw [hf]; exact hval
      rw [←hfval]
      exact f.left_inv hv
    rw [hv'] at hnorm
    exact hnorm

end WeakMTWTransport
open Set

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LocalMetricGradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_metric_gradient (a : M) :
    ∃ δ τ : ℝ, 0 < δ ∧ 0 < τ ∧
      Metric.ball a δ ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      ∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
      ∃ z : TangentBundle 𝓘(ℝ,E) M,
        z.1 = b ∧ (sprayFlow τ z).1 = y ∧ dist b y = τ * ‖z.2‖ ∧
        HasFDerivAt (fun w : E => dist b ((extChartAt 𝓘(ℝ,E) a).symm w)^2 / 2)
          (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a y)
            ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E))
              (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) (sprayFlow τ z)).2))
          (extChartAt 𝓘(ℝ,E) a y) := by
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,hode,he,hesub,hed,hei,hsrc,hdiag,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  refine ⟨δ,τ,hδ,hτ,hsrc,?_⟩
  intro b hb y hy
  let c := extChartAt 𝓘(ℝ,E) a
  let A : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) A
  let g := riemannianCoordinateMetric (E := E) a
  have hp : ∀ z : E × E, (e z).1 = z.1 := by intro z; rw [he]
  let f := fiberwiseHomeomorph e hp (c b)
  let v := f.symm (c y)
  have hyt : c y ∈ f.target := htarget b hb y hy
  have hvs : v ∈ f.source := f.map_target hyt
  have hcb : dist (c b) (c a) < r :=
    (max_lt_iff.mp (show max (dist (c b) (c a)) (dist (0:E) 0) < r from hesub (hdiag b hb))).1
  have hball : ∀ w ∈ Metric.ball (0:E) r, (c b,w) ∈ Metric.ball (c a,0) r := by
    intro w hw
    exact max_lt hcb hw
  have hv : v ∈ Metric.ball (0:E) r :=
    (max_lt_iff.mp (show max (dist (c b) (c a)) (dist v 0) < r from hesub hvs)).2
  let Ψ : ℝ × E → E := fun z => (Φ (z.1,(c b,z.2))).1
  let W : ℝ × E → E := fun z => (Φ (z.1,(c b,z.2))).2
  have hΦc := hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    (show MapsTo (fun z : ℝ × E => (z.1,(c b,z.2)))
      (Ioo (-r) r ×ˢ Metric.ball 0 r) (Ioo (-r) r ×ˢ Metric.ball (c a,0) r) from
      fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
  have hf : (f : E → E) = fun w => Ψ (τ,w) := by
    funext w
    change (e (c b,w)).2 = _
    rw [he]
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have hΨv : Ψ (τ,v) = c y := (congrFun hf v).symm.trans (f.right_inv hyt)
  have hG : ∀ w : E, g (c y) (W (τ,v)) (fderiv ℝ f v w) = τ*g (c b) v w := by
    intro w
    rw [hf,←hΨv]
    exact coordinate_endpoint_gauss (Ψ := Ψ) (W := W) (x := c b) (g := g)
      (isOpen_extChartAt_target a)
      (contDiffOn_riemannianCoordinateMetric a)
      (fun _ hx => riemannianCoordinateMetric_isInvertible hx)
      (fun x _ u v => riemannianCoordinateMetric_symm a x u v)
      (show ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r) from hΦc.fst)
      (show ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r) from hΦc.snd)
      (fun t ht w hw => (hode t ht (c b,w) (hball w hw)).1)
      (fun t ht w hw => ⟨((hode t ht (c b,w) (hball w hw)).2).fst,
        ((hode t ht (c b,w) (hball w hw)).2).snd⟩) h0
      (fun w hw => congrArg Prod.fst (hΦ0 (c b,w) (hball w hw)))
      (fun w hw => congrArg Prod.snd (hΦ0 (c b,w) (hball w hw))) ht hv w
  have hfd := ((fiberwiseHomeomorph_contDiffOn hp (c b) hed).contDiffAt
    (f.open_source.mem_nhds hvs)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfi := ((fiberwiseHomeomorph_symm_contDiffOn hp (c b) hei).contDiffAt
    (f.open_target.mem_nhds hyt)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD := normal_action_hasFDerivAt f hyt hfd hfi (g (c b)) (g (c y))
    (riemannianCoordinateMetric_symm a (c b)) (W (τ,v)) τ hG
  have hnear : ∀ᶠ w : E in 𝓝 (c y), w ∈ c.target ∧ c.symm w ∈ Metric.ball a δ := by
    have hcy : c y ∈ c.target := c.map_source (hsrc hy)
    have hynear := ((continuousOn_extChartAt_symm a).continuousAt ((isOpen_extChartAt_target a).mem_nhds hcy)).preimage_mem_nhds
      (by rw [c.left_inv (hsrc hy)]; exact Metric.isOpen_ball.mem_nhds hy)
    filter_upwards [(isOpen_extChartAt_target a).mem_nhds hcy, hynear] with w hw hwy
    exact ⟨hw,hwy⟩
  have hdistEq : (fun w : E => dist b (c.symm w)^2/2) =ᶠ[𝓝 (c y)]
      (fun w => (τ^2/2)*g (c b) (f.symm w) (f.symm w)) := by
    filter_upwards [hnear] with w hw
    have hwt : w ∈ f.target := by
      change (c b,w) ∈ e.target
      have hh : (c b,c (c.symm w)) ∈ e.target := htarget b hb (c.symm w) hw.2
      simpa only [c.right_inv hw.1] using hh
    have hh := hdist b hb (c.symm w) hw.2 (f.symm w) (f.map_target hwt)
      (show (Φ (τ,(c b,f.symm w))).1 = c (c.symm w) by
        rw [c.right_inv hw.1]
        exact (congrFun hf _).symm.trans (f.right_inv hwt))
    have hn : 0 ≤ g (c b) (f.symm w) (f.symm w) := by
      by_cases hh : f.symm w = 0
      · simp only [hh,map_zero,le_refl]
      · exact (riemannianCoordinateMetric_positive (c.map_source (hsrc hb)) hh).le
    rw [hh,mul_pow,Real.sq_sqrt hn]
    ring
  let z := χ.symm (c b,v)
  have hzt : (c b,v) ∈ χ.target := (tangent_chart_target_iff A _).mpr (c.map_source (hsrc hb))
  have hzchart : χ z = (c b,v) := χ.right_inv hzt
  have hzsrc : z ∈ χ.source := χ.map_target hzt
  have hzb : z.1 = b := by
    have hh := congrArg Prod.fst hzchart
    rw [tangent_chart_apply] at hh
    exact c.injOn ((tangent_chart_source_iff A z).mp hzsrc) (hsrc hb) hh
  have hflow := sprayFlow_eq_coordinate_curve A hr
    (fun t ht' => (hode t ht' (c b,v) (hball v hv)).1)
    (fun t ht' => (hode t ht' (c b,v) (hball v hv)).2)
    (show χ.symm (Φ (0,(c b,v))) = z by rw [hΦ0 (c b,v) (hball v hv)]) ht
  have hflowchart : χ (sprayFlow τ z) = Φ (τ,(c b,v)) := by
    rw [hflow,χ.right_inv ((tangent_chart_target_iff A _).mpr (hode τ ht (c b,v) (hball v hv)).1)]
  have hflowsrc : sprayFlow τ z ∈ χ.source := by
    rw [hflow]
    exact χ.map_target ((tangent_chart_target_iff A _).mpr (hode τ ht (c b,v) (hball v hv)).1)
  have hfy : (sprayFlow τ z).1 = y := by
    apply c.injOn ((tangent_chart_source_iff A _).mp hflowsrc) (hsrc hy)
    exact (congrArg Prod.fst (tangent_chart_apply A (sprayFlow τ z))).symm.trans
      ((congrArg Prod.fst hflowchart).trans hΨv)
  refine ⟨z,hzb,hfy,?_,?_⟩
  · have hh := hdist b hb y hy v hvs hΨv
    have hn := coordinate_spray_energy A z ((tangent_chart_source_iff A z).mp hzsrc)
    rw [hzchart] at hn
    rw [hh,hn,Real.sqrt_sq (norm_nonneg _)]
  · have hh := hD.congr_of_eventuallyEq hdistEq
    rw [show (χ (sprayFlow τ z)).2 = W (τ,v) from congrArg Prod.snd hflowchart]
    exact hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LocalCostGradient
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_cost_gradient (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
      ∃ q : TangentBundle 𝓘(ℝ,E) M,
        q.1 = y ∧ ‖q.2‖ = dist b y ∧ (sprayFlow (-1) q).1 = b ∧
        HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun x => dist b x ^ 2 / 2) q.1 (innerSL ℝ q.2) := by
  obtain ⟨δ,τ,hδ,hτ,hsrc,H⟩ := exists_local_metric_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro b hb y hy
  obtain ⟨z,hzb,hzy,hn,hD⟩ := H b hb y hy
  have hzs : (sprayFlow τ z).1 ∈ (extChartAt 𝓘(ℝ,E) a).source := hzy ▸ hsrc hy
  have hDc : HasFDerivAt (fun w : E => dist b ((extChartAt 𝓘(ℝ,E) a).symm w)^2 / 2)
      (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a (sprayFlow τ z).1)
        ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E))
          (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) (sprayFlow τ z)).2))
      (extChartAt 𝓘(ℝ,E) a (sprayFlow τ z).1) := by rwa [hzy]
  have hD' := hasMFDerivAt_of_coordinate_gradient (sprayFlow τ z) hzs
    (fun x => dist b x^2/2) τ hDc
  refine ⟨tangentScale τ (sprayFlow τ z),hzy,?_,?_,?_⟩
  · change ‖τ • (sprayFlow τ z).2‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hτ,sprayFlow_speed]
    exact hn.symm
  · rw [sprayFlow_scale,show τ * (-1) = -τ by ring,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]
    exact hzb
  · exact hD'.congr_mfderiv (map_smul (innerSL ℝ) τ (sprayFlow τ z).2).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayMinimizing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_locally_minimizing (z : TangentBundle 𝓘(ℝ,E) M) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ, |s-t₀| < ε → |u-t₀| < ε →
      dist (sprayFlow s z).1 (sprayFlow u z).1 = |s-u| * ‖z.2‖ := by
  let γ := fun t => sprayFlow t z
  let a := γ t₀
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let cM := extChartAt 𝓘(ℝ,E) a.1
  let q := χ ∘ γ
  have hγ := (sprayFlow_curve z).isMIntegralCurveAt t₀
  have hγc : ContinuousAt (fun t => (γ t).1) t₀ :=
    (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt.comp
      hγ.continuousAt
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,_,hΦ0,hΦode,_,hesub,_,_,hδsrc,hediag,_,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a.1
  have hnear : ∀ᶠ s in 𝓝 t₀, (γ s).1 ∈ Metric.ball a.1 δ :=
    hγc.preimage_mem_nhds (Metric.ball_mem_nhds _ hδ)
  have hode : ∀ᶠ s in 𝓝 t₀,
      (γ s).1 ∈ Metric.ball a.1 δ ∧
      HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q s)) s := by
    filter_upwards [hnear,hγ.eventually_hasDerivAt] with s hs hd
    rw [geodesicSpray_coordinates a (γ s) (hδsrc hs)] at hd
    exact ⟨hs,hd⟩
  obtain ⟨h,hh,hN⟩ := Metric.mem_nhds_iff.mp hode
  have hN' : ∀ s : ℝ, |s-t₀| < h → (γ s).1 ∈ Metric.ball a.1 δ ∧
      HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q s)) s := by
    intro s hs
    exact hN (show s ∈ Metric.ball t₀ h by simpa only [Metric.mem_ball,Real.dist_eq] using hs)
  have hqc : ContinuousAt q t₀ := (spray_chart_hasDerivAt hγ).continuousAt
  let K : ℝ × ℝ → E × E := fun p => ((q p.1).1,((p.2-p.1)/τ) • (q p.1).2)
  have hqp : ContinuousAt (fun p : ℝ × ℝ => q p.1) (t₀,t₀) :=
    ContinuousAt.comp (g := q) (f := (Prod.fst : ℝ × ℝ → ℝ)) hqc continuousAt_fst
  have hscale : ContinuousAt (fun p : ℝ × ℝ => (p.2-p.1)/τ) (t₀,t₀) :=
    (continuousAt_snd.sub continuousAt_fst).div_const τ
  have hK : ContinuousAt K (t₀,t₀) := hqp.fst.prodMk (hscale.smul hqp.snd)
  have hKt : K (t₀,t₀) ∈ e.source := by
    simpa only [K,sub_self,zero_div,zero_smul,q,χ,Function.comp_apply,tangent_chart_apply]
      using hediag a.1 (Metric.mem_ball_self hδ)
  obtain ⟨η,hη,hηK⟩ := Metric.mem_nhds_iff.mp
    (hK.preimage_mem_nhds (e.open_source.mem_nhds hKt))
  obtain ⟨ε,hε,hεη,hεh,htube⟩ := exists_small_affine_time_tube t₀ hh hτ hr hη
  refine ⟨ε,hε,?_⟩
  intro s u hs hu
  have hsN := hN' s (hs.trans_le hεh)
  have huN := hN' u (hu.trans_le hεh)
  let c := (u-s)/τ
  let v₀ : E × E := ((q s).1,c • (q s).2)
  have hv : v₀ ∈ e.source := by
    change K (s,u) ∈ e.source
    apply hηK (a := (s,u))
    simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq] using
      max_lt (hs.trans_le hεη) (hu.trans_le hεη)
  have hvball := hesub hv
  let P : ℝ → E × E := fun w => ((q (s+c*w)).1,c • (q (s+c*w)).2)
  have hPimg : ∀ w ∈ Ioo (-r) r, (P w).1 ∈ cM.target := by
    intro w hw
    have hw' : |w| < r := abs_lt.mpr hw
    have hNw := hN' (s+c*w) (htube s u w hs hu hw')
    exact cM.map_source (hδsrc hNw.1)
  have hPode : ∀ w ∈ Ioo (-r) r,
      HasDerivAt P (coordinateGeodesicField (riemannianCoordinateMetric a.1) (P w)) w := by
    intro w hw
    exact coordinate_geodesic_affine (hN' (s+c*w) (htube s u w hs hu (abs_lt.mpr hw))).2
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have h₁ := sprayFlow_eq_coordinate_curve a hr
    (fun w hw => (hΦode w hw v₀ hvball).1)
    (fun w hw => (hΦode w hw v₀ hvball).2)
    (congrArg χ.symm (hΦ0 v₀ hvball)) ht
  have h₂ := sprayFlow_eq_coordinate_curve a hr hPimg hPode
    (show χ.symm (P 0) = χ.symm v₀ by simp only [P,v₀,mul_zero,add_zero]) ht
  have hEq : Φ (τ,v₀) = P τ := by
    have hh := congrArg χ (h₁.symm.trans h₂)
    rw [χ.right_inv ((tangent_chart_target_iff a _).mpr (hΦode τ ht v₀ hvball).1),
      χ.right_inv ((tangent_chart_target_iff a _).mpr (hPimg τ ht))] at hh
    exact hh
  have htime : s+c*τ = u := by
    dsimp [c]
    rw [div_mul_cancel₀ _ (ne_of_gt hτ)]
    ring
  have hend : (Φ (τ,v₀)).1 = cM (γ u).1 := by
    rw [hEq]
    change (q (s+c*τ)).1 = _
    rw [htime]
    exact congrArg Prod.fst (tangent_chart_apply a (γ u))
  have hmet := hdist (γ s).1 hsN.1 (γ u).1 huN.1 (c • (q s).2) hv hend
  have hen : riemannianCoordinateMetric a.1 (q s).1 (q s).2 (q s).2 = ‖(γ s).2‖^2 :=
    coordinate_spray_energy a (γ s) (hδsrc hsN.1)
  have hsc : riemannianCoordinateMetric a.1 (q s).1 (c • (q s).2) (c • (q s).2) =
      (c*‖(γ s).2‖)^2 := by
    simp only [map_smul,smul_apply,smul_eq_mul,hen]
    ring
  change dist (γ s).1 (γ u).1 = τ * Real.sqrt
    (riemannianCoordinateMetric a.1 (q s).1 (c • (q s).2) (c • (q s).2)) at hmet
  rw [hsc,Real.sqrt_sq_eq_abs,abs_mul,abs_norm] at hmet
  calc
    dist (γ s).1 (γ u).1 = τ * (|c| * ‖(γ s).2‖) := hmet
    _ = |s-u| * ‖(γ s).2‖ := by
      dsimp [c]
      rw [abs_div,abs_of_pos hτ,abs_sub_comm u s]
      field_simp [ne_of_gt hτ]
    _ = |s-u| * ‖z.2‖ := by rw [sprayFlow_speed]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicExistence
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma sprayFlow_isGeodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    IsGeodesicWithInitialData x v (fun t => (sprayFlow t ⟨x,v⟩).1) := by
  have hsm : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun t => sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const)
  refine ⟨(Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).comp hsm,?_,?_⟩
  · rw [spray_velocity_eq_mfderiv ((sprayFlow_curve ⟨x,v⟩).isMIntegralCurveAt 0)]
    exact sprayFlow_zero ⟨x,v⟩
  · exact sprayFlow_locally_minimizing ⟨x,v⟩

lemma exists_geodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ γ : ℝ → M, IsGeodesicWithInitialData x v γ :=
  ⟨_,sprayFlow_isGeodesicWithInitialData x v⟩

lemma riemannianExp_eq_chosen_geodesic (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    riemannianExp x v = Classical.choose (exists_geodesicWithInitialData x v) 1 := by
  rw [riemannianExp,dite_eq_left (exists_geodesicWithInitialData x v)]

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_NormalFlow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_metric_normal_flow (a : M) :
    ∃ δ r τ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < τ ∧ τ < r ∧
    ∃ Ψ W : ℝ × E → E, ∃ e : OpenPartialHomeomorph E E,
      ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r) ∧
      ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball (0:E) r, Ψ (0,v) = extChartAt 𝓘(ℝ,E) a a ∧ W (0,v) = v) ∧
      (∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball (0:E) r,
        Ψ (t,v) ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
        HasDerivAt (fun s => Ψ (s,v)) (W (t,v)) t ∧
        HasDerivAt (fun s => W (s,v))
          (-coordinateChristoffel (riemannianCoordinateMetric a) (Ψ (t,v)) (W (t,v)) (W (t,v))) t) ∧
      (e : E → E) = (fun v => Ψ (τ,v)) ∧
      0 ∈ e.source ∧ e 0 = extChartAt 𝓘(ℝ,E) a a ∧ e.source ⊆ Metric.ball (0:E) r ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (Metric.ball a δ ⊆ (extChartAt 𝓘(ℝ,E) a).source ∩
        (extChartAt 𝓘(ℝ,E) a) ⁻¹' e.target) ∧
      (∀ y ∈ Metric.ball a δ, dist a y = τ *
        Real.sqrt (riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a a)
          (e.symm (extChartAt 𝓘(ℝ,E) a y)) (e.symm (extChartAt 𝓘(ℝ,E) a y)))) ∧
      fderiv ℝ e 0 = τ • ContinuousLinearMap.id ℝ E := by
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,hode,he,hesub,hed,hei,hsrc,hdiag,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  let c := extChartAt 𝓘(ℝ,E) a
  let x := c a
  let Ψ : ℝ × E → E := fun z => (Φ (z.1,(x,z.2))).1
  let W : ℝ × E → E := fun z => (Φ (z.1,(x,z.2))).2
  have hball : ∀ v ∈ Metric.ball (0:E) r, (x,v) ∈ Metric.ball (x,0) r := by
    intro v hv
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hr hv
  have hΦc := hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    (show MapsTo (fun z : ℝ × E => (z.1,(x,z.2)))
      (Ioo (-r) r ×ˢ Metric.ball 0 r) (Ioo (-r) r ×ˢ Metric.ball (x,0) r) from
      fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
  have hp : ∀ z : E × E, (e z).1 = z.1 := by intro z; rw [he]
  let f := fiberwiseHomeomorph e hp x
  have hf : (f : E → E) = fun v => Ψ (τ,v) := by funext v; change (e (x,v)).2 = _; rw [he]
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have haz : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
  have hzero := coordinate_geodesic_zero_velocity
    (fun t ht' => ((contDiffOn_riemannianCoordinateMetric a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds
        (hode t ht' (x,0) (Metric.mem_ball_self hr)).1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun t ht' => riemannianCoordinateMetric_isInvertible
      (hode t ht' (x,0) (Metric.mem_ball_self hr)).1)
    (fun t ht' _ hv => riemannianCoordinateMetric_positive
      (hode t ht' (x,0) (Metric.mem_ball_self hr)).1 hv)
    (fun t _ u v => riemannianCoordinateMetric_symm a _ u v)
    (fun t ht' => ⟨((hode t ht' (x,0) (Metric.mem_ball_self hr)).2).fst,
      ((hode t ht' (x,0) (Metric.mem_ball_self hr)).2).snd⟩) h0
    (show (Φ (0,(x,0))).2 = 0 from congrArg Prod.snd (hΦ0 (x,0) (Metric.mem_ball_self hr))) ht
  have hf0 : f 0 = x := by
    rw [hf]
    exact hzero.1.trans (congrArg Prod.fst (hΦ0 (x,0) (Metric.mem_ball_self hr)))
  refine ⟨δ,r,τ,hδ,hr,hτ,hτr,Ψ,W,f,hΦc.fst,hΦc.snd,?_,?_,hf,hdiag a haz,hf0,?_,
    fiberwiseHomeomorph_contDiffOn hp x hed,fiberwiseHomeomorph_symm_contDiffOn hp x hei,?_,?_,?_⟩
  · intro v hv
    exact ⟨congrArg Prod.fst (hΦ0 (x,v) (hball v hv)),congrArg Prod.snd (hΦ0 (x,v) (hball v hv))⟩
  · intro t ht' v hv
    exact ⟨(hode t ht' (x,v) (hball v hv)).1,
      ((hode t ht' (x,v) (hball v hv)).2).fst,((hode t ht' (x,v) (hball v hv)).2).snd⟩
  · intro v hv
    exact (max_lt_iff.mp (show max (dist x x) (dist v 0) < r from hesub hv)).2
  · intro y hy
    exact ⟨hsrc hy,htarget a haz y hy⟩
  · intro y hy
    apply hdist a haz y hy (f.symm (c y))
    · exact f.map_target (htarget a haz y hy)
    · change Ψ (τ,f.symm (c y)) = c y
      exact (congrFun hf _).symm.trans (f.right_inv (htarget a haz y hy))
  · rw [hf]
    exact coordinate_flow_endpoint_derivative_zero a hr hΦ hΦ0 hode ht

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MetricCurveSpeed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma metric_curve_speed_square {γ : ℝ → M} {t k : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ t)
    (hd : ∀ᶠ s in 𝓝 t, dist (γ t) (γ s) = |s-t| * k) :
    ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)‖^2 = k^2 := by
  let a := γ t
  let c := extChartAt 𝓘(ℝ,E) a
  let q : ℝ → E := c ∘ γ
  let g := riemannianCoordinateMetric (E := E) a (c a)
  obtain ⟨δ,_,τ,hδ,_,hτ,_,_,_,e,_,_,_,_,_,hes,he0,_,hed,hei,_,hdist,hD⟩ :=
    exists_metric_normal_flow (E := E) a
  have hqat : q t ∈ e.target := by change c a ∈ e.target; rw [←he0]; exact e.map_source hes
  have hq : ContDiffAt ℝ ∞ q t :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ,E)) (x := a)).comp t hγ).contDiffAt
  let f : ℝ → E := e.symm ∘ q
  have hf : ContDiffAt ℝ ∞ f t :=
    (hei.contDiffAt (e.open_target.mem_nhds hqat)).comp t hq
  have hf0 : f t = 0 := by
    change e.symm (c a) = 0
    rw [←he0]; exact e.left_inv hes
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ Metric.ball a δ :=
    hγ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds a hδ)
  have hgs : ∀ᶠ s in 𝓝 t, g (f s) (f s) = (k^2/τ^2)*(s-t)^2 := by
    filter_upwards [hn,hd] with s hs hds
    have H : τ^2 * g (f s) (f s) = (s-t)^2*k^2 := by
      calc
        _ = (τ * Real.sqrt (g (f s) (f s)))^2 := by
          rw [mul_pow,Real.sq_sqrt (positive_bilinear_nonneg g
            (fun v hv => riemannianCoordinateMetric_positive (mem_extChartAt_target a) hv) _)]
        _ = dist (γ t) (γ s)^2 := by rw [hdist (γ s) hs]; rfl
        _ = _ := by rw [hds,mul_pow,sq_abs]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero 2 hτ.ne')).mpr
    nlinarith [H]
  have hjet := bilinear_metric_speed_of_square hf hf0 hgs
  have hedf : HasDerivAt (fun s => e (f s)) (τ • deriv f t) t := by
    have H := (hed.contDiffAt (e.open_source.mem_nhds hes)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have H' : HasFDerivAt e (τ • ContinuousLinearMap.id ℝ E) (f t) := by
      rw [hf0]; rw [←hD]; exact H.hasFDerivAt
    simpa only [Function.comp_def,smul_apply,ContinuousLinearMap.id_apply] using
      H'.comp_hasDerivAt t (hf.differentiableAt (by simp)).hasDerivAt
  have heq : (fun s => e (f s)) =ᶠ[𝓝 t] q := by
    filter_upwards [hq.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hqat)] with s hs
    exact e.right_inv hs
  have hqder : deriv q t = τ • deriv f t :=
    (hedf.congr_of_eventuallyEq heq.symm).deriv
  have hspeed : g (deriv q t) (deriv q t) = k^2 := by
    simp only [hqder,map_smul,smul_apply,smul_eq_mul,hjet]
    field_simp [hτ.ne']
  have hm := mfderiv_comp t (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,E)) (mem_chart_source E a)) (hγ.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hm
  have hval : deriv q t = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c a
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1) :=
    congrArg (fun L : ℝ →L[ℝ] E => L 1) hm
  have hnorm := coordinate_metric_chart_derivative_norm (mem_extChartAt_source (I := 𝓘(ℝ,E)) a)
    (g := g) (by
      intro u v
      change riemannianCoordinateMetric a (c a) u v = _
      rw [riemannianCoordinateMetric_apply,c.left_inv (mem_extChartAt_source (I := 𝓘(ℝ,E)) a)])
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1)
  rw [←hval] at hnorm
  calc
    _ = (Real.sqrt (g (deriv q t) (deriv q t)))^2 :=
      congrArg (fun x : ℝ => x^2) hnorm.symm
    _ = g (deriv q t) (deriv q t) := Real.sq_sqrt (positive_bilinear_nonneg g
      (fun v hv => riemannianCoordinateMetric_positive (mem_extChartAt_target a) hv) _)
    _ = k^2 := hspeed

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MetricCurveLocal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma metric_curve_eq_spray_local {γ : ℝ → M} {t k ε : ℝ}
    (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ) (hε : 0 < ε)
    (hd : ∀ s u : ℝ, |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u| * k) :
    γ =ᶠ[𝓝 t] (fun s =>
      (sprayFlow (s-t) ⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩).1) := by
  let a := γ t
  let c := extChartAt 𝓘(ℝ,E) a
  let q := c ∘ γ
  let g := riemannianCoordinateMetric (E := E) a
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Ψ,W,e,hΨ,hW,hinit,hode,hef,hes,he0,hesub,
    hed,hei,hball,hdist,hD⟩ := exists_metric_normal_flow (E := E) a
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have htau : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have hnear : γ ⁻¹' Metric.ball a δ ∩ Metric.ball t ε ∈ 𝓝 t :=
    inter_mem (hγ.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds a hδ))
      (Metric.ball_mem_nhds t hε)
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let J := Ioo (t-η) (t+η)
  have hJ : ∀ s ∈ J, |s-t| < η := by intro s hs; exact abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hJt : t ∈ J := ⟨by linarith,by linarith⟩
  have hclose : ∀ s ∈ J, γ s ∈ Metric.ball a δ ∧ |s-t| < ε := by
    intro s hs
    have H := hsub (show s ∈ Metric.ball t η by simpa only [Metric.mem_ball,Real.dist_eq] using hJ s hs)
    exact ⟨H.1,by simpa only [Metric.mem_ball,Real.dist_eq] using H.2⟩
  have hqsrc : ∀ s ∈ J, γ s ∈ c.source := fun s hs => (hball (hclose s hs).1).1
  have hqt : ∀ s ∈ J, q s ∈ e.target := fun s hs => (hball (hclose s hs).1).2
  have hq : ∀ s ∈ J, ContDiffAt ℝ ∞ q s := by
    intro s hs
    exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (x := a) (by simpa only [c,extChartAt_source] using hqsrc s hs)).comp s hγ.contMDiffAt).contDiffAt
  let f : ℝ → E := e.symm ∘ q
  have hf : ∀ s ∈ J, ContDiffAt ℝ ∞ f s := by
    intro s hs
    exact (hei.contDiffAt (e.open_target.mem_nhds (hqt s hs))).comp s (hq s hs)
  have hfs : MapsTo f J e.source := fun s hs => e.map_target (hqt s hs)
  have hf0 : f t = 0 := by change e.symm (c a) = 0; rw [←he0]; exact e.left_inv hes
  have heq : ∀ s ∈ J, e (f s) = q s := fun s hs => e.right_inv (hqt s hs)
  have heqnear : ∀ s ∈ J, (e ∘ f) =ᶠ[𝓝 s] q := by
    intro s hs
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact heq u hu
  have hsquares : ∀ s ∈ J, τ^2*g (c a) (f s) (f s) = (s-t)^2*k^2 := by
    intro s hs
    calc
      _ = (τ*Real.sqrt (g (c a) (f s) (f s)))^2 := by
        rw [mul_pow,Real.sq_sqrt (positive_bilinear_nonneg _
          (fun v hv => riemannianCoordinateMetric_positive (mem_extChartAt_target a) hv) _)]
      _ = dist (γ t) (γ s)^2 := by rw [hdist (γ s) (hclose s hs).1]; rfl
      _ = _ := by rw [hd t s (by simpa only [sub_self,abs_zero] using hε) (hclose s hs).2,
        mul_pow,sq_abs]; ring
  have hlin : ∀ s ∈ J, f s = (s-t) • deriv f t := by
    apply normal_chart_radial_rigidity e hed hei (g (c a))
      (riemannianCoordinateMetric_symm a (c a)) g (fun v => W (τ,v)) τ k
      (fun v hv w hw => riemannianCoordinateMetric_positive (by rw [hef]; exact (hode τ htau v (hesub hv)).1) hw)
      (fun v _ => riemannianCoordinateMetric_symm a (e v)) ?_ ?_ ?_
      (fun s hs => (hf s hs).contDiffWithinAt) hJt hfs ?_ hsquares
    · intro v hv
      have H := coordinate_geodesic_speed_constant
        (fun s hs => ((contDiffOn_riemannianCoordinateMetric a).contDiffAt
          ((isOpen_extChartAt_target a).mem_nhds (hode s hs v (hesub hv)).1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (fun s hs => riemannianCoordinateMetric_isInvertible (hode s hs v (hesub hv)).1)
        (fun s _ => riemannianCoordinateMetric_symm a (Ψ (s,v)))
        (fun s hs => (hode s hs v (hesub hv)).2) htau h0
      simpa only [hef,(hinit v (hesub hv)).1,(hinit v (hesub hv)).2] using H
    · intro v hv w
      have H := coordinate_endpoint_gauss (isOpen_extChartAt_target a)
        (contDiffOn_riemannianCoordinateMetric a)
        (fun x hx => riemannianCoordinateMetric_isInvertible hx)
        (fun x _ => riemannianCoordinateMetric_symm a x) hΨ hW
        (fun s hs v hv => (hode s hs v hv).1) (fun s hs v hv => (hode s hs v hv).2)
        h0 (fun v hv => (hinit v hv).1) (fun v hv => (hinit v hv).2) htau (hesub hv) w
      simpa only [hef] using H
    · intro v hv
      rw [hef]
      exact coordinate_endpoint_radial a hr hΨ hinit hode (hesub hv) htau
    · intro s hs
      rw [heq s hs,(heqnear s hs).deriv_eq]
      have Hspeed : g (q s) (deriv q s) (deriv q s) =
          ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ s (1:ℝ)‖^2 :=
        coordinate_curve_speed_square (hγ.mdifferentiable (by simp) s) (hqsrc s hs)
      rw [Hspeed]
      apply metric_curve_speed_square hγ.contMDiffAt
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      rw [hd s u (hclose s hs).2 (hclose u hu).2,abs_sub_comm s u]
  have hqtder : deriv q t = τ • deriv f t := by
    have heD := (hed.contDiffAt (e.open_source.mem_nhds hes)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hD' : HasFDerivAt e (τ • ContinuousLinearMap.id ℝ E) (f t) := by
      rw [hf0,←hD]; exact heD.hasFDerivAt
    have H := hD'.comp_hasDerivAt t ((hf t hJt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
    simpa only [smul_apply,ContinuousLinearMap.id_apply] using
      (H.congr_of_eventuallyEq (heqnear t hJt).symm).deriv
  have hvel : τ • deriv f t = mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ) :=
    hqtder.symm.trans (coordinate_curve_derivative_at_center (hγ.mdifferentiable (by simp) t))
  filter_upwards [isOpen_Ioo.mem_nhds hJt] with s hs
  have H := sprayFlow_eq_coordinate_curve (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) hr
    (fun u hu => (hode u hu (f s) (hesub (hfs hs))).1)
    (fun u hu => (hode u hu (f s) (hesub (hfs hs))).2.1.prodMk
      (hode u hu (f s) (hesub (hfs hs))).2.2)
    (show (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)).symm
        (Ψ (0,f s),W (0,f s)) = ⟨a,f s⟩ by
      rw [(hinit (f s) (hesub (hfs hs))).1,(hinit (f s) (hesub (hfs hs))).2]
      exact tangent_chart_at_self_base_symm (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) (f s)) htau
  have Hb := congrArg (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) H
  rw [tangent_chart_symm_base,←congrFun hef (f s),heq s hs] at Hb
  have hbase : γ s = (sprayFlow τ ⟨a,f s⟩).1 := by
    rw [Hb]; exact (c.left_inv (hqsrc s hs)).symm
  rw [hbase,hlin s hs,←hvel]
  rw [show (⟨a,(s-t) • deriv f t⟩ : TangentBundle 𝓘(ℝ,E) M) =
    tangentScale (s-t) ⟨a,deriv f t⟩ from rfl,sprayFlow_scale]
  rw [show (⟨γ t,τ • deriv f t⟩ : TangentBundle 𝓘(ℝ,E) M) =
    tangentScale τ ⟨a,deriv f t⟩ from rfl,sprayFlow_scale]
  change (sprayFlow ((s-t)*τ) ⟨a,deriv f t⟩).1 = (sprayFlow (τ*(s-t)) ⟨a,deriv f t⟩).1
  rw [mul_comm]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MetricGeodesicLift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma metric_curve_velocity_isMIntegralCurve {γ : ℝ → M} {k : ℝ}
    (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ)
    (hloc : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ,
      |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u| * k) :
    IsMIntegralCurve
      (fun t => (⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩ : TangentBundle 𝓘(ℝ,E) M))
      (geodesicSpray (E := E)) := by
  intro t
  obtain ⟨ε,hε,hd⟩ := hloc t
  let δ : ℝ → TangentBundle 𝓘(ℝ,E) M := fun s =>
    sprayFlow (s-t) ⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩
  have hδ : IsMIntegralCurve δ (geodesicSpray (E := E)) :=
    isMIntegralCurve_comp_sub.mpr (sprayFlow_curve _)
  have he : γ =ᶠ[𝓝 t] (fun s => (δ s).1) := metric_curve_eq_spray_local hγ hε hd
  have hL : (fun s => (⟨γ s,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ s (1:ℝ)⟩ : TangentBundle 𝓘(ℝ,E) M))
      =ᶠ[𝓝 t] δ := by
    filter_upwards [he.eventuallyEq_nhds] with s hs
    rw [velocity_lift_eq_of_eventuallyEq hs,
      spray_velocity_eq_mfderiv (hδ.isMIntegralCurveAt s)]
  have H := (hδ t).congr_of_eventuallyEq hL
  rw [←hL.self_of_nhds] at H
  exact H

lemma metric_curve_eq_spray {γ : ℝ → M} {k : ℝ}
    (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ)
    (hloc : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ,
      |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u| * k) :
    γ = (fun t => (sprayFlow t ⟨γ 0,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ 0 (1:ℝ)⟩).1) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  have H := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (contMDiff_geodesicSpray.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (metric_curve_velocity_isMIntegralCurve hγ hloc) (sprayFlow_curve _)
    (sprayFlow_zero _).symm
  funext t
  exact congrArg (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) (congrFun H t)

end

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma geodesicWithInitialData_eq_spray {x : M} {v : TangentSpace 𝓘(ℝ,Model n) x}
    {γ : ℝ → M} (hγ : IsGeodesicWithInitialData x v γ) :
    γ = (fun t => (sprayFlow t ⟨x,v⟩).1) := by
  have H := metric_curve_eq_spray hγ.1 hγ.2.2
  rwa [hγ.2.1] at H

lemma riemannianExp_eq_sprayFlow (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    riemannianExp x v = (sprayFlow 1 ⟨x,v⟩).1 := by
  rw [riemannianExp_eq_chosen_geodesic,
    geodesicWithInitialData_eq_spray (Classical.choose_spec (exists_geodesicWithInitialData x v))]

lemma riemannianExp_smul (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) (t : ℝ) :
    riemannianExp x (t • v) = (sprayFlow t ⟨x,v⟩).1 := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale t ⟨x,v⟩)).1 = _
  rw [sprayFlow_scale,mul_one]
  rfl

lemma contMDiff_riemannianExp :
    ContMDiff (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,Model n) ∞
      (fun z : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp z.1 z.2) := by
  have hF : ContMDiff (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun z : TangentBundle 𝓘(ℝ,Model n) M => sprayFlow 1 z) :=
    contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)
  have H := (Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).comp hF
  apply H.congr
  intro z
  cases z
  exact riemannianExp_eq_sprayFlow _ _

end WeakMTWTransport

end

end OAI
end

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

lemma continuous_riemannianExp (x : M) : Continuous (riemannianExp (n := n) x) :=
  contMDiff_riemannianExp.continuous.comp (FiberBundle.continuous_totalSpaceMk _ _ x)

lemma isClosed_minimizingVectors (x : M) : IsClosed (minimizingVectors (n := n) x) :=
  isClosed_eq (continuous_const.dist (continuous_riemannianExp x)) continuous_norm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ShortGradient
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_spray_cost_gradient (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, ∀ t : ℝ, 0 < t →
      z.1 ∈ Metric.ball a δ → (sprayFlow t z).1 ∈ Metric.ball a δ →
      dist z.1 (sprayFlow t z).1 = t*‖z.2‖ →
      HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist z.1 y^2/2)
        (sprayFlow t z).1 (innerSL ℝ (t • (sprayFlow t z).2)) := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z t ht hz hy hmin
  obtain ⟨⟨b,w⟩,hb,hn,_,hD⟩ := H z.1 hz (sprayFlow t z).1 hy
  dsimp only at hb
  subst b
  have hw := sprayFlow_minimizer_gradient z ht hmin w hn hD
  rwa [hw] at hD

lemma exists_local_spray_cost_start_gradient (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, ∀ t : ℝ, 0 < t →
      z.1 ∈ Metric.ball a δ → (sprayFlow t z).1 ∈ Metric.ball a δ →
      dist z.1 (sprayFlow t z).1 = t*‖z.2‖ →
      HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist y (sprayFlow t z).1^2/2)
        z.1 (innerSL ℝ ((-t) • z.2)) := by
  obtain ⟨δ,hδ,H⟩ := exists_local_spray_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z t ht hz hy hmin
  let w := tangentScale (-1) (sprayFlow t z)
  have hw : sprayFlow t w = tangentScale (-1) z := sprayFlow_reverse z t
  have hb : (sprayFlow t w).1 ∈ Metric.ball a δ := by rw [hw]; exact hz
  have hm : dist w.1 (sprayFlow t w).1 = t*‖w.2‖ := by
    rw [hw]
    change dist (sprayFlow t z).1 z.1 = t*‖(-1:ℝ) • (sprayFlow t z).2‖
    rw [neg_one_smul,norm_neg,sprayFlow_speed,dist_comm,hmin]
  have hd := H w t ht hy hb hm
  rw [hw] at hd
  change HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist (sprayFlow t z).1 y^2/2)
    z.1 (innerSL ℝ (t • ((-1:ℝ) • z.2))) at hd
  rw [smul_smul,mul_neg_one] at hd
  have hf : (fun y => dist y (sprayFlow t z).1^2/2) =
      (fun y => dist (sprayFlow t z).1 y^2/2) := by
    funext y; rw [dist_comm]
  rw [hf]
  exact hd

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpNonconjugacy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contMDiff_riemannianExp_fiber (x : M) :
    ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞ (riemannianExp (n := n) x) := by
  have H := (Bundle.contMDiff_proj (fun z : M => TangentSpace 𝓘(ℝ,Model n) z)).comp
    (contMDiff_spray_fiber x 1)
  apply H.congr
  intro v
  exact riemannianExp_eq_sprayFlow x v

end WeakMTWTransport

end

end OAI
end


