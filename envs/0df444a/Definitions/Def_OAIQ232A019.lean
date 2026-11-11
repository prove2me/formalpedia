-- Prove2me | Definitions.Def_OAIQ232A019
-- name    : OAIQ232A019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:30.678213+00:00
-- url     : https://prove2.me/theorems/2ae190c9-a65e-44e7-b06e-76da235a648b
-- title:
--   Definitions bundle OAIQ232A019 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Volume_RiemannianCalibration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Volume/RiemannianCalibration.lean).
--
--   **Imports.** It imports the bundles `OAIQ232A015` and `OAIQ232A017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A021`.
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
import Definitions.Def_OAIQ232A015
import Definitions.Def_OAIQ232A017

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RiemannianCalibration
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

lemma coordinate_normal_chart_radial_bound
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
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
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hγimg : MapsTo γ (Icc a b) e.target)
    (hγa : γ a = e 0) :
    ENNReal.ofReal (τ * Real.sqrt (g x (e.symm (γ b)) (e.symm (γ b)))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (γ t) (deriv γ t) (deriv γ t))) := by
  have hef_apply : ∀ v, Ψ (τ,v) = e v := fun v => congrFun hef.symm v
  have hi : ∀ y ∈ S, (g y).IsInvertible := fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  have hx : x ∈ S := by
    rw [←hΨ0 0 (hesub hes)]
    exact himg 0 h0 0 (hesub hes)
  have het : ∀ y ∈ e.target, y ∈ S := by
    intro y hy
    have hyv := hesub (e.map_target hy)
    have hh := himg τ hτ (e.symm y) hyv
    rw [hef_apply,e.right_inv hy] at hh
    exact hh
  apply normal_chart_radial_path_bound e (hed.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hei.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hes
    (g x) (positive_bilinear_nonneg _ (hpos x hx)) (hsym x hx) g
    (fun y hy => hpos y (het y hy)) (fun y hy => hsym y (het y hy))
    (fun y => W (τ,e.symm y)) hτnonneg ?_ ?_ hab hγ hγimg hγa
  · intro y hy
    have hv := hesub (e.map_target hy)
    have heq : Ψ (τ,e.symm y) = y := by rw [hef_apply,e.right_inv hy]
    have hc := coordinate_geodesic_speed_constant
      (fun t ht => (hg.contDiffAt (hS.mem_nhds (himg t ht (e.symm y) hv))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (fun t ht => hi _ (himg t ht _ hv))
      (fun t ht => hsym _ (himg t ht _ hv))
      (fun t ht => hode t ht _ hv) hτ h0
    simpa only [heq,hΨ0 _ hv,hW0 _ hv] using hc
  · intro y hy w
    have hv := hesub (e.map_target hy)
    have hh := coordinate_endpoint_gauss hS hg hi hsym hΨ hW himg hode
      h0 hΨ0 hW0 hτ hv w
    rw [hef_apply,e.right_inv hy,←hef] at hh
    exact hh

end WeakMTWTransport

end

end OAI
end


