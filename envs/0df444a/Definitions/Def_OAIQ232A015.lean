-- Prove2me | Definitions.Def_OAIQ232A015
-- name    : OAIQ232A015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:48:24.664083+00:00
-- url     : https://prove2.me/theorems/5d8efbf2-9799-45a0-a71d-9501d3d136f7
-- title:
--   Definitions bundle OAIQ232A015 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Coordinates_NormalCoordinates2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/NormalCoordinates2.lean).
--
--   **Imports.** It imports the bundle `OAIQ232A007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A019`.
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
import Definitions.Def_OAIQ232A007

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates2
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma coordinate_endpoint_gauss
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {Ψ W : ℝ × E → E} {a b R : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo a b ×ˢ Metric.ball 0 R))
    (hW : ContDiffOn ℝ ∞ W (Ioo a b ×ˢ Metric.ball 0 R))
    (himg : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo a b)
    (hΨ0 : ∀ v ∈ Metric.ball 0 R, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 R, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo a b) {v : E} (hv : v ∈ Metric.ball 0 R) (w : E) :
    g (Ψ (τ,v)) (W (τ,v)) ((fderiv ℝ (fun z => Ψ (τ,z)) v) w) = τ * g x v w := by
  have hνc : ContinuousAt (fun s : ℝ => v + s • w) 0 := by fun_prop
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, v + s • w ∈ Metric.ball 0 R :=
    hνc (by simpa only [zero_smul,add_zero] using Metric.isOpen_ball.mem_nhds hv)
  obtain ⟨δ,hd,hδ⟩ := Metric.mem_nhds_iff.mp hnear
  have hνmem : ∀ s ∈ Ioo (-δ) δ, v + s • w ∈ Metric.ball 0 R := by
    intro s hs
    exact hδ (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using abs_lt.mpr hs)
  let A : ℝ × ℝ → E := fun z => Ψ (z.1,v + z.2 • w)
  let V : ℝ × ℝ → E := fun z => W (z.1,v + z.2 • w)
  have hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo (-δ) δ) :=
    hΨ.comp (contDiffOn_fst.prodMk (contDiffOn_const.add
      (contDiffOn_snd.smul contDiffOn_const))) (fun z hz => ⟨hz.1,hνmem z.2 hz.2⟩)
  have hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo (-δ) δ) :=
    hW.comp (contDiffOn_fst.prodMk (contDiffOn_const.add
      (contDiffOn_snd.smul contDiffOn_const))) (fun z hz => ⟨hz.1,hνmem z.2 hz.2⟩)
  have hs0 : (0:ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hd,hd⟩
  have hν : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    convert ((hasDerivAt_id (0:ℝ)).smul_const w).const_add v using 1 <;>
      first | rfl | simp only [one_smul]
  have hG := coordinate_gauss_variation hS hg hi hsym hA hV
    (fun t ht s hs => himg t ht (v+s•w) (hνmem s hs))
    (fun t ht s hs => hode t ht (v+s•w) (hνmem s hs))
    h0 (fun s hs => hΨ0 (v+s•w) (hνmem s hs))
    (fun s hs => hW0 (v+s•w) (hνmem s hs)) hτ hs0 hν
  have hψd : DifferentiableAt ℝ (fun z => Ψ (τ,z)) v :=
    ((hΨ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hτ,hv⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψder := (show HasFDerivAt (fun z => Ψ (τ,z))
      (fderiv ℝ (fun z => Ψ (τ,z)) v) (v+(0:ℝ)•w) by
    simpa only [zero_smul,add_zero] using hψd.hasFDerivAt).comp_hasDerivAt 0 hν
  have hAr := hasDerivAt_slice_right ((hA.contDiffAt
    ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hτ,hs0⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hJ : directionalDerivative A (0,1) (τ,0) =
      (fderiv ℝ (fun z => Ψ (τ,z)) v) w := hAr.unique hψder
  simpa only [A,V,zero_smul,add_zero,hJ] using hG

end

end WeakMTWTransport

end

end OAI
end


