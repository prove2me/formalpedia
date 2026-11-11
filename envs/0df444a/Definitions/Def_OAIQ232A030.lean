-- Prove2me | Definitions.Def_OAIQ232A030
-- name    : OAIQ232A030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:32.869434+00:00
-- url     : https://prove2.me/theorems/528a3625-34d5-4732-a806-2b5295a23f99
-- title:
--   Definitions bundle OAIQ232A030 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 8 definitions, 2 inductive types or structures and 28 theorems. The definitions and types are `OAI.WeakMTWTransport.MaximumDiagonal`, `OAI.WeakMTWTransport.MaximumJensenFamily`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleCenter`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleGradient`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleH`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleIndex`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleL`, `OAI.WeakMTWTransport.MaximumJensenFamily.samplePoint`, `OAI.WeakMTWTransport.MaximumJensenFamily.sampleSlope`, `OAI.WeakMTWTransport.WeakMTW.graphHomeomorph`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_HopfGradient`, `BiholderTransport_Contact_ActiveContinuationLocal`, `BiholderTransport_Contact_ActiveLocalGrowth`, `BiholderTransport_Contact_GlobalSupport`, `BiholderTransport_Contact_GraphProjection`, `BiholderTransport_Contact_HopfSupports`, `BiholderTransport_Convexity_MaximumJensenFamily`, `BiholderTransport_Convexity_UniformEnvelope`, `BiholderTransport_Coordinates_ActiveHull`, `BiholderTransport_Coordinates_ActiveHullUniform`, `BiholderTransport_Coordinates_ActiveUniformGrowth`, `BiholderTransport_Coordinates_FiniteActiveGrowth`, `BiholderTransport_Coordinates_MetricLocalGrowth`, `BiholderTransport_CostGeometry_GraphOpen`, `BiholderTransport_CostGeometry_PrecutExtension`, `BiholderTransport_CostGeometry_ProjectionContinuation`, `BiholderTransport_CostGeometry_UniformLocalGap`, `BiholderTransport_Duality_GeometricEnvelope`, `BiholderTransport_Regularity_GraphInverse`, `BiholderTransport_Regularity_MaximumCenterSequence`, `BiholderTransport_Regularity_MaximumDiagonal`, `BiholderTransport_Regularity_MaximumReindex`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A028` and `OAIQ232A029` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A031`; the statements `OAI.WeakMTWTransport.MaximumDiagonal.center_matrix_limit`, `OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact`, `OAI.WeakMTWTransport.MaximumDiagonal.good_centers`, `OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets`, `OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first`, `OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact`, `OAI.WeakMTWTransport.MaximumJensenFamily.center_regular`, `OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward`, `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact`, `OAI.WeakMTWTransport.MaximumRow.jensen_first_limit`, `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous`, `OAI.WeakMTWTransport.exists_maximum_center_gain` and `OAI.WeakMTWTransport.exists_maximum_true_center`; the proofs of `OAI.WeakMTWTransport.MaximumDiagonal.center_matrix_limit`, `OAI.WeakMTWTransport.MaximumDiagonal.center_phase_compact`, `OAI.WeakMTWTransport.MaximumDiagonal.good_centers`, `OAI.WeakMTWTransport.MaximumFamily.eventually_jensen_first`, `OAI.WeakMTWTransport.MaximumJensenFamily.active_outward_compact`, `OAI.WeakMTWTransport.MaximumJensenFamily.eventual_outward`, `OAI.WeakMTWTransport.WeakMTW.class_power`, `OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix`, `OAI.WeakMTWTransport.WeakMTW.exists_locally_uniform_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_maximum_family`, `OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess`, `OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts`, `OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure` and `OAI.WeakMTWTransport.uniform_biHolder_transport`.
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
import Definitions.Def_OAIQ232A028
import Definitions.Def_OAIQ232A029

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiniteActiveGrowth
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.finite_active_cost_growth (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0<t) (hts : t < s) (hs : s<1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0, ∃ i,
      b*‖h‖^2≤
        (normalCost x (t • (∑ j, w j • p j)) h-normalCost x (t • (∑ j, w j • p j)) 0)/t-
        (normalCost x (s • p i) h-normalCost x (s • p i) 0)/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let r := ∑ j, w j • p j
  have hrh : r ∈ convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hw i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  have hrt := hID r hrh
  have hsi : ∀ i, s • p i ∈ injectivityDomain x :=
    fun i => contracted_minimizer_mem_injectivityDomain (hmin i) (ht.trans hts) hs
  let f := fun i (h : TangentSpace 𝓘(ℝ,Model n) x) =>
    t⁻¹*(normalCost x (t • r) h-normalCost x (t • r) 0)-
    s⁻¹*(normalCost x (s • p i) h-normalCost x (s • p i) 0)
  have hleft : ContDiffAt ℝ 2 (normalCost x (t • r)) 0 :=
    (normalCost_contDiffAt hrt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hright : ∀ i, ContDiffAt ℝ 2 (normalCost x (s • p i)) 0 :=
    fun i => (normalCost_contDiffAt (hsi i)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := fun i =>
    (contDiffAt_const.mul (hleft.sub contDiffAt_const)).sub
      (contDiffAt_const.mul ((hright i).sub contDiffAt_const))
  have hfirst : ∀ i, fderiv ℝ (f i) 0=innerSL ℝ (p i-r) := by
    intro i
    have H := (((normalCost_hasFDerivAt_zero hrt).sub_const (normalCost x (t • r) 0)).const_smul t⁻¹).sub
      (((normalCost_hasFDerivAt_zero (hsi i)).sub_const (normalCost x (s • p i) 0)).const_smul s⁻¹)
    have H' : HasFDerivAt (f i) (innerSL ℝ (p i-r)) 0 := by
      apply H.congr_fderiv
      ext v
      simp only [sub_apply,smul_apply,innerSL_apply_apply,inner_neg_left,
        real_inner_smul_left,inner_sub_left,smul_eq_mul]
      field_simp [ht.ne', (ht.trans hts).ne']
      ring
    exact H'.fderiv
  have hsecond : ∀ i v, fderiv ℝ (fderiv ℝ (f i)) 0 v v=
      hessianValue x (t • r) v/t-hessianValue x (s • p i) v/s := by
    intro i v
    rw [second_fderiv_scaled_differences hleft (hright i)]
    rw [hessianValue_eq_normalHessian hrt,hessianValue_eq_normalHessian (hsi i)]
    simp only [normalHessian,div_eq_mul_inv]
    ring
  have hmean : ∀ v, ∑ i, w i*fderiv ℝ (f i) 0 v=0 := by
    intro v
    simp only [hfirst,innerSL_apply_apply,inner_sub_left,mul_sub,Finset.sum_sub_distrib,
      ←Finset.sum_mul,hsum,one_mul]
    have heq : (∑ i, w i*inner ℝ (p i) v)=inner ℝ r v := by
      simp only [r,sum_inner,real_inner_smul_left]
    rw [heq,sub_self]
  have hpos : ∀ v, v≠0 → (∀ i, fderiv ℝ (f i) 0 v=0) →
      0<∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v := by
    intro v hv hl
    have hortho : ∀ i, inner ℝ v (p i-r)=0 := by
      intro i
      rw [real_inner_comm]
      simpa only [hfirst,innerSL_apply_apply] using hl i
    have H := hmtw.finite_transverse_slack_strict p w hw hsum hmin ht hts hs hID hv hortho
    simp only [hsecond,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
    exact sub_pos.mpr H
  obtain ⟨b,hb,H⟩ := finite_smooth_transverse_growth f hf (fun i => by simp [f]) w hw hsum hmean hpos
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  refine ⟨i,?_⟩
  simpa only [f,r,div_eq_mul_inv,mul_comm] using hi
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActiveLocalGrowth
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_local_growth (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    {v : M → ℝ} (hv : Continuous v)
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform v) v x (riemannianExp x (p i))=0)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      b*‖h‖^2 ≤
        cTransform v (riemannianExp x h)-cTransform v x+
        (cost (riemannianExp x h) (riemannianExp x (t • (∑ j, w j • p j)))-
          cost x (riemannianExp x (t • (∑ j, w j • p j))))/t := by
  obtain ⟨s,hts,hs1⟩ := exists_between ht1
  obtain ⟨b,hb,H⟩ := hmtw.finite_active_cost_growth p w hw hsum hmin ht hts hs1 hID
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  have hsup := active_split_lower_support hv (hmin i) (hactive i) (ht.trans hts) hs1
    (riemannianExp x h)
  simp only [normalCost,riemannianExp_zero] at hi
  rw [neg_div] at hsup
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveHull
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

lemma WeakMTW.active_hull_local_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      b*‖h‖^2 ≤ cTransform v (riemannianExp x h)-cTransform v x+
        (cost (riemannianExp x h) (riemannianExp x (t • p))-
          cost x (riemannianExp x (t • p)))/t := by
  obtain ⟨ι,inst,z,w,hz,_,hw,hsum,heq⟩ := eq_pos_convex_span_of_mem_convexHull hp
  let : Fintype ι := inst
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  have hsub : convexHull ℝ (range z) ⊆ convexHull ℝ (activeLogs (n := n) v x) := convexHull_mono hz
  have H := hmtw.active_local_growth hv z w hw hsum (fun i => (hz (mem_range_self i)).1)
    (fun i => (hz (mem_range_self i)).2) ht ht1 (fun q hq => hID q (hsub hq))
  simpa only [heq] using H

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

lemma WeakMTW.active_hull_metric_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∃ b>0, ∀ᶠ z in 𝓝 x,
      b*dist x z^2 ≤ cTransform v z-cTransform v x+
        (cost z (riemannianExp x (t • p))-cost x (riemannianExp x (t • p)))/t := by
  obtain ⟨b,hb,H⟩ := hmtw.active_hull_local_growth hv hp ht ht1 hID
  refine ⟨b,hb,?_⟩
  have hh := metric_local_growth_of_normal (n := n)
    (f := fun z => cTransform v z+cost z (riemannianExp x (t • p))/t)
    (b := b) (x := x) (by
      filter_upwards [H] with h hh
      rw [sub_div] at hh
      linarith)
  filter_upwards [hh] with z hz
  rw [sub_div]
  linarith

lemma WeakMTW.active_hull_strict_local_min (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∀ᶠ z in 𝓝 x, z≠x →
      cTransform v x+cost x (riemannianExp x (t • p))/t <
        cTransform v z+cost z (riemannianExp x (t • p))/t := by
  obtain ⟨b,hb,H⟩ := hmtw.active_hull_metric_growth hv hp ht ht1 hID
  filter_upwards [H] with z hz hzx
  have hd : 0<dist x z := dist_pos.mpr hzx.symm
  have hpos := mul_pos hb (sq_pos_of_pos hd)
  rw [sub_div] at hz
  linarith

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

lemma WeakMTW.active_hull_nearby_local_min (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∀ O ∈ 𝓝 x, ∀ᶠ y in 𝓝 (riemannianExp x (t • p)),
      ∃ z∈O, IsLocalMin (fun w => cTransform v w+cost w y/t) z := by
  let : Nonempty M := ⟨x⟩
  apply exists_local_min_of_strict_growth
  · exact ((continuous_cTransform hv).comp continuous_fst).add
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2 |>.div_const t)
  · exact hmtw.active_hull_strict_local_min hv hp ht ht1 hID

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_GraphOpen
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.local_projection_surjective (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈normalSubdifferential (n := n) (cTransform v) x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q∈normalSubdifferential (n := n) (cTransform v) x, t • q∈injectivityDomain x) :
    ∀ O∈𝓝 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      ∀ᶠ y in 𝓝 (riemannianExp x (t • p)),
        ∃ z∈O, z.2∈normalSubdifferential (n := n) (cTransform v) z.1 ∧
          riemannianExp z.1 (t • z.2)=y := by
  intro O hO
  let y₀ := riemannianExp x (t • p)
  have htp := hID p hp
  obtain ⟨P,hP,hP0,_,hPinv⟩ := exists_smooth_exp_branch
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) (riemannianExp_interior_nonconjugate htp)
  let Q := fun q : M×M => tangentScale t⁻¹ (P q)
  have hQ : ContinuousAt Q (x,y₀) :=
    (contMDiff_tangentScale (E := Model n) (M := M)).continuous.continuousAt.comp
      (continuousAt_const.prodMk hP.continuousAt)
  have hQ0 : Q (x,y₀)=(⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    dsimp only [Q,y₀]
    rw [hP0]
    simp only [tangentScale,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  have hQO : ∀ᶠ q : M×M in 𝓝 (x,y₀), Q q∈O :=
    hQ.preimage_mem_nhds (hQ0.symm ▸ hO)
  have hPID : ∀ᶠ q : M×M in 𝓝 (x,y₀), (P q).2∈injectivityDomain (P q).1 := by
    have hmem : {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈injectivityDomain z.1} ∈
        𝓝 (P (x,y₀)) := by
      apply (isOpen_total_injectivityDomain (n := n) (M := M)).mem_nhds
      rw [hP0]
      exact htp
    exact hP.continuousAt.preimage_mem_nhds hmem
  have H := (hQO.and hPID).and hPinv
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp H
  have hpH : p∈convexHull ℝ (activeLogs (n := n) v x) :=
    normalSubdifferential_subset_active_hull hv x hp
  have hIDH : ∀ q∈convexHull ℝ (activeLogs (n := n) v x), t • q∈injectivityDomain x :=
    fun q hq => hID q (active_hull_subset_normalSubdifferential hv x hq)
  have hmin := hmtw.active_hull_nearby_local_min hv hpH ht ht1 hIDH U hU
  filter_upwards [hV,hmin] with y hy hh
  obtain ⟨a,ha,hmin⟩ := hh
  have hq := hUV (show (a,y)∈U ×ˢ V from ⟨ha,hy⟩)
  rcases hPa : P (a,y) with ⟨b,r⟩
  change (tangentScale t⁻¹ (P (a,y))∈O ∧
    (P (a,y)).2∈injectivityDomain (P (a,y)).1) ∧
    (P (a,y)).1=a ∧ riemannianExp (P (a,y)).1 (P (a,y)).2=y at hq
  rw [hPa] at hq
  have hb : b=a := hq.2.1
  subst b
  have hr : r∈injectivityDomain a := hq.1.2
  have hE : riemannianExp a r=y := hq.2.2
  have htr : t • (t⁻¹ • r)=r := by rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  refine ⟨⟨a,t⁻¹ • r⟩,?_,?_,?_⟩
  · exact hq.1.1
  · apply local_min_divided_cost_subgradient ht.ne'
    · simpa only [htr] using hr
    · simpa only [htr,hE] using hmin
  · simpa only [htr] using hE

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GraphProjection
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.isOpenMap_graphProjection (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ x : M, ∀ q∈normalSubdifferential (n := n) (cTransform v) x,
      t • q∈injectivityDomain x) :
    IsOpenMap (graphProjection (n := n) (cTransform v) t) := by
  intro O hO
  obtain ⟨U,hU,hUO⟩ := isOpen_induced_iff.mp hO
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨z,hz,rfl⟩
  have hzU : z.1∈U := by
    have : z∈Subtype.val ⁻¹' U := by rw [hUO]; exact hz
    exact this
  have H := hmtw.local_projection_surjective hv z.2 ht ht1 (hID z.1.1) U (hU.mem_nhds hzU)
  filter_upwards [H] with y hy
  obtain ⟨p,hp,hpG,hpy⟩ := hy
  refine ⟨⟨p,hpG⟩,?_,hpy⟩
  rw [←hUO]
  exact hp
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

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

lemma eventually_uniform_graph_precut {v : M → ℝ} (hv : Continuous v) {T : ℝ}
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      T • p ∈ injectivityDomain x) :
    ∀ᶠ t in 𝓝 T, ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • p ∈ injectivityDomain x := by
  let : CompactSpace (subgradientGraph (n := n) (cTransform v)) :=
    isCompact_iff_compactSpace.mp (isCompact_subgradientGraph hv)
  have hf : Continuous (fun q : ℝ × subgradientGraph (n := n) (cTransform v) => tangentScale q.1 q.2.1) :=
    contMDiff_tangentScale.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have H : ∀ᶠ t in 𝓝 T, ∀ z : subgradientGraph (n := n) (cTransform v),
      t • z.1.2 ∈ injectivityDomain z.1.1 := by
    have HH : ∀ᶠ t in 𝓝 T, ∀ z ∈ (univ : Set (subgradientGraph (n := n) (cTransform v))),
        t • z.1.2 ∈ injectivityDomain z.1.1 := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro z _
      exact (isOpen_total_injectivityDomain.preimage hf).mem_nhds
        (hID z.1.1 z.1.2 (normalSubdifferential_subset_active_hull hv z.1.1 z.2))
    exact HH.mono (fun _ h z => h z (mem_univ z))
  filter_upwards [H] with t ht x p hp
  exact ht ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩

lemma exists_extended_uniform_precut {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      T • p ∈ injectivityDomain x) :
    ∃ S, T<S ∧ S<1 ∧ ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) S, t • p ∈ injectivityDomain x := by
  obtain ⟨S,hTS,hS1,hS⟩ := ((frequently_gt_nhds T).and_eventually
    ((eventually_lt_nhds hT1).and (eventually_uniform_graph_precut hv hID))).exists
  refine ⟨S,hTS,hS1,?_⟩
  intro x p hp t ht
  exact scaled_injectivityDomain_of_le (hT.trans hTS) ht.1 ht.2 (hS x p hp)

end WeakMTWTransport

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_UniformEnvelope
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

lemma WeakMTW.compact_scaled_envelope_growth
    (hmtw : WeakMTW (n := n) (M := M))
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : M) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (d : P → EnvelopeData (Model n) ι) (hd : Continuous d)
    (hb : ∀ z, (d z).1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hw : ∀ z i, 0 ≤ (d z).2.1 i) (hsum : ∀ z, ∑ i, (d z).2.1 i = 1)
    (ht : ∀ z, 0 ≤ (d z).2.2) (hts : ∀ z, (d z).2.2 < s)
    (hmin : ∀ z i, chartFiberInverse a (d z).1.1 ((d z).1.2 i) ∈
      minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1))
    (hID : ∀ z p, p ∈ convexHull ℝ (range (fun i => chartFiberInverse a (d z).1.1 ((d z).1.2 i))) →
      (d z).2.2 • p ∈ injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1)) :
    ∃ b > 0, ∀ᶠ h : Model n in 𝓝 0, ∀ z : P, ∃ i,
      b * ‖h‖^2 ≤ scaledNormalEnvelope a s (d z) i h := by
  have hi : ∀ z i, chartFiberInverse a (d z).1.1 (s • (d z).1.2 i) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1) := by
    intro z i
    rw [map_smul]
    exact contracted_minimizer_mem_injectivityDomain (hmin z i) hs hs1
  have hp : ∀ z, chartFiberInverse a (d z).1.1 ((d z).2.2 • ∑ j, (d z).2.1 j • (d z).1.2 j) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm (d z).1.1) := by
    intro z
    simp only [map_smul,map_sum]
    apply hID z
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw z i) (hsum z)
      (fun i _ => subset_convexHull ℝ _ (mem_range_self i))
  apply compact_smooth_data_transverse_growth (scaledNormalEnvelope a s) d hd
    (fun z => (d z).2.1) hw hsum
  · intro i
    exact (continuous_apply i).comp hd.snd.fst
  · intro z i
    exact scaledNormalEnvelope_contDiffAt i (hb z) (hp z) (hi z i)
  · intro z i
    exact scaledNormalEnvelope_zero a s (d z) i
  · intro z v
    exact scaledNormalEnvelope_mean hs.ne' (hb z) (hp z) (hi z) (hsum z) v
  · intro z v hv hle
    let L := chartFiberInverse a (d z).1.1
    have hLv : L v ≠ 0 := by
      intro he
      have hv0 : v = 0 := (chartFiberInverse_injective (hb z)) (he.trans (map_zero L).symm)
      simp only [hv0,norm_zero] at hv
      norm_num at hv
    have H := hmtw.finite_scaled_transverse_positive
      (fun i => L ((d z).1.2 i)) ((d z).2.1) (hw z) (hsum z) (hmin z)
      (ht z) (hts z) hs1 (hID z) hLv
    have hl : ∀ i, (d z).2.2 * inner ℝ
        (L ((d z).1.2 i) - ∑ j, (d z).2.1 j • L ((d z).1.2 j)) (L v) ≤ 0 := by
      intro i
      simpa only [scaledNormalEnvelope_first hs.ne' i (hb z) (hp z) (hi z i),
        map_sub,map_sum,map_smul,L] using hle i
    have HH := H hl
    simpa only [scaledNormalEnvelope_second _ (hb z) (hp z) (hi z _),
      map_smul,map_sum,L] using HH

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveUniformGrowth
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.active_configurations_uniform_growth
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a : M} {K : Set M} (hK : IsCompact K)
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source)
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : ℝ} (hT : T < 1)
    (hID : ∀ x ∈ K, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∃ b > 0, ∀ᶠ h : Model n in 𝓝 0,
      ∀ q ∈ activeConfiguration v a K T ι,
        b * ‖h‖^2 ≤ q.2.2 *
          (cTransform v (movingNormal a (q.1.1,h)) -
            cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) +
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) h -
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) 0 := by
  classical
  obtain ⟨s,hTs,hs1⟩ := exists_between (max_lt (show (0:ℝ)<1 by norm_num) hT)
  have hs : 0 < s := (le_max_left 0 T).trans_lt hTs
  have hTs' : T < s := (le_max_right 0 T).trans_lt hTs
  let Q := activeConfiguration (n := n) v a K T ι
  have hQ : IsCompact Q := compact_common_base_configurations
    (isCompact_active_coordinates hv hK hKa) T
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  have hmem (q : Q) (i : ι) := mem_active_coordinates hKa (q.2.1 i)
  have hbase (q : Q) : q.1.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target :=
    (hmem q (Classical.arbitrary ι)).1
  have H := hmtw.compact_scaled_envelope_growth a s hs hs1
    (fun q : Q => q.1) continuous_subtype_val hbase
    (fun q i => q.2.2.1 i) (fun q => q.2.2.2.1)
    (fun q => q.2.2.2.2.1) (fun q => q.2.2.2.2.2.trans_lt hTs')
    (fun q i => (hmem q i).2.1.1) (fun q p hp => hID _
      (hmem q (Classical.arbitrary ι)).2.2 p
      ((convexHull_mono (by rintro _ ⟨i,rfl⟩; exact (hmem q i).2.1)) hp)
      _ q.2.2.2.2)
  obtain ⟨b,hb,H⟩ := H
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh q hq
  obtain ⟨i,hi⟩ := hh ⟨q,hq⟩
  have hp := (hmem ⟨q,hq⟩ i).2.1
  have hsup := active_split_lower_support hv hp.1 hp.2 hs hs1
    (movingNormal a (q.1.1,h))
  have he : riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
      (s • chartFiberInverse a q.1.1 (q.1.2 i)) = movingNormal a (q.1.1,s • q.1.2 i) := by
    rw [movingNormal_eq (hbase ⟨q,hq⟩),map_smul]
  rw [he] at hsup
  have hsup' := mul_le_mul_of_nonneg_left hsup hq.2.2.2.1
  unfold scaledNormalEnvelope movingNormalCost at hi
  rw [movingNormal_zero (hbase ⟨q,hq⟩)] at hi
  change b * ‖h‖^2 ≤ _
  unfold movingNormalCost
  rw [movingNormal_zero (hbase ⟨q,hq⟩)]
  nlinarith [show q.2.2 * (-(cost (movingNormal a (q.1.1,h))
      (movingNormal a (q.1.1,s • q.1.2 i)) -
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
          (movingNormal a (q.1.1,s • q.1.2 i))) / s) =
      -(q.2.2 / s) * (cost (movingNormal a (q.1.1,h))
        (movingNormal a (q.1.1,s • q.1.2 i)) -
          cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
            (movingNormal a (q.1.1,s • q.1.2 i))) by ring]

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

lemma WeakMTW.active_hull_uniform_strict_growth
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a : M} {K : Set M} (hK : IsCompact K)
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source)
    {T : ℝ} (hT : T < 1)
    (hID : ∀ x ∈ K, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∀ᶠ h : Model n in 𝓝 0, ∀ x ∈ K,
      ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), ∀ t ∈ Icc (0:ℝ) T,
      h ≠ 0 →
      0 < t * (cTransform v (movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,h)) - cTransform v x) +
        cost (movingNormal a (extChartAt 𝓘(ℝ,Model n) a x,h)) (riemannianExp x (t • p)) -
        cost x (riemannianExp x (t • p)) := by
  classical
  let k := Module.finrank ℝ (Model n) + 1
  have H : ∀ᶠ h : Model n in 𝓝 0, ∀ m ∈ Finset.Icc 1 k,
      ∀ q ∈ activeConfiguration v a K T (Fin m), h ≠ 0 →
        0 < q.2.2 * (cTransform v (movingNormal a (q.1.1,h)) -
            cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) +
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) h -
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) 0 := by
    rw [Filter.eventually_all_finset]
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
    let : Nonempty (Fin m) := ⟨⟨0,hm0⟩⟩
    obtain ⟨b,hb,Hb⟩ := hmtw.active_configurations_uniform_growth
      (ι := Fin m) hv hK hKa hT hID
    filter_upwards [Hb] with h hh q hq hh0
    exact (mul_pos hb (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hh0))).trans_le (hh q hq)
  filter_upwards [H] with h hh x hx p hp t ht hh0
  let b := extChartAt 𝓘(ℝ,Model n) a x
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  let S := L '' activeLogs (n := n) v x
  have hp' : L p ∈ convexHull ℝ S := by
    change L p ∈ convexHull ℝ (L.toLinearMap '' activeLogs v x)
    rw [←L.toLinearMap.image_convexHull]
    exact ⟨p,hp,rfl⟩
  obtain ⟨m,hm0,hmk,z,w,hz,hw,hsum,hmean⟩ := finite_simplex_representation hp'
  let q : EnvelopeData (Model n) (Fin m) := ((b,z),(w,t))
  have hq : q ∈ activeConfiguration v a K T (Fin m) := by
    refine ⟨?_,hw,hsum,ht⟩
    intro i
    obtain ⟨r,hr,hri⟩ := hz i
    refine ⟨(⟨x,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),⟨hr,hx⟩,?_⟩
    have hLr : L r = tangentCoordChange 𝓘(ℝ,Model n) x a x r := by
      dsimp only [L]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
        (show x ∈ (chartAt (Model n) a).source by simpa only [extChartAt_source] using hKa hx)]
      rfl
    change (b,tangentCoordChange 𝓘(ℝ,Model n) x a x r) = (b,z i)
    rw [←hLr,hri]
  have hstrict := hh m (Finset.mem_Icc.mpr ⟨hm0,hmk⟩) q hq hh0
  have hbase : (extChartAt 𝓘(ℝ,Model n) a).symm b = x :=
    (extChartAt 𝓘(ℝ,Model n) a).left_inv (hKa hx)
  have hy : movingNormal a (b,t • ∑ i, w i • z i) = riemannianExp x (t • p) := by
    rw [hmean,←map_smul]
    exact movingNormal_trivialization (hKa hx) (t • p)
  have hx0 : movingNormal a (b,0) = x := by
    rw [movingNormal_zero ((extChartAt 𝓘(ℝ,Model n) a).map_source (hKa hx)),hbase]
  simpa only [q,movingNormalCost,hbase,hy,hx0,b] using hstrict

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_UniformLocalGap
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.uniform_local_scaled_gap
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {T : ℝ} (hT : T < 1)
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∃ δ > 0, ∀ x z : M, dist x z < δ → x ≠ z →
      ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), ∀ t ∈ Icc (0:ℝ) T,
        0 < t * (cTransform v z-cTransform v x) +
          cost z (riemannianExp x (t • p)) - cost x (riemannianExp x (t • p)) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let P := fun z : TangentBundle 𝓘(ℝ,Model n) M =>
    ∀ p ∈ convexHull ℝ (activeLogs (n := n) v z.1), ∀ t ∈ Icc (0:ℝ) T,
      riemannianExp z.1 z.2 ≠ z.1 →
      0 < t * (cTransform v (riemannianExp z.1 z.2)-cTransform v z.1) +
        cost (riemannianExp z.1 z.2) (riemannianExp z.1 (t • p)) -
        cost z.1 (riemannianExp z.1 (t • p))
  have H : ∀ᶠ r : ℝ in 𝓝 0, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2 ∈ minimizingVectors z.1 → ‖z.2‖=r → P z := by
    apply compact_eventually_fiberwise (isCompact_total_minimizingVectors (n := n) (M := M))
      continuous_bundle_norm (continuousAt_id (x := (0:ℝ)))
    rintro ⟨a,q⟩ _ he
    have hq : q = 0 := norm_eq_zero.mp he
    subst q
    obtain ⟨K,hKn,hKa,hK⟩ := local_compact_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) a).mem_nhds (mem_extChartAt_source a))
    have HG := hmtw.active_hull_uniform_strict_growth hv hK hKa hT
      (fun x _ p hp t ht => hID x p hp t ht)
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    have hχ0 : (χ (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 = 0 :=
      map_zero (tangentCoordChange 𝓘(ℝ,Model n) a a a)
    have hc : Tendsto (fun q : ℝ × TangentBundle 𝓘(ℝ,Model n) M => (χ q.2).2)
        (𝓝 (0,⟨a,0⟩)) (𝓝 0) := by
      have hχ : ContinuousAt χ (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) := continuousAt_extChartAt _
      have hh := hχ.snd.comp
        (f := fun q : ℝ × TangentBundle 𝓘(ℝ,Model n) M => q.2) (x := (0,⟨a,0⟩)) continuousAt_snd
      convert hh.tendsto using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [Function.comp_def,hχ0])
    have hbase : ∀ᶠ q : ℝ × TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (0,⟨a,0⟩), q.2.1 ∈ K :=
      ((FiberBundle.continuous_proj _ _).comp continuous_snd).continuousAt.preimage_mem_nhds hKn
    filter_upwards [hc.eventually HG,hbase] with q hG hqK p hp t ht hne
    have hm : movingNormal a (extChartAt 𝓘(ℝ,Model n) a q.2.1,(χ q.2).2) =
        riemannianExp q.2.1 q.2.2 := movingNormal_chart (hKa hqK) q.2.2
    have hn : (χ q.2).2 ≠ 0 := by
      intro hz
      rw [hz,movingNormal_zero ((extChartAt 𝓘(ℝ,Model n) a).map_source (hKa hqK)),
        (extChartAt 𝓘(ℝ,Model n) a).left_inv (hKa hqK)] at hm
      exact hne hm.symm
    have hh := hG q.2.1 hqK p hp t ht hn
    simpa only [hm] using hh
  obtain ⟨δ,hδ,Hδ⟩ := Metric.eventually_nhds_iff.mp H
  refine ⟨δ,hδ,?_⟩
  intro x z hxz hne p hp t ht
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) x z
  have hnq : ‖q‖ = dist x z := by rw [←hq,hqz]
  have hr : dist (dist x z) 0 < δ := by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hxz
  have hh := Hδ hr ⟨x,q⟩ hq hnq p hp t ht (by rw [hqz]; exact hne.symm)
  simpa only [hqz] using hh

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.uniform_graph_fiber_separation
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {T : ℝ} (hT : T < 1)
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∃ δ > 0, ∀ t ∈ Ioc (0:ℝ) T,
      ∀ z w : subgradientGraph (n := n) (cTransform v),
        dist z.1.1 w.1.1 < δ →
        graphProjection (cTransform v) t z = graphProjection (cTransform v) t w → z = w := by
  obtain ⟨δ,hδ,Hδ⟩ := hmtw.uniform_local_scaled_gap hv hT hID
  refine ⟨δ,hδ,?_⟩
  rintro t ht ⟨⟨x,p⟩,hp⟩ ⟨⟨z,q⟩,hq⟩ hdist he
  have hpH := normalSubdifferential_subset_active_hull hv x hp
  have hqH := normalSubdifferential_subset_active_hull hv z hq
  change riemannianExp x (t • p) = riemannianExp z (t • q) at he
  have hxz : x = z := by
    by_contra hn
    have h1 := Hδ x z hdist hn p hpH t ⟨ht.1.le,ht.2⟩
    have h2 := Hδ z x (by rwa [dist_comm]) (Ne.symm hn) q hqH t ⟨ht.1.le,ht.2⟩
    rw [he] at h1
    linarith
  subst z
  have hpq : t • p = t • q := riemannianExp_injOn_injectivityDomain x
    (hID x p hpH t ⟨ht.1.le,ht.2⟩) (hID x q hqH t ⟨ht.1.le,ht.2⟩) he
  have hpq' : p = q := (smul_right_injective _ ht.1.ne') hpq
  subst q
  rfl

lemma WeakMTW.exists_short_injective_graphProjection
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v) :
    ∃ τ > 0, τ < 1 ∧ ∀ t ∈ Ioc (0:ℝ) τ,
      Function.Injective (graphProjection (n := n) (cTransform v) t) := by
  obtain ⟨T,hT,hT1,H⟩ := exists_uniform_short_active_hull_contraction (n := n) (M := M)
  obtain ⟨δ,hδ,Hδ⟩ := hmtw.uniform_graph_fiber_separation hv hT1
    (fun x p hp t ht => H v x p hp t ht.1 ht.2)
  let D := Metric.diam (univ : Set M)
  have hD : 0 ≤ D := Metric.diam_nonneg
  let τ := min T (δ/(4*(D+1)))
  have hτ : 0 < τ := lt_min hT (div_pos hδ (by positivity))
  refine ⟨τ,hτ,(min_le_left _ _).trans_lt hT1,?_⟩
  intro t ht z w he
  apply Hδ t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩ z w _ he
  have hz := graphProjection_base_dist hv ht.1.le z
  have hw := graphProjection_base_dist hv ht.1.le w
  rw [←he] at hw
  have hd := dist_triangle z.1.1 (graphProjection (cTransform v) t z) w.1.1
  rw [dist_comm (graphProjection (cTransform v) t z) w.1.1] at hd
  have htδ : t * (4*(D+1)) ≤ δ :=
    (le_div_iff₀ (by positivity : 0 < 4*(D+1))).mp (ht.2.trans (min_le_right _ _))
  change dist z.1.1 (graphProjection (cTransform v) t z) ≤ t*D at hz
  change dist w.1.1 (graphProjection (cTransform v) t z) ≤ t*D at hw
  nlinarith [mul_nonneg ht.1.le hD]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ProjectionContinuation
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.extend_injective_graphProjection
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t)) :
    ∃ R, T<R ∧ R<1 ∧ ∀ t ∈ Ioc (0:ℝ) R,
      Function.Injective (graphProjection (n := n) (cTransform v) t) := by
  let : CompactSpace (subgradientGraph (n := n) (cTransform v)) :=
    isCompact_iff_compactSpace.mp (isCompact_subgradientGraph hv)
  have hTI := hmtw.injective_graphProjection_at_left_limit hv hT hT1 hinj
  have hID := hmtw.active_hull_precut_at_left_limit hv hT hT1 hinj
  obtain ⟨S,hTS,hS1,hSID⟩ := exists_extended_uniform_precut hv hT hT1 hID
  obtain ⟨δ,hδ,hsep⟩ := hmtw.uniform_graph_fiber_separation hv hS1 hSID
  have hnear : ∀ᶠ t in 𝓝 T, Function.Injective (graphProjection (n := n) (cTransform v) t) := by
    apply eventually_injective_of_uniform_local_injective
      (graphProjection (n := n) (cTransform v)) (continuous_graphProjection_family _)
      (fun z => z.1.1) ((FiberBundle.continuous_proj _ _).comp continuous_subtype_val) hδ hTI
    filter_upwards [eventually_gt_nhds hT,eventually_lt_nhds hTS] with t ht htS
    exact hsep t ⟨ht,htS.le⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let R := T+min (ε/2) ((1-T)/2)
  have hTR : T<R := by dsimp [R]; have : 0 < min (ε/2) ((1-T)/2) := lt_min (by linarith) (by linarith); linarith
  have hR1 : R<1 := by have := min_le_right (ε/2) ((1-T)/2); dsimp [R] <;> linarith
  have hRε : R<T+ε := by have := min_le_left (ε/2) ((1-T)/2); dsimp [R] <;> linarith
  refine ⟨R,hTR,hR1,?_⟩
  intro t ht
  by_cases htT : t<T
  · exact hinj t ⟨ht.1,htT⟩
  · apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt htT))]
    linarith [ht.2]

lemma WeakMTW.injective_graphProjection
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Function.Injective (graphProjection (n := n) (cTransform v) t) := by
  let A : Set ℝ := {T | 0<T ∧ T<1 ∧ ∀ s ∈ Ioc (0:ℝ) T,
    Function.Injective (graphProjection (n := n) (cTransform v) s)}
  obtain ⟨τ,hτ,hτ1,hτI⟩ := hmtw.exists_short_injective_graphProjection hv
  have hτA : τ∈A := ⟨hτ,hτ1,hτI⟩
  have hA : A.Nonempty := ⟨τ,hτA⟩
  have hAb : BddAbove A := ⟨1,fun _ h => h.2.1.le⟩
  have hB : 0 < sSup A := hτ.trans_le (le_csSup hAb hτA)
  have hB1 : sSup A≤1 := csSup_le hA (fun _ h => h.2.1.le)
  have hBI : ∀ s ∈ Ioo (0:ℝ) (sSup A),
      Function.Injective (graphProjection (n := n) (cTransform v) s) := by
    intro s hs
    obtain ⟨R,hRA,hsR⟩ := exists_lt_of_lt_csSup hA hs.2
    exact hRA.2.2 s ⟨hs.1,hsR.le⟩
  have heq : sSup A=1 := by
    apply le_antisymm hB1
    by_contra hn
    obtain ⟨R,hBR,hR1,hRI⟩ := hmtw.extend_injective_graphProjection hv hB (lt_of_not_ge hn) hBI
    have hRA : R∈A := ⟨hB.trans hBR,hR1,hRI⟩
    exact (not_lt_of_ge (le_csSup hAb hRA)) hBR
  apply hBI t
  exact ⟨ht,by rwa [heq]⟩

lemma WeakMTW.active_hull_precut
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), t • p ∈ injectivityDomain x :=
  hmtw.active_hull_precut_at_left_limit hv ht ht1
    (fun _ hs => hmtw.injective_graphProjection hv hs.1 (hs.2.trans ht1))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GlobalSupport
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.global_support
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ normalSubdifferential (cTransform v) x) :
    p ∈ minimizingVectors x ∧ ∀ a : M,
      cTransform v x+cost x (riemannianExp x p) ≤
        cTransform v a+cost a (riemannianExp x p) := by
  let z : subgradientGraph (n := n) (cTransform v) := ⟨⟨x,p⟩,hp⟩
  have H := graph_global_min_at_left_limit (continuous_cTransform hv) (by norm_num : (0:ℝ)<1)
    (fun t ht => hmtw.injective_graphProjection hv ht.1 ht.2) z
  simpa only [one_smul,div_one,graphProjection,z] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_GeometricEnvelope
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma WeakMTW.subgradient_dual_contact (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈normalSubdifferential (n := n) u x) :
    p∈minimizingVectors x ∧ contactGap u v x (riemannianExp x p)=0 := by
  have hs := hmtw.global_support hv (show p∈normalSubdifferential (cTransform v) x by rwa [←hdual.1])
  rw [←hdual.1] at hs
  refine ⟨hs.1,le_antisymm ?_ (dualPair_gap_nonneg hv hdual _ _)⟩
  have hc : v (riemannianExp x p) ≤ -u x-cost x (riemannianExp x p) := by
    rw [hdual.2]
    apply (cTransform_le_iff hu _ _).mpr
    intro a
    have H := hs.2 a
    rw [cost_symm (riemannianExp x p) a]
    linarith
  dsimp [contactGap]
  linarith

lemma WeakMTW.dual_hopfLax_identity (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    hopfLax t u = fun z => -hopfLax (1-t) v z := by
  funext z
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have hc := hmtw.subgradient_dual_contact hu hv hdual q.2
  let y := riemannianExp q.1.1 q.1.2
  have hsplit := splitNormalAction_contact hc.1 ht ht1
  change cost (riemannianExp q.1.1 0) (graphProjection u t q)/t+
    cost (graphProjection u t q) y/(1-t) = cost (riemannianExp q.1.1 0) y at hsplit
  rw [riemannianExp_zero,hq] at hsplit
  have hleft := hopfLax_le hu t z q.1.1
  have hright := hopfLax_le hv (1-t) z y
  rw [cost_symm y z] at hright
  have hcontact : u q.1.1+cost q.1.1 y+v y=0 := hc.2
  have hnonneg := dual_hopfLax_sum_nonneg hu hv hdual ht ht1 z
  linarith

lemma WeakMTW.hopfLax_graph_value (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : subgradientGraph (n := n) (cTransform v)) :
    hopfLax t (cTransform v) (graphProjection (cTransform v) t q) =
      cTransform v q.1.1+cost q.1.1 (graphProjection (cTransform v) t q)/t :=
  hopfLax_eq_of_min (continuous_cTransform hv) t _ _
    (global_min_of_injective_graphProjection (continuous_cTransform hv) ht
      (hmtw.injective_graphProjection hv ht ht1) q).2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_HopfSupports
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

lemma WeakMTW.uniform_hopfLax_C11 (hmtw : WeakMTW (n := n) (M := M)) (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ t : ℝ, 0<t → t<1 → ∀ u v : M → ℝ, Continuous u → Continuous v →
        IsCostDualPair u v →
        (∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          DifferentiableAt ℝ (fun z => hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z)) x) ∧
        LipschitzOnWith (Real.toNNReal (6*(B/t+B/(1-t))))
          (fderiv ℝ (fun z => hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm z)))
          (ball (extChartAt 𝓘(ℝ,Model n) a a) (r/4)) := by
  obtain ⟨B,hB,r,hr,hrT,H⟩ := uniform_hopfLax_chart_upper (n := n) a
  refine ⟨B,hB,r,hr,hrT,?_⟩
  intro t ht ht1 u v hu hv hdual
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let S := ball (χ a) r
  let f := fun z => hopfLax t u (χ.symm z)
  let C := B/t+B/(1-t)
  have hC : 0≤C := by dsimp [C] <;> positivity
  have hid := hmtw.dual_hopfLax_identity hu hv hdual ht ht1
  have hsup : ∀ x∈S, ∃ L U : Model n →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-C*‖y-x‖^2≤f y ∧ f y≤f x+U (y-x)+C*‖y-x‖^2 := by
    intro x hx
    obtain ⟨U,hU⟩ := H t ht u hu x hx
    obtain ⟨V,hV⟩ := H (1-t) (sub_pos.mpr ht1) v hv x hx
    refine ⟨-V,U,?_⟩
    intro y hy
    have hUy := hU y hy
    have hVy := hV y hy
    have hf (z : Model n) : hopfLax (1-t) v (χ.symm z) = -f z := by
      dsimp [f]
      rw [hid]
      simp only [neg_neg]
    change f y≤f x+U (y-x)+(B/t)*‖y-x‖^2 at hUy
    rw [hf y,hf x] at hVy
    have htB : 0≤B/t := by positivity
    have htB' : 0≤B/(1-t) := by positivity
    simp only [_root_.neg_apply]
    dsimp only [C]
    constructor
    · nlinarith [mul_nonneg htB (sq_nonneg ‖y-x‖)]
    · nlinarith [mul_nonneg htB' (sq_nonneg ‖y-x‖)]
  have hrem := quadratic_remainder_of_two_supports isOpen_ball hC hsup
  refine ⟨fun x hx => (hrem x hx).1,?_⟩
  change LipschitzOnWith (Real.toNNReal (6*C)) (fderiv ℝ f) (ball (χ a) (r/4))
  have he : Real.toNNReal (6*C) = (⟨6*C, mul_nonneg (by norm_num : (0:ℝ)≤6) hC⟩ : ℝ≥0) := by
    exact Real.toNNReal_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6) hC)
  rw [he]
  exact derivative_lipschitz_of_quadratic_remainder hr hC (fun x hx => (hrem x hx).2)

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

lemma WeakMTW.mdifferentiable_hopfLax (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) := by
  intro z
  obtain ⟨B,hB,r,hr,_,H⟩ := hmtw.uniform_hopfLax_C11 z
  apply mdifferentiableAt_of_chart_differentiable
  exact (H t ht ht1 u v hu hv hdual).1 _ (mem_ball_self hr)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_GraphInverse
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

def WeakMTW.graphHomeomorph (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    subgradientGraph (n := n) (cTransform v) ≃ₜ M :=
  (Equiv.ofBijective (graphProjection (cTransform v) t)
    ⟨hmtw.injective_graphProjection hv ht ht1,
      surjective_graphProjection (continuous_cTransform hv) ht⟩).toHomeomorphOfContinuousOpen
    (continuous_graphProjection _ _) (hmtw.isOpenMap_graphProjection hv ht ht1
      (fun x p hp=>hmtw.active_hull_precut hv ht ht1 x p
        (normalSubdifferential_subset_active_hull hv x hp)))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_MaximumJensenFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure MaximumJensenFamily {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo) (a c : M) (N : Set (Model n)) where
  poleSource : ∀ k,(F.row k).q.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source
  endpointSource : ∀ k,F.z k∈(extChartAt 𝓘(ℝ,Model n) c).source
  sample : ∀ k,JensenSamplesAt (modifiedDatum v α D (F.b k) Bo)
    (modifiedDatum v α D (F.b k) Bc) (F.t k) c (F.z k) N
  first : ∀ k,
    let e := hmtw.graphHomeomorph (continuous_modifiedDatum hv α D (F.b k) ho)
      (F.prefixTime k).1 (F.prefixTime k).2
    ChartFixedPrefixLimit a (modifiedDatum v α D (F.b k) Bo)
      (hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc)) (F.t k)
      (fun j=>e.symm ((extChartAt 𝓘(ℝ,Model n) c).symm ((sample k).z j))) (F.row k).q

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumDiagonal
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
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

abbrev MaximumJensenFamily.sampleIndex (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :=
  (J.first k).σ j

def MaximumJensenFamily.samplePoint (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    subgradientGraph (n := n) (cTransform (modifiedDatum v α D (F.b k) Bo)) :=
  (hmtw.graphHomeomorph (continuous_modifiedDatum hv α D (F.b k) ho)
    (F.prefixTime k).1 (F.prefixTime k).2).symm
      ((extChartAt 𝓘(ℝ,Model n) c).symm ((J.sample k).z (J.sampleIndex k j)))

def MaximumJensenFamily.sampleCenter (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) : Model n :=
  extChartAt 𝓘(ℝ,Model n) c ((J.sample k).Y ((J.sample k).z (J.sampleIndex k j)))

def MaximumJensenFamily.sampleGradient (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    Model n →L[ℝ] ℝ :=
  fderiv ℝ (chartOuterEnvelope (modifiedDatum v α D (F.b k) Bo) (F.t k) c)
      ((J.sample k).z (J.sampleIndex k j))+
    fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
      ((J.sample k).z (J.sampleIndex k j))

def MaximumJensenFamily.sampleH (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  coordinateCenterMatrix a (F.t k) (hopfLax (1-F.t k) (modifiedDatum v α D (F.b k) Bc))
    (graphBaseCoordinate a (J.samplePoint k j).1) (graphVelocityCoordinate a (J.samplePoint k j).1)

def MaximumJensenFamily.sampleL (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  coordinatePoleMatrix a (F.t k) (modifiedDatum v α D (F.b k) Bo)
    (graphBaseCoordinate a (J.samplePoint k j).1) (graphVelocityCoordinate a (J.samplePoint k j).1)

structure MaximumDiagonal (J : MaximumJensenFamily hmtw hv ho F a c N)
    (ε : ℕ → ℝ) (P : ℕ → ℕ → Prop) where
  ν : ℕ → ℕ
  poleSource : ∀ k,(J.samplePoint k (ν k)).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source
  chart : ∀ k,(J.sample k).z (J.sampleIndex k (ν k))∈(extChartAt 𝓘(ℝ,Model n) c).target
  baseClose : ∀ k,dist (graphBaseCoordinate a (J.samplePoint k (ν k)).1)
    (graphBaseCoordinate a (F.row k).q.1)<ε k
  velocityClose : ∀ k,dist (graphVelocityCoordinate a (J.samplePoint k (ν k)).1)
    (graphVelocityCoordinate a (F.row k).q.1)<ε k
  centerClose : ∀ k,dist (J.sampleCenter k (ν k))
    (extChartAt 𝓘(ℝ,Model n) c (riemannianExp (F.row k).q.1.1 (F.row k).q.1.2))<ε k
  gradientClose : ∀ k,‖J.sampleGradient k (ν k)‖<ε k
  HClose : ∀ k,‖J.sampleH k (ν k)-(J.first k).H‖<ε k
  LClose : ∀ k,‖J.sampleL k (ν k)-(J.first k).L‖<ε k
  activeClose : ∀ k,dist ((J.first k).pj (ν k)) (J.first k).pj₀<ε k
  weightClose : ∀ k,dist ((J.first k).w (ν k)) (J.first k).w₀<ε k
  extra : ∀ k,P k (ν k)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumReindex
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
section MaximumReindex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumJensenFamily.sampleProjection (J : MaximumJensenFamily hmtw hv ho F a c N)
    (k j:ℕ) :
    graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
      (J.samplePoint k j)=
      (extChartAt 𝓘(ℝ,Model n) c).symm ((J.sample k).z (J.sampleIndex k j)) := by
  exact (hmtw.graphHomeomorph (continuous_modifiedDatum hv α D (F.b k) ho)
    (F.prefixTime k).1 (F.prefixTime k).2).apply_symm_apply _

lemma MaximumDiagonal.endpointSource {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P) (k:ℕ) :
    graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
      (J.samplePoint k (S.ν k))∈(extChartAt 𝓘(ℝ,Model n) c).source := by
  rw [J.sampleProjection]
  exact (extChartAt 𝓘(ℝ,Model n) c).map_target (S.chart k)

lemma MaximumDiagonal.endpointChart {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P) (k:ℕ) :
    extChartAt 𝓘(ℝ,Model n) c
      (graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
        (J.samplePoint k (S.ν k)))=(J.sample k).z (J.sampleIndex k (S.ν k)) := by
  rw [J.sampleProjection]
  exact (extChartAt 𝓘(ℝ,Model n) c).right_inv (S.chart k)

end MaximumReindex
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterSequence
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
section MaximumCenterSequence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumJensenFamily.sampleSlope (J : MaximumJensenFamily hmtw hv ho F a c N) (k j:ℕ) : ℝ :=
  deriv (fun s=>modifiedScalar α D Bc (F.b k,s))
    (v ((J.sample k).Y ((J.sample k).z (J.sampleIndex k j))))

end MaximumCenterSequence
end WeakMTWTransport

end
end

end OAI
end


