-- Prove2me | Definitions.Def_OAIQ232A028
-- name    : OAIQ232A028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:29:55.893462+00:00
-- url     : https://prove2.me/theorems/63af0a56-a01c-4d49-8ab6-f9177bc6e89e
-- title:
--   Definitions bundle OAIQ232A028 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 28 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Contact_ActiveContinuationLocal`, `BiholderTransport_Contact_GraphCompact`, `BiholderTransport_Contact_GraphProjection`, `BiholderTransport_Contact_MovingCostSupport`, `BiholderTransport_Contact_SubgradientUpper`, `BiholderTransport_Coordinates_BranchJets`, `BiholderTransport_Coordinates_NormalCoordinates3`, `BiholderTransport_Coordinates_NormalSubdifferential`, `BiholderTransport_CostGeometry_BranchActiveGrowth`, `BiholderTransport_CostGeometry_BranchGrowth`, `BiholderTransport_CostGeometry_LimitIsolation`, `BiholderTransport_CostGeometry_Slack`, `BiholderTransport_CostGeometry_StrictDividedAction`, `BiholderTransport_CostGeometry_UniformLocalGap`, `BiholderTransport_Geodesics_GraphGlobalMinimal`, `BiholderTransport_LinearAlgebra_ScaledSlack`, `BiholderTransport_Regularity_LimitGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A025` and `OAIQ232A026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A030`; the proofs of `OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_active_outer_matrix`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_true_matrix`, `OAI.WeakMTWTransport.exists_parametric_short_lower_sequence` and `OAI.WeakMTWTransport.uniform_family_short_mdifferentiable`.
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
import Definitions.Def_OAIQ232A025
import Definitions.Def_OAIQ232A026

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_StrictDividedAction
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.finite_transverse_slack_strict (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0<t) (hts : t < s) (hs : s<1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {xi : TangentSpace 𝓘(ℝ,Model n) x} (hxi : xi≠0)
    (hortho : ∀ i, inner ℝ xi (p i-∑ j, w j • p j)=0) :
    (∑ i, w i*(hessianValue x (s • p i) xi/s)) <
      hessianValue x (t • (∑ i, w i • p i)) xi/t := by
  let r := ∑ i, w i • p i
  have hhyper : Convex ℝ {q : TangentSpace 𝓘(ℝ,Model n) x | inner ℝ xi q=inner ℝ xi r} := by
    intro u hu v hv a b ha hb hab
    simp only [mem_ofPred_eq,inner_add_right,real_inner_smul_right] at hu hv ⊢
    rw [hu,hv,←add_mul,hab,one_mul]
  have hsub : convexHull ℝ (range p) ⊆ {q | inner ℝ xi q=inner ℝ xi r} := by
    apply convexHull_min _ hhyper
    rintro q ⟨i,rfl⟩
    have hh := hortho i
    rw [inner_sub_right] at hh
    exact sub_eq_zero.mp hh
  have hc := hmtw.contracted_transverse_concaveOn_set (convex_convexHull ℝ (range p)) hID
    (fun u hu v hv => by rw [inner_sub_right,hsub hu,hsub hv,sub_self])
  have hj := hc.le_map_sum (t := Finset.univ) (w := w) (p := p)
    (fun i _ => (hw i).le) hsum (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  simp only [smul_eq_mul] at hj
  have hj' := div_le_div_of_nonneg_right hj ht.le
  rw [Finset.sum_div] at hj'
  have hlt : (∑ i, w i*(hessianValue x (s • p i) xi/s)) <
      ∑ i, w i*hessianValue x (t • p i) xi/t := by
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_div_assoc]
      exact (mul_lt_mul_of_pos_left (divided_hessian_strict_decrease (hmin i) ht hts hs hxi) (hw i)).le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨i,Finset.mem_univ i,?_⟩
      rw [mul_div_assoc]
      exact mul_lt_mul_of_pos_left (divided_hessian_strict_decrease (hmin i) ht hts hs hxi) (hw i)
  exact hlt.trans_le hj'

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalSubdifferential
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

lemma activeLogs_subset_normalSubdifferential {v : M → ℝ} (hv : Continuous v) (x : M) :
    activeLogs (n := n) v x ⊆ normalSubdifferential (cTransform v) x := by
  intro p hp
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    (-2:ℝ)*(normalCost x ((1/2:ℝ) • p) h-normalCost x ((1/2:ℝ) • p) 0)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hID).sub_const
      (normalCost x ((1/2:ℝ) • p) 0)).const_smul (-2:ℝ)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    ring
  intro ε hε
  filter_upwards [hasFDerivAt_affine_lower_support hD ε hε] with h hh
  have hs := active_split_lower_support hv hp.1 hp.2
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
  have hf0 : f 0=0 := by simp [f]
  rw [hf0,sub_zero] at hh
  simp only [innerSL_apply_apply] at hh
  apply hh.trans
  have he : f h = -(cost (riemannianExp x h) (riemannianExp x ((1/2:ℝ) • p)) -
      cost x (riemannianExp x ((1/2:ℝ) • p))) / (1/2:ℝ) := by
    dsimp [f,normalCost]
    rw [riemannianExp_zero]
    ring
  rw [he]
  exact hs

lemma active_hull_subset_normalSubdifferential {v : M → ℝ} (hv : Continuous v) (x : M) :
    convexHull ℝ (activeLogs (n := n) v x) ⊆ normalSubdifferential (cTransform v) x :=
  convexHull_min (activeLogs_subset_normalSubdifferential hv x)
    (convex_normalSubdifferential (cTransform v) x)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActiveContinuationLocal
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

lemma local_min_divided_cost_subgradient {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ} (ht : t≠0)
    (hID : t • p ∈ injectivityDomain x)
    (hmin : IsLocalMin (fun z => u z+cost z (riemannianExp x (t • p))/t) x) :
    p ∈ normalSubdifferential (n := n) u x := by
  let g := fun h : TangentSpace 𝓘(ℝ,Model n) x => (-t⁻¹)*normalCost x (t • p) h
  have hg : HasFDerivAt g (innerSL ℝ p) 0 := by
    apply ((normalCost_hasFDerivAt_zero hID).const_smul (-t⁻¹)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    field_simp
  apply smooth_lower_support_mem_normalSubdifferential hg
  have hm : ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      u x+cost x (riemannianExp x (t • p))/t≤
        u (riemannianExp x h)+cost (riemannianExp x h) (riemannianExp x (t • p))/t := by
    have hc := (continuous_riemannianExp (n := n) x).continuousAt (x := 0) |>.tendsto
    rw [riemannianExp_zero] at hc
    exact hc.eventually hmin
  filter_upwards [hm] with h hh
  dsimp only [g,normalCost]
  rw [riemannianExp_zero]
  simp only [div_eq_mul_inv] at hh
  nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_MovingCostSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma moving_half_cost_secant {A : Type*} [TopologicalSpace A]
    {Y : A → M} {a : A} (hY : ContinuousAt Y a) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ minimizingVectors x)
    (hya : Y a=riemannianExp x ((1/2:ℝ) • p))
    (h : TangentSpace 𝓘(ℝ,Model n) x) {K : ℝ} (hK : inner ℝ p h<K) :
    ∀ᶠ q : ℝ×A in 𝓝 (0,a), 0≤q.1 →
      -2*(cost (riemannianExp x (q.1 • h)) (Y q.2)-cost x (Y q.2))≤K*q.1 := by
  let y := riemannianExp x ((1/2:ℝ) • p)
  let d := extChartAt 𝓘(ℝ,Model n) y
  have hyS : y∈d.source := mem_extChartAt_source y
  have hyT : d y∈d.target := d.map_source hyS
  have hdy : d.symm (d y)=y := d.left_inv hyS
  have hID := contracted_minimizer_mem_injectivityDomain hp
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let F := fun q : Model n×ℝ => (2:ℝ)*cost (riemannianExp x (q.2 • h)) (d.symm q.1)
  have hA : ContMDiffAt 𝓘(ℝ,Model n×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×ℝ => riemannianExp x (q.2 • h)) (d y,0) :=
    (contMDiff_riemannianExp_fiber (n := n) x _).comp (d y,0)
      (contDiffAt_snd.smul contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Model n×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×ℝ => d.symm q.1) (d y,0) :=
    ((contMDiffWithinAt_extChartAt_symm_target y hyT).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hyT)).comp (d y,0) contDiffAt_fst.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨x,(1/2:ℝ) • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hID
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2)
      (riemannianExp x ((0:ℝ) • h),d.symm (d y)) := by
    simpa only [zero_smul,riemannianExp_zero,hdy] using hC
  have hF0 := hC'.comp (d y,0) (hA.prodMk hB)
  have hF : ContDiffAt ℝ ∞ F (d y,0) :=
    contDiffAt_const.mul hF0.contDiffAt
  have hD : HasDerivAt (fun r : ℝ => F (d y,r)) (-inner ℝ p h) 0 := by
    have hN : HasFDerivAt (normalCost x ((1/2:ℝ) • p))
        (innerSL ℝ (-((1/2:ℝ) • p))) ((id (0:ℝ)) • h) := by
      simpa only [id_eq,zero_smul] using normalCost_hasFDerivAt_zero hID
    have H := (hN.comp_hasDerivAt 0
      ((hasDerivAt_id (0:ℝ)).smul_const h)).const_mul (2:ℝ)
    apply H.congr_deriv (by
      simp only [innerSL_apply_apply,inner_neg_left,real_inner_smul_left,one_smul]
      ring) |>.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun r => by dsimp [F,normalCost,y]; rw [hdy])
  have hDF := hF.differentiableAt (by simp) |>.hasFDerivAt
  have hDs := hDF.comp_hasDerivAt 0 ((hasDerivAt_const (0:ℝ) (d y)).prodMk (hasDerivAt_id (0:ℝ)))
  have heD : fderiv ℝ F (d y,0) (0,1) = -inner ℝ p h := hDs.unique hD
  have H := contDiffAt_parametric_secant_lower
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    (K := -K) (by rw [heD]; linarith)
  have hySa : Y a∈d.source := hya.symm ▸ hyS
  have hcY : ContinuousAt (fun q : ℝ×A => Y q.2) (0,a) := hY.comp continuousAt_snd
  have hc : ContinuousAt (fun q : ℝ×A => (d (Y q.2),q.1)) (0,a) :=
    ((show ContinuousAt d (Y a) by rw [hya]; exact continuousAt_extChartAt y).comp (f := fun q : ℝ×A => Y q.2) (x := (0,a))
      hcY).prodMk continuousAt_fst
  have hc' : Tendsto (fun q : ℝ×A => (d (Y q.2),q.1)) (𝓝 (0,a)) (𝓝 (d y,0)) := by
    simpa only [hya] using hc.tendsto
  have hnear : ∀ᶠ q : ℝ×A in 𝓝 (0,a), Y q.2∈d.source :=
    hcY.preimage_mem_nhds ((isOpen_extChartAt_source y).mem_nhds hySa)
  filter_upwards [hc'.eventually H,hnear] with q hq hsrc ht
  have hh := hq ht
  dsimp only [F] at hh
  rw [d.left_inv hsrc,zero_smul,riemannianExp_zero] at hh
  linarith

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma active_directional_upper_support {v : M → ℝ} (hv : Continuous v) {x : M}
    (h : TangentSpace 𝓘(ℝ,Model n) x) {K : ℝ}
    (hK : ∀ p∈activeLogs (n := n) v x, inner ℝ p h<K) :
    ∀ᶠ t : ℝ in 𝓝 0, 0≤t →
      cTransform v (riemannianExp x (t • h))-cTransform v x≤K*t := by
  let Y := fun z : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp z.1 ((1/2:ℝ) • z.2)
  have hY : Continuous Y := (contMDiff_riemannianExp (n := n) (M := M)).continuous.comp
    ((contMDiff_tangentScale (E := Model n) (M := M)).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hg : ContinuousAt (fun t : ℝ => riemannianExp x (t • h)) 0 :=
    (continuous_riemannianExp x).continuousAt.comp (continuousAt_id.smul continuousAt_const)
  have H : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈activeLogs (n := n) v z.1 → z.1=riemannianExp x (t • h) →
      (0≤t → -2*(cost (riemannianExp x (t • h)) (Y z)-cost x (Y z))≤K*t) := by
    apply compact_eventually_fiberwise (isCompact_total_activeLogs hv)
      (FiberBundle.continuous_proj _ _) hg
    rintro ⟨a,p⟩ hp he
    simp only [zero_smul,riemannianExp_zero] at he
    subst a
    exact moving_half_cost_secant hY.continuousAt hp.1 rfl h (hK p hp)
  filter_upwards [H] with t ht ht0
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (riemannianExp x (t • h))
  have hh := ht ⟨riemannianExp x (t • h),p⟩ hp rfl ht0
  have hs := active_split_lower_support hv hp.1 hp.2
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) x
  dsimp only [Y] at hh
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SubgradientUpper
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

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalSubdifferential_subset_active_hull {v : M → ℝ} (hv : Continuous v) (x : M) :
    normalSubdifferential (cTransform v) x ⊆ convexHull ℝ (activeLogs (n := n) v x) := by
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  have : CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x) := FiniteDimensional.complete ℝ _
  intro p hp
  by_contra hn
  obtain ⟨f,K,hK,hpK⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (activeLogs (n := n) v x))
    (isCompact_convexHull_finiteDimensional (isCompact_activeLogs (n := n) hv x)).isClosed hn
  let h := (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).symm f
  have he : ∀ q : TangentSpace 𝓘(ℝ,Model n) x, inner ℝ q h=f q := by
    intro q
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hh := active_directional_upper_support hv h
    (fun q hq => by rw [he]; exact hK q (subset_convexHull ℝ _ hq))
  have H := normalSubdifferential_directional_le hp h hh
  rw [he] at H
  exact (not_lt_of_ge H hpK)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GraphProjection
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma global_min_divided_cost_subgradient {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t)
    (hmin : ∀ z : M, u x+cost x (riemannianExp x p)/t≤
      u z+cost z (riemannianExp x p)/t) :
    t⁻¹ • p∈normalSubdifferential (n := n) u x := by
  have hs : (0:ℝ)<1/2 := by norm_num
  have hs1 : (1/2:ℝ)<1 := by norm_num
  have htne : t≠0 := ht.ne'
  have hscale : (t/2) • (t⁻¹ • p)=(1/2:ℝ) • p := by
    rw [smul_smul]
    congr 1
    field_simp
  apply local_min_divided_cost_subgradient (t := t/2) (by positivity)
  · rw [hscale]
    exact contracted_minimizer_mem_injectivityDomain hp hs hs1
  · rw [hscale]
    apply Filter.Eventually.of_forall
    intro z
    have hh := hmin z
    have hu := (div_le_div_iff_of_pos_right ht).mpr
      (minimizing_split_upper_support hp hs hs1 z)
    have hc := minimizing_split_contact hp hs hs1
    have hx : cost x (riemannianExp x p)/t =
        cost x (riemannianExp x ((1/2:ℝ) • p))/(t/2)+(1-1/2)*‖p‖^2/2/t := by
      rw [←hc]
      field_simp
    have hz : (cost z (riemannianExp x ((1/2:ℝ) • p))/(1/2)+(1-1/2)*‖p‖^2/2)/t =
        cost z (riemannianExp x ((1/2:ℝ) • p))/(t/2)+(1-1/2)*‖p‖^2/2/t := by
      field_simp
    rw [hx] at hh
    rw [hz] at hu
    linarith

lemma surjective_graphProjection {u : M → ℝ} (hu : Continuous u) {t : ℝ} (ht : 0<t) :
    Function.Surjective (graphProjection (n := n) u t) := by
  intro y
  let : Nonempty M := ⟨y⟩
  obtain ⟨x,_,hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hu.add ((continuous_cost_left y).div_const t)).continuousOn
  obtain ⟨p,hp,hpy⟩ := exists_minimizing_vector (n := n) x y
  have hsub := global_min_divided_cost_subgradient hp ht
    (show ∀ z : M, u x+cost x (riemannianExp x p)/t≤
      u z+cost z (riemannianExp x p)/t by
      intro z
      rw [hpy]
      exact hmin (mem_univ z))
  refine ⟨⟨⟨x,t⁻¹ • p⟩,hsub⟩,?_⟩
  dsimp only [graphProjection]
  rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul,hpy]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GraphCompact
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

lemma isClosed_subgradientGraph {v : M → ℝ} (hv : Continuous v) :
    IsClosed (subgradientGraph (n := n) (cTransform v)) := by
  classical
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x,p⟩ hp
  have hn : p∉convexHull ℝ (activeLogs (n := n) v x) := by
    intro hh
    exact hp (active_hull_subset_normalSubdifferential hv x hh)
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  obtain ⟨f,K,hK,hpK⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (activeLogs (n := n) v x))
    (isCompact_convexHull_finiteDimensional (isCompact_activeLogs (n := n) hv x)).isClosed hn
  let e := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) x
  have hx : x∈e.baseSet := mem_baseSet_trivializationAt _ _ x
  let g : Model n →L[ℝ] ℝ := f.comp (e.continuousLinearEquivAt ℝ x hx).symm.toContinuousLinearMap
  let F := fun z : TangentBundle 𝓘(ℝ,Model n) M => g (e z).2
  have hF (z : TangentBundle 𝓘(ℝ,Model n) M) (hz : z.1∈e.baseSet) : ContinuousAt F z :=
    g.continuous.continuousAt.comp ((e.toOpenPartialHomeomorph.continuousAt
      (e.mem_source.mpr hz)).snd)
  have hFx (q : TangentSpace 𝓘(ℝ,Model n) x) : F ⟨x,q⟩=f q := by
    dsimp only [F,g,ContinuousLinearMap.comp_apply]
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ x hx q]
    exact congrArg f ((e.continuousLinearEquivAt ℝ x hx).symm_apply_apply q)
  have HF : ∀ᶠ y in 𝓝 x, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈activeLogs (n := n) v z.1 → z.1=y → F z<K := by
    apply compact_eventually_fiberwise (isCompact_total_activeLogs hv)
      (FiberBundle.continuous_proj _ _) (continuousAt_id (x := x))
    rintro ⟨a,q⟩ hq he
    change a=x at he
    subst a
    have hqK : F ⟨x,q⟩<K := by rw [hFx]; exact hK q (subset_convexHull ℝ _ hq)
    have hsnd : ContinuousAt (fun a : M × TangentBundle 𝓘(ℝ,Model n) M => a.2)
        (x,⟨x,q⟩) := continuousAt_snd
    have hc : ContinuousAt (fun a : M × TangentBundle 𝓘(ℝ,Model n) M => F a.2)
        (x,⟨x,q⟩) := ContinuousAt.comp
          (f := fun a : M × TangentBundle 𝓘(ℝ,Model n) M => a.2)
          (g := F) (x := (x,⟨x,q⟩)) (hF ⟨x,q⟩ hx) hsnd
    exact hc.eventually_lt continuousAt_const hqK
  have hproj : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
    FiberBundle.continuous_proj _ _
  have HK : ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 ⟨x,p⟩, K<F z :=
    continuousAt_const.eventually_lt (hF ⟨x,p⟩ hx) (by rw [hFx]; exact hpK)
  have HB : ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 ⟨x,p⟩, z.1∈e.baseSet :=
    hproj.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)
  filter_upwards [hproj.continuousAt.eventually HF,HK,HB] with z hz hzK hzB
  intro hzG
  have hzh : z.2 ∈ convexHull ℝ (activeLogs (n := n) v z.1) :=
    normalSubdifferential_subset_active_hull hv z.1 hzG
  let L : TangentSpace 𝓘(ℝ,Model n) z.1 →L[ℝ] ℝ :=
    g.comp (e.continuousLinearMapAt ℝ z.1)
  have hLe (q : TangentSpace 𝓘(ℝ,Model n) z.1) : L q=F ⟨z.1,q⟩ := by
    dsimp only [L,F,ContinuousLinearMap.comp_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hzB]
  have hsub : activeLogs (n := n) v z.1 ⊆ {q | L q≤K} := by
    intro q hq
    rw [mem_ofPred_eq,hLe]
    exact (hz ⟨z.1,q⟩ hq rfl).le
  have hcv : Convex ℝ {q : TangentSpace 𝓘(ℝ,Model n) z.1 | L q≤K} :=
    convex_halfSpace_le L.toLinearMap.isLinear K
  have hbound := convexHull_min hsub hcv hzh
  change L z.2≤K at hbound
  rw [hLe] at hbound
  exact not_lt_of_ge hbound hzK

lemma isCompact_subgradientGraph {v : M → ℝ} (hv : Continuous v) :
    IsCompact (subgradientGraph (n := n) (cTransform v)) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  apply (isCompact_bundle_disk (F := Model n)
    (E := fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
    (isClosed_subgradientGraph hv)
  intro z hz
  exact active_hull_norm_le_diam (normalSubdifferential_subset_active_hull hv z.1 hz)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_BranchJets
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

lemma cost_branch_normal_jets {x : M} {r : TangentSpace 𝓘(ℝ,Model n) x}
    {T : ℝ} (hT : 0 < T) {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • r)))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, t • r ∈ injectivityDomain x) :
    let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      G (riemannianExp x h,riemannianExp x (T • r))
    ContDiffAt ℝ ∞ f 0 ∧ HasFDerivAt f (innerSL ℝ (-(T • r))) 0 ∧
      ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x,
      Tendsto (fun t : ℝ => hessianValue x (t • r) ξ) (𝓝[<] T)
        (𝓝 (fderiv ℝ (fderiv ℝ f) 0 ξ ξ)) := by
  let F := fun (t : ℝ) (h : TangentSpace 𝓘(ℝ,Model n) x) =>
    G (riemannianExp x h,riemannianExp x (t • r))
  have hfamily : ContDiffAt ℝ ∞ (Function.uncurry F) (T,0) := smooth_branch_normal_family hG
  have hFT : ContDiffAt ℝ ∞ (F T) 0 := hfamily.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have H : ∀ᶠ t in 𝓝[<] T, t • r ∈ injectivityDomain x ∧
      normalCost x (t • r) =ᶠ[𝓝 0] F t := by
    filter_upwards [(cost_branch_normal_eventuallyEq hagree).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht ht0 htT
    have htID := hID t ⟨ht0,htT⟩
    exact ⟨htID,ht htID⟩
  have hL : ContinuousAt (fun t => fderiv ℝ (F t) 0) T :=
    (ContDiffAt.partial_snd_fderiv hfamily).continuousAt.comp (f := fun t : ℝ => (t,(0 : TangentSpace 𝓘(ℝ,Model n) x)))
      (continuousAt_id.prodMk continuousAt_const)
  have hLe : fderiv ℝ (F T) 0 = innerSL ℝ (-(T • r)) := by
    have hR : ContinuousAt (fun t : ℝ => innerSL ℝ (-(t • r))) T := by fun_prop
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[<] T)
      (hL.tendsto.mono_left nhdsWithin_le_nhds) (hR.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [H] with t ht
    rw [←ht.2.fderiv_eq]
    exact (normalCost_hasFDerivAt_zero ht.1).fderiv
  refine ⟨hFT,?_,?_⟩
  · rw [←hLe]
    exact (hFT.differentiableAt (by simp)).hasFDerivAt
  · intro ξ
    have hB : ContinuousAt (fun t => fderiv ℝ (fderiv ℝ (F t)) 0 ξ ξ) T :=
      (((ContDiffAt.partial_snd_fderiv_two hfamily).continuousAt.comp (f := fun t : ℝ => (t,(0 : TangentSpace 𝓘(ℝ,Model n) x)))
        (continuousAt_id.prodMk continuousAt_const)).clm_apply continuousAt_const).clm_apply continuousAt_const
    apply (hB.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [H] with t ht
    rw [hessianValue_eq_normalHessian ht.1]
    dsimp only [normalHessian]
    rw [ht.2.fderiv.fderiv_eq]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates3
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

lemma hessianValue_zero (x : M) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    hessianValue x 0 xi = ‖xi‖^2 := by
  have hA := (hessianValue_contDiffAt (zero_mem_injectivityDomain (n := n) x) xi).continuousAt
  have hl : ContinuousAt (fun r : ℝ => r • xi) 0 := continuousAt_id.smul continuousAt_const
  have h0 : (0:ℝ) • xi = 0 := zero_smul ℝ xi
  have hc : ContinuousAt (fun r : ℝ => hessianValue x (r • xi) xi) 0 := by
    exact (show ContinuousAt (fun q => hessianValue x q xi) ((0:ℝ) • xi) by simpa using hA).comp (x := (0:ℝ)) (f := fun r : ℝ => r • xi) hl
  have he : ∀ᶠ r : ℝ in 𝓝 0, r • xi ∈ injectivityDomain x := by
    exact hl.preimage_mem_nhds ((isOpen_injectivityDomain x).mem_nhds (by simpa using zero_mem_injectivityDomain (n := n) x))
  have heq : (fun r : ℝ => hessianValue x (r • xi) xi) =ᶠ[𝓝[≠] 0] (fun _ => ‖xi‖^2) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hr0
    exact hessianValue_contracted_radial hr0 hr
  have H := tendsto_nhds_unique_of_eventuallyEq (hc.mono_left nhdsWithin_le_nhds)
    (continuousAt_const.mono_left nhdsWithin_le_nhds) heq
  simpa only [zero_smul] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchGrowth
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

lemma WeakMTW.branch_transverse_slack_strict (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {T s : ℝ} (hT : 0<T) (hTs : T < s) (hs : s<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {ξ : TangentSpace 𝓘(ℝ,Model n) x} (hξ : ξ≠0)
    (hortho : ∀ i, inner ℝ ξ (p i-∑ j, w j • p j)=0) {A : ℝ}
    (hlim : Tendsto (fun t => hessianValue x (t • (∑ j, w j • p j)) ξ) (𝓝[<] T) (𝓝 A)) :
    (∑ i, w i*(hessianValue x (s • p i) ξ/s)) < A/T := by
  obtain ⟨a,hTa,has⟩ := exists_between hTs
  have hlim' := hlim.div (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hT.ne'
  have hle : (∑ i, w i*(hessianValue x (a • p i) ξ/a)) ≤ A/T := by
    apply ge_of_tendsto hlim'
    filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htT
    exact (hmtw.finite_transverse_slack_strict p w hw hsum hmin ht (htT.trans hTa)
      (has.trans hs) (hID t ⟨ht,htT⟩) hξ hortho).le
  apply lt_of_lt_of_le _ hle
  apply Finset.sum_lt_sum
  · intro i _
    exact (mul_lt_mul_of_pos_left
      (divided_hessian_strict_decrease (hmin i) (hT.trans hTa) has hs hξ) (hw i)).le
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_left
      (divided_hessian_strict_decrease (hmin i) (hT.trans hTa) has hs hξ) (hw i)⟩

lemma finite_normal_branch_envelope_growth
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {T s : ℝ} (hT : 0<T) (hs0 : 0 < s) (hs : s<1)
    (g : TangentSpace 𝓘(ℝ,Model n) x → ℝ) (hg : ContDiffAt ℝ 2 g 0)
    (hgfirst : HasFDerivAt g (innerSL ℝ (-(T • (∑ j, w j • p j)))) 0)
    (hslack : ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x, ξ≠0 →
      (∀ i, inner ℝ ξ (p i-∑ j, w j • p j)=0) →
      (∑ i, w i*(hessianValue x (s • p i) ξ/s)) < fderiv ℝ (fderiv ℝ g) 0 ξ ξ/T) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0, ∃ i,
      b*‖h‖^2≤ (g h-g 0)/T-
        (normalCost x (s • p i) h-normalCost x (s • p i) 0)/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let r := ∑ j, w j • p j
  have hsi : ∀ i, s • p i ∈ injectivityDomain x :=
    fun i => contracted_minimizer_mem_injectivityDomain (hmin i) hs0 hs
  let f := fun i (h : TangentSpace 𝓘(ℝ,Model n) x) =>
    T⁻¹*(g h-g 0)-s⁻¹*(normalCost x (s • p i) h-normalCost x (s • p i) 0)
  have hleft : ContDiffAt ℝ 2 g 0 := hg
  have hright : ∀ i, ContDiffAt ℝ 2 (normalCost x (s • p i)) 0 :=
    fun i => (normalCost_contDiffAt (hsi i)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := fun i =>
    (contDiffAt_const.mul (hleft.sub contDiffAt_const)).sub
      (contDiffAt_const.mul ((hright i).sub contDiffAt_const))
  have hfirst : ∀ i, fderiv ℝ (f i) 0=innerSL ℝ (p i-r) := by
    intro i
    have H := ((hgfirst.sub_const (g 0)).const_smul T⁻¹).sub
      (((normalCost_hasFDerivAt_zero (hsi i)).sub_const (normalCost x (s • p i) 0)).const_smul s⁻¹)
    have H' : HasFDerivAt (f i) (innerSL ℝ (p i-r)) 0 := by
      apply H.congr_fderiv
      ext v
      simp only [_root_.sub_apply,_root_.smul_apply,innerSL_apply_apply,inner_neg_left,
        real_inner_smul_left,inner_sub_left,smul_eq_mul]
      field_simp [hT.ne', hs0.ne']
      ring
    exact H'.fderiv
  have hsecond : ∀ i v, fderiv ℝ (fderiv ℝ (f i)) 0 v v=
      fderiv ℝ (fderiv ℝ g) 0 v v/T-hessianValue x (s • p i) v/s := by
    intro i v
    rw [second_fderiv_scaled_differences hleft (hright i)]
    rw [hessianValue_eq_normalHessian (hsi i)]
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
    have H := hslack v hv hortho
    simp only [hsecond,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
    exact sub_pos.mpr H
  obtain ⟨b,hb,H⟩ := finite_smooth_transverse_growth f hf (fun i => by simp [f]) w hw hsum hmean hpos
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  refine ⟨i,?_⟩
  simpa only [f,r,div_eq_mul_inv,mul_comm] using hi

lemma WeakMTW.finite_branch_cost_growth (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {T s : ℝ} (hT : 0<T) (hTs : T < s) (hs : s<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • (∑ i, w i • p i))))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • (∑ i, w i • p i)⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0, ∃ i,
      b*‖h‖^2≤
        (G (riemannianExp x h,riemannianExp x (T • (∑ j, w j • p j)))-
          G (x,riemannianExp x (T • (∑ j, w j • p j))))/T-
        (normalCost x (s • p i) h-normalCost x (s • p i) 0)/s := by
  let r := ∑ j, w j • p j
  let g := fun h : TangentSpace 𝓘(ℝ,Model n) x => G (riemannianExp x h,riemannianExp x (T • r))
  have hrh : r ∈ convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hw i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  obtain ⟨hg,hgfirst,hglim⟩ := cost_branch_normal_jets hT hG hagree (fun t ht => hID t ht r hrh)
  have hg2 : ContDiffAt ℝ 2 g 0 := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := finite_normal_branch_envelope_growth p w hw hsum hmin hT (hT.trans hTs) hs g hg2 hgfirst
    (fun ξ hξ ho => hmtw.branch_transverse_slack_strict p w hw hsum hmin hT hTs hs hID hξ ho (hglim ξ))
  simpa only [g,r,riemannianExp_zero] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchActiveGrowth
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

lemma WeakMTW.active_hull_branch_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • q ∈ injectivityDomain x)
    {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • p)))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ b>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      b*‖h‖^2 ≤ cTransform v (riemannianExp x h)-cTransform v x+
        (G (riemannianExp x h,riemannianExp x (T • p))-G (x,riemannianExp x (T • p)))/T := by
  obtain ⟨ι,inst,z,w,hz,_,hw,hsum,heq⟩ := eq_pos_convex_span_of_mem_convexHull hp
  let : Fintype ι := inst
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  have hsub : convexHull ℝ (range z) ⊆ convexHull ℝ (activeLogs (n := n) v x) := convexHull_mono hz
  obtain ⟨s,hTs,hs⟩ := exists_between hT1
  obtain ⟨b,hb,H⟩ := hmtw.finite_branch_cost_growth z w hw hsum
    (fun i => (hz (mem_range_self i)).1) hT hTs hs
    (fun t ht q hq => hID t ht q (hsub hq)) (by simpa only [heq] using hG)
    (by simpa only [heq] using hagree)
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh
  obtain ⟨i,hi⟩ := hh
  have hiA := hz (mem_range_self i)
  have hsup := active_split_lower_support hv hiA.1 hiA.2 (hT.trans hTs) hs (riemannianExp x h)
  simp only [normalCost,riemannianExp_zero,heq] at hi
  rw [neg_div] at hsup
  linarith

lemma WeakMTW.active_hull_branch_strict_growth (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hID : ∀ t ∈ Ioo (0:ℝ) T, ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x),
      t • q ∈ injectivityDomain x)
    {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • p)))
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • p⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∀ᶠ a in 𝓝 x, a≠x → cTransform v x+G (x,riemannianExp x (T • p))/T <
      cTransform v a+G (a,riemannianExp x (T • p))/T := by
  obtain ⟨b,hb,H⟩ := hmtw.active_hull_branch_growth hv hp hT hT1 hID hG hagree
  have hh := metric_local_growth_of_normal (n := n)
    (f := fun a => cTransform v a+G (a,riemannianExp x (T • p))/T)
    (b := b) (x := x) (by
      filter_upwards [H] with h hh
      rw [sub_div] at hh
      linarith)
  filter_upwards [hh] with a ha hax
  have hd : 0<dist x a := dist_pos.mpr hax.symm
  have hpos := mul_pos hb (sq_pos_of_pos hd)
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GraphGlobalMinimal
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

lemma exists_minimizing_graph_point {u : M → ℝ} (hu : Continuous u)
    {t : ℝ} (ht : 0<t) (y : M) :
    ∃ z : subgradientGraph (n := n) u, graphProjection u t z=y ∧
      t • z.1.2∈minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 y/t≤u a+cost a y/t := by
  let : Nonempty M := ⟨y⟩
  obtain ⟨x,_,hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hu.add ((continuous_cost_left y).div_const t)).continuousOn
  obtain ⟨p,hp,hpy⟩ := exists_minimizing_vector (n := n) x y
  have hsub := global_min_divided_cost_subgradient hp ht
    (show ∀ z : M, u x+cost x (riemannianExp x p)/t≤
      u z+cost z (riemannianExp x p)/t by
      intro z
      rw [hpy]
      exact hmin (mem_univ z))
  refine ⟨⟨⟨x,t⁻¹ • p⟩,hsub⟩,?_,?_,fun a => hmin (mem_univ a)⟩
  · dsimp only [graphProjection]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul,hpy]
  · simpa only [smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hp

lemma global_min_of_injective_graphProjection {u : M → ℝ} (hu : Continuous u)
    {t : ℝ} (ht : 0<t) (hinj : Function.Injective (graphProjection (n := n) u t))
    (z : subgradientGraph (n := n) u) :
    t • z.1.2∈minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u t z)/t≤
        u a+cost a (graphProjection u t z)/t := by
  obtain ⟨w,hw,hmin,hglobal⟩ := exists_minimizing_graph_point (n := n) hu ht (graphProjection u t z)
  have he : w=z := hinj hw
  subst w
  exact ⟨hmin,hglobal⟩

lemma unique_minimizing_direction_of_injective_graphProjection {u : M → ℝ}
    {t : ℝ} (ht : 0<t) (hinj : Function.Injective (graphProjection (n := n) u t))
    (z : subgradientGraph (n := n) u)
    (hmin : ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u t z)/t≤
      u a+cost a (graphProjection u t z)/t)
    {q : TangentSpace 𝓘(ℝ,Model n) z.1.1} (hq : q∈minimizingVectors z.1.1)
    (hqe : riemannianExp z.1.1 q=graphProjection u t z) : q=t • z.1.2 := by
  have hsub := global_min_divided_cost_subgradient hq ht
    (show ∀ a : M, u z.1.1+cost z.1.1 (riemannianExp z.1.1 q)/t≤
      u a+cost a (riemannianExp z.1.1 q)/t by simpa only [hqe] using hmin)
  let w : subgradientGraph (n := n) u := ⟨⟨z.1.1,t⁻¹ • q⟩,hsub⟩
  have hw : graphProjection u t w=graphProjection u t z := by
    dsimp only [graphProjection,w]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    exact hqe
  have he : w=z := hinj hw
  have heval := congrArg Subtype.val he
  have hp : t⁻¹ • q=z.1.2 := by
    exact TotalSpace.mk_injective z.1.1 heval
  calc
    q = t • (t⁻¹ • q) := by rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    _ = t • z.1.2 := congrArg (t • ·) hp

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LimitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff Pointwise

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma graph_global_min_at_left_limit {u : M → ℝ} (hu : Continuous u)
    {T : ℝ} (hT : 0<T)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) u t))
    (z : subgradientGraph (n := n) u) :
    T • z.1.2 ∈ minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u T z)/T ≤
        u a+cost a (graphProjection u T z)/T := by
  have H : ∀ᶠ t in 𝓝[<] T, t • z.1.2 ∈ minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u t z)/t ≤
        u a+cost a (graphProjection u t z)/t := by
    filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htT
    exact global_min_of_injective_graphProjection hu ht (hinj t ⟨ht,htT⟩) z
  refine ⟨?_,?_⟩
  · have hcs : Continuous (fun t : ℝ => t • z.1.2) := continuous_id.smul continuous_const
    apply (isClosed_minimizingVectors z.1.1).mem_of_tendsto
      (hcs.continuousAt.tendsto.mono_left (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds))
    exact H.mono (fun _ h => h.1)
  · intro a
    have hc (b : M) : ContinuousAt (fun t => u b+cost b (graphProjection u t z)/t) T :=
      continuousAt_const.add (((continuous_cost_right b).continuousAt.comp
        ((continuous_graphProjection_family u).continuousAt.comp
          (f := fun t : ℝ => (t,z)) (continuousAt_id.prodMk continuousAt_const))).div continuousAt_id hT.ne')
    exact le_of_tendsto_of_tendsto (b := 𝓝[<] T)
      ((hc z.1.1).tendsto.mono_left nhdsWithin_le_nhds)
      ((hc a).tendsto.mono_left nhdsWithin_le_nhds) (H.mono (fun _ h => h.2 a))

end

open Set Filter
open scoped Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_LimitIsolation
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

lemma WeakMTW.isolated_graph_fiber_at_left_limit
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t))
    (z : subgradientGraph (n := n) (cTransform v)) :
    ∀ᶠ w in 𝓝 z, graphProjection (cTransform v) T w=graphProjection (cTransform v) T z → w=z := by
  have hglobal := graph_global_min_at_left_limit (continuous_cTransform hv) hT hinj
  have hmin (x : M) : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x := by
    intro p hp
    exact (hglobal ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩).1
  have hp := normalSubdifferential_subset_active_hull hv z.1.1 z.2
  have hreg := hmtw.active_hull_nonconjugate_of_minimizing hT hT1 (hmin z.1.1) hp
  obtain ⟨G,hG,hagree⟩ := exists_smooth_cost_branch (tangentScale T z.1) hreg
  have hbranch := cost_branch_agrees_on_minimizing hG hagree
  have hbase := hmtw.active_hull_branch_strict_growth hv hp hT hT1
    (active_hull_interior_below_minimizing hT (hmin z.1.1)) hG hagree
  obtain ⟨U,hU,hzU,hUinj⟩ := joint_exp_locally_injective_of_nonconjugate (tangentScale T z.1) hreg
  have hscale : Continuous (fun w : subgradientGraph (n := n) (cTransform v) => tangentScale T w.1) :=
    contMDiff_tangentScale.continuous.comp (continuous_const.prodMk continuous_subtype_val)
  have hproj : Continuous (fun w : subgradientGraph (n := n) (cTransform v) => w.1.1) :=
    (FiberBundle.continuous_proj _ _).comp continuous_subtype_val
  have hcostz : cost z.1.1 (graphProjection (cTransform v) T z)=
      G (z.1.1,graphProjection (cTransform v) T z) :=
    hbranch.self_of_nhds (hglobal z).1
  filter_upwards [hscale.continuousAt.eventually hbranch,
    hscale.continuousAt.preimage_mem_nhds (hU.mem_nhds hzU),
    hproj.continuousAt.eventually hbase] with w hwG hwU hwbase he
  have hcostw : cost w.1.1 (graphProjection (cTransform v) T w)=
      G (w.1.1,graphProjection (cTransform v) T w) := hwG (hglobal w).1
  have hsame : w.1.1=z.1.1 := by
    by_contra hn
    have hlt := hwbase hn
    change cTransform v z.1.1+G (z.1.1,graphProjection (cTransform v) T z)/T <
      cTransform v w.1.1+G (w.1.1,graphProjection (cTransform v) T z)/T at hlt
    rw [he] at hcostw
    rw [←hcostz,←hcostw] at hlt
    have hle := (hglobal w).2 z.1.1
    rw [he] at hle
    exact (not_lt_of_ge hle) hlt
  apply Subtype.ext
  apply tangentScale_injective hT.ne'
  exact hUinj hwU hzU (Prod.ext hsame he)

lemma WeakMTW.injective_graphProjection_at_left_limit
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t)) :
    Function.Injective (graphProjection (n := n) (cTransform v) T) := by
  let : CompactSpace (subgradientGraph (n := n) (cTransform v)) :=
    isCompact_iff_compactSpace.mp (isCompact_subgradientGraph hv)
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (Model n) M
  let : T2Space (TangentBundle 𝓘(ℝ,Model n) M) := bundle_totalSpace_t2
  have hclosure : T ∈ closure {t | Function.Bijective (graphProjection (n := n) (cTransform v) t)} := by
    apply mem_closure_of_frequently_of_tendsto
      (f := fun t : ℝ => t) (b := 𝓝[<] T)
    · apply Filter.Eventually.frequently
      filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht htT
      exact ⟨hinj t ⟨ht,htT⟩,surjective_graphProjection (continuous_cTransform hv) ht⟩
    · exact tendsto_id.mono_right nhdsWithin_le_nhds
  intro z w he
  have hconn := isPreconnected_fiber_of_mem_closure_bijective
    (graphProjection (n := n) (cTransform v)) (continuous_graphProjection_family _) hclosure
    (graphProjection (cTransform v) T z)
  have hs : {q : subgradientGraph (n := n) (cTransform v) | graphProjection (cTransform v) T q=graphProjection (cTransform v) T z}.Subsingleton := by
    apply fiber_subsingleton_of_preconnected_isolated hconn
    intro q hq
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp (hmtw.isolated_graph_fiber_at_left_limit hv hT hT1 hinj q)
    refine ⟨U,hU,hqU,?_⟩
    intro r hr
    exact hUP hr.1 (hr.2.trans hq.symm)
  exact hs rfl he.symm

lemma WeakMTW.active_hull_precut_at_left_limit
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t)) :
    ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ injectivityDomain x := by
  have hTI := hmtw.injective_graphProjection_at_left_limit hv hT hT1 hinj
  have hglobal := global_min_of_injective_graphProjection (continuous_cTransform hv) hT hTI
  have hmin (x : M) : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x := by
    intro p hp
    exact (hglobal ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩).1
  intro x p hp
  apply mem_injectivityDomain_of_nonconjugate_unique
    (hmtw.active_hull_nonconjugate_of_minimizing hT hT1 (hmin x) hp)
  intro q hq he
  let z : subgradientGraph (n := n) (cTransform v) :=
    ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩
  exact unique_minimizing_direction_of_injective_graphProjection hT hTI z (hglobal z).2 hq he

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_Slack
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.finite_nonnegative_transverse_slack_strict
    (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] {x : M} (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s < 1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {xi : TangentSpace 𝓘(ℝ,Model n) x} (hxi : xi ≠ 0)
    (hortho : ∀ i, 0 < w i → inner ℝ xi (p i - ∑ j, w j • p j) = 0) :
    (∑ i, w i * (hessianValue x (s • p i) xi / s)) <
      hessianValue x (t • (∑ i, w i • p i)) xi / t := by
  classical
  let S := Finset.univ.filter (fun i => 0 < w i)
  let r := ∑ i, w i • p i
  let C := convexHull ℝ (range p) ∩ {q | inner ℝ xi q = inner ℝ xi r}
  have hhyper : Convex ℝ {q : TangentSpace 𝓘(ℝ,Model n) x | inner ℝ xi q = inner ℝ xi r} := by
    intro u hu v hv a b ha hb hab
    simp only [mem_ofPred_eq,inner_add_right,real_inner_smul_right] at hu hv ⊢
    rw [hu,hv,←add_mul,hab,one_mul]
  have hC : Convex ℝ C := (convex_convexHull ℝ (range p)).inter hhyper
  have hS : ∀ i ∈ S, p i ∈ C := by
    intro i hi
    refine ⟨subset_convexHull ℝ (range p) (mem_range_self i),?_⟩
    exact sub_eq_zero.mp (by simpa only [inner_sub_right] using hortho i (Finset.mem_filter.mp hi).2)
  have hsumS : ∑ i ∈ S, w i = 1 := by
    have H := sum_filter_positive_weights w hw (fun _ => (1:ℝ))
    simpa only [S,smul_eq_mul,mul_one,hsum] using H
  have hc := hmtw.contracted_transverse_concaveOn_set hC (fun q hq => hID q hq.1)
    (fun u hu v hv => by rw [inner_sub_right,hu.2,hv.2,sub_self])
  have hj := hc.le_map_sum (t := S) (w := w) (p := p) (fun i _ => hw i) hsumS hS
  rw [sum_filter_positive_weights w hw p,
    sum_filter_positive_weights w hw (fun q => hessianValue x (t • p q) xi)] at hj
  simp only [smul_eq_mul] at hj
  have hj' := div_le_div_of_nonneg_right hj ht.le
  rw [Finset.sum_div] at hj'
  have hpos : ∃ i, 0 < w i := by
    by_contra hn
    have hz : ∀ i, w i = 0 := fun i => le_antisymm (le_of_not_gt (fun h => hn ⟨i,h⟩)) (hw i)
    simp only [hz,Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨j,hjpos⟩ := hpos
  have hlt : (∑ i, w i * (hessianValue x (s • p i) xi / s)) <
      ∑ i, w i * hessianValue x (t • p i) xi / t := by
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (divided_hessian_strict_decrease (hmin i) ht hts hs hxi).le (hw i)
    · refine ⟨j,Finset.mem_univ j,?_⟩
      rw [mul_div_assoc]
      exact mul_lt_mul_of_pos_left (divided_hessian_strict_decrease (hmin j) ht hts hs hxi) hjpos
  exact hlt.trans_le hj'

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ScaledSlack
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

lemma WeakMTW.finite_scaled_transverse_positive
    (hmtw : WeakMTW (n := n) (M := M))
    {ι : Type*} [Fintype ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmin : ∀ i, p i ∈ minimizingVectors x)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t < s) (hs : s < 1)
    (hID : ∀ q ∈ convexHull ℝ (range p), t • q ∈ injectivityDomain x)
    {xi : TangentSpace 𝓘(ℝ,Model n) x} (hxi : xi ≠ 0)
    (hle : ∀ i, t * inner ℝ (p i - ∑ j, w j • p j) xi ≤ 0) :
    0 < ∑ i, w i * (hessianValue x (t • ∑ j, w j • p j) xi -
      (t / s) * hessianValue x (s • p i) xi) := by
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · subst t
    simp only [zero_smul,hessianValue_zero,zero_div,zero_mul,sub_zero,←Finset.sum_mul,hsum,one_mul]
    exact sq_pos_of_pos (norm_pos_iff.mpr hxi)
  · let r := ∑ j, w j • p j
    have hneg : ∀ i, inner ℝ (p i-r) xi ≤ 0 := by
      intro i
      exact nonpos_of_mul_nonpos_right (hle i) ht0
    have hmean : ∑ i, w i * inner ℝ (p i-r) xi = 0 := by
      simp only [inner_sub_left,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
      have he : (∑ i, w i * inner ℝ (p i) xi) = inner ℝ r xi := by
        simp only [r,sum_inner,real_inner_smul_left]
      rw [he,sub_self]
    have horth : ∀ i, 0 < w i → inner ℝ xi (p i-r) = 0 := by
      intro i hi
      rw [real_inner_comm]
      exact finite_nonnegative_weight_zero_on_pos w (fun i => inner ℝ (p i-r) xi) hw hneg hmean i hi
    have H := hmtw.finite_nonnegative_transverse_slack_strict p w hw hsum hmin ht0 hts hs hID hxi horth
    have H' := (mul_lt_mul_of_pos_left H ht0)
    have he : t * (hessianValue x (t • r) xi / t) = hessianValue x (t • r) xi := by
      field_simp
    rw [he] at H'
    have heq : (∑ i, w i * (hessianValue x (t • r) xi -
        (t/s)*hessianValue x (s • p i) xi)) =
        hessianValue x (t • r) xi - t * ∑ i, w i * (hessianValue x (s • p i) xi / s) := by
      simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum,one_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    exact sub_pos.mpr H'

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

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma graphProjection_base_dist {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0 ≤ t) (z : subgradientGraph (n := n) (cTransform v)) :
    dist z.1.1 (graphProjection (cTransform v) t z) ≤ t * Metric.diam (univ : Set M) := by
  apply (dist_riemannianExp_le z.1.1 (t • z.1.2)).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left
    (active_hull_norm_le_diam (normalSubdifferential_subset_active_hull hv z.1.1 z.2)) ht

end WeakMTWTransport

end

end OAI
end


