-- Prove2me | Definitions.Def_OAIQ232A022
-- name    : OAIQ232A022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:08:15.279268+00:00
-- url     : https://prove2.me/theorems/48861d1d-4ee1-4086-b5c8-ffdad5b2aaee
-- title:
--   Definitions bundle OAIQ232A022 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_LocalCostSmooth`, `BiholderTransport_Coordinates_ExpNonconjugacy`, `BiholderTransport_Coordinates_JointExpInverse`, `BiholderTransport_Coordinates_RadialIdentity`, `BiholderTransport_Coordinates_TotalInjectivity`, `BiholderTransport_Coordinates_UniformShort`, `BiholderTransport_Geodesics_MinimizingSubinterval`, `BiholderTransport_Geodesics_NoCorner`, `BiholderTransport_Geodesics_SprayDistanceBound`, `BiholderTransport_Geodesics_SprayMinimizerUnique`, `BiholderTransport_Geodesics_SprayNonconjugacy`, `BiholderTransport_Regularity_ActionLocalData`, `BiholderTransport_Regularity_LimitGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundle `OAIQ232A021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A024` and `OAIQ232A025`.
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
import Definitions.Def_OAIQ232A021

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_LocalCostSmooth
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
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_cost_smooth (a : M) :
    ∃ δ : ℝ, 0<δ ∧ ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => dist z.1 z.2^2/2) (Metric.ball a δ ×ˢ Metric.ball a δ) := by
  obtain ⟨δ,_,τ,hδ,_,_,_,Φ,e,_,_,_,he,_,_,hei,hsrc,_,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  let c := extChartAt 𝓘(ℝ,E) a
  let g := riemannianCoordinateMetric (E := E) a
  let V : M×M → E := fun z => (e.symm (c z.1,c z.2)).2
  let f : M×M → ℝ := fun z => (τ^2/2)*g (c z.1) (V z) (V z)
  have heq : ∀ z ∈ Metric.ball a δ ×ˢ Metric.ball a δ, dist z.1 z.2^2/2 = f z := by
    rintro ⟨b,y⟩ ⟨hb,hy⟩
    have ht := htarget b hb y hy
    have hs := e.map_target ht
    have hi := e.right_inv ht
    have hfst : (e.symm (c b,c y)).1=c b := by
      have hh := congrArg Prod.fst hi
      rw [he] at hh
      exact hh
    have hpair : e.symm (c b,c y)=(c b,V (b,y)) := Prod.ext hfst rfl
    rw [hpair] at hs hi
    have hval : (Φ (τ,(c b,V (b,y)))).1=c y := by
      have hh := congrArg Prod.snd hi
      rw [he] at hh
      exact hh
    have hd := hdist b hb y hy (V (b,y)) hs hval
    have hnonneg : 0 ≤ g (c b) (V (b,y)) (V (b,y)) := by
      by_cases hv : V (b,y)=0
      · simp [hv]
      · exact (riemannianCoordinateMetric_positive (c.map_source (hsrc hb)) hv).le
    change dist b y^2/2 = (τ^2/2)*g (c b) (V (b,y)) (V (b,y))
    rw [hd,mul_pow,Real.sq_sqrt hnonneg]
    ring
  refine ⟨δ,hδ,?_⟩
  rintro z hz
  have hc₁ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun z : M×M => c z.1) z :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (by simpa only [extChartAt_source] using hsrc hz.1)).comp z contMDiffAt_fst
  have hc₂ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun z : M×M => c z.2) z :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (by simpa only [extChartAt_source] using hsrc hz.2)).comp z contMDiffAt_snd
  have heSnd : ContDiffAt ℝ ∞ (fun w : E×E => (e.symm w).2) (c z.1,c z.2) :=
    (hei.contDiffAt (e.open_target.mem_nhds (htarget z.1 hz.1 z.2 hz.2))).snd
  have heSndM : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞
      (fun w : E×E => (e.symm w).2) (c z.1,c z.2) := heSnd.contMDiffAt
  have hV : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ V z :=
    heSndM.comp (f := fun z : M×M => (c z.1,c z.2)) z (hc₁.prodMk_space hc₂)
  have hg : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun z : M×M => g (c z.1)) z :=
    ((contDiffOn_riemannianCoordinateMetric a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (c.map_source (hsrc hz.1)))).contMDiffAt.comp z hc₁
  have hf : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f z :=
    contMDiffAt_const.mul ((hg.clm_apply hV).clm_apply hV)
  exact ((hf.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hz) heq)).contMDiffWithinAt)

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

lemma dist_riemannianExp_smul_le (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) (s t : ℝ) :
    dist (riemannianExp x (s • v)) (riemannianExp x (t • v)) ≤ |s - t| * ‖v‖ := by
  simp only [riemannianExp_smul]
  exact dist_sprayFlow_le ⟨x,v⟩ s t

lemma dist_riemannianExp_le (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    dist x (riemannianExp x v) ≤ ‖v‖ := by
  have H := dist_sprayFlow_le (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M) 0 1
  simpa only [sprayFlow_zero,riemannianExp_eq_sprayFlow,zero_sub,abs_neg,abs_one,one_mul] using H

lemma minimizingVectors_smul {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • p ∈ minimizingVectors x := by
  change dist x (riemannianExp x (t • p)) = ‖t • p‖
  apply le_antisymm (dist_riemannianExp_le _ _)
  have H := dist_triangle x (riemannianExp x (t • p)) (riemannianExp x p)
  have Hb := dist_riemannianExp_smul_le x p t 1
  rw [one_smul,abs_of_nonpos (sub_nonpos.mpr ht1)] at Hb
  change dist x (riemannianExp x p) = ‖p‖ at hp
  rw [hp] at H
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
  nlinarith

lemma injectivityDomain_subset_minimizingVectors (x : M) :
    injectivityDomain (n := n) x ⊆ minimizingVectors x := by
  rintro p ⟨a,ha,he⟩
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hmin : a • p ∈ minimizingVectors x := by
    change dist x (riemannianExp x (a • p)) = ‖a • p‖
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
  have H := minimizingVectors_smul hmin (inv_nonneg.mpr ha0.le)
    (inv_le_one_of_one_le₀ ha.le)
  simpa only [smul_smul,inv_mul_cancel₀ ha0.ne',one_smul] using H

lemma isCompact_minimizingVectors (x : M) : IsCompact (minimizingVectors (n := n) x) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  apply (isCompact_closedBall (0 : TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
    (isClosed_minimizingVectors x)
  intro p hp
  rw [Metric.mem_closedBall,dist_zero_right,←hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ _)

lemma isCompact_total_minimizingVectors :
    IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ minimizingVectors z.1} := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  apply (isCompact_bundle_disk (F := Model n)
    (E := fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
  · exact isClosed_eq ((FiberBundle.continuous_proj _ _).dist contMDiff_riemannianExp.continuous)
      continuous_bundle_norm
  · intro z hz
    change ‖z.2‖ ≤ _
    rw [←hz]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_NoCorner
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

lemma exists_spray_local_extension (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, z.1 = a → ‖z.2‖ = 1 →
      ∀ ε : ℝ, 0 < ε → ε < δ → ∀ b : M,
      dist (sprayFlow (-ε) z).1 z.1 = ε → dist z.1 b = ε →
      dist (sprayFlow (-ε) z).1 b = 2*ε → (sprayFlow ε z).1 = b := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z hza hzn ε hε hεδ b hmin hzb hpb
  have hzball : z.1 ∈ Metric.ball a δ := by rw [hza]; exact Metric.mem_ball_self hδ
  have hpball : (sprayFlow (-ε) z).1 ∈ Metric.ball a δ := by
    rw [←hza,Metric.mem_ball,hmin]; exact hεδ
  have hbball : b ∈ Metric.ball a δ := by
    rw [←hza,Metric.mem_ball,dist_comm,hzb]; exact hεδ
  obtain ⟨q,hqy,hqn,_,hDq⟩ := H _ hpball _ hzball
  rcases q with ⟨y,u⟩
  change y=z.1 at hqy
  subst y
  obtain ⟨r,hry,hrn,hrback,hDr⟩ := H b hbball _ hzball
  rcases r with ⟨y,v⟩
  change y=z.1 at hry
  subst y
  have hflow : sprayFlow ε (sprayFlow (-ε) z) = z := by
    rw [←sprayFlow_add,add_neg_cancel,sprayFlow_zero]
  have hg := sprayFlow_minimizer_gradient (sprayFlow (-ε) z) hε
    (show dist (sprayFlow (-ε) z).1 (sprayFlow ε (sprayFlow (-ε) z)).1 =
      ε * ‖(sprayFlow (-ε) z).2‖ by rw [hflow,sprayFlow_speed,hzn,mul_one]; exact hmin)
  rw [hflow] at hg
  have hu : u = ε • z.2 := hg u hqn hDq
  have hop := cost_gradients_opposite
    (show dist (sprayFlow (-ε) z).1 b = dist (sprayFlow (-ε) z).1 z.1 + dist b z.1 by
      rw [hpb,hmin,dist_comm b z.1,hzb]; ring)
    (show dist (sprayFlow (-ε) z).1 z.1 = dist b z.1 by rw [hmin,dist_comm b z.1,hzb])
    u v hDq hDr
  have hv : v = (-ε) • z.2 := by
    rw [neg_smul,←hu]
    exact eq_neg_of_add_eq_zero_right hop
  have hr : (⟨z.1,v⟩ : TangentBundle 𝓘(ℝ,E) M) = tangentScale (-ε) z := by
    rw [hv]; cases z; rfl
  rw [hr,sprayFlow_scale,show (-ε)*(-1)=ε by ring] at hrback
  exact hrback

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MinimizingSubinterval
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

namespace WeakMTWTransport

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_local_minimizingVectors (x : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Metric.ball x δ,
      ∃ p ∈ minimizingVectors (n := n) x, riemannianExp x p = y := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := Model n) x
  refine ⟨δ,hδ,?_⟩
  intro y hy
  obtain ⟨q,hqx,hqn,hqb,_⟩ := H y hy x (Metric.mem_ball_self hδ)
  rcases q with ⟨a,u⟩
  change a=x at hqx
  subst a
  have he : riemannianExp x (-u) = y := by
    rw [show -u = (-1:ℝ) • u by simp,riemannianExp_smul]
    exact hqb
  refine ⟨-u,?_,he⟩
  change dist x (riemannianExp x (-u)) = ‖-u‖
  rw [he,norm_neg,hqn,dist_comm]

lemma exists_minimizing_vector (x y : M) :
    ∃ p ∈ minimizingVectors (n := n) x, riemannianExp x p = y := by
  classical
  by_cases hxy : x=y
  · subst y
    exact ⟨0,by simp [minimizingVectors],riemannianExp_zero x⟩
  have hD : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨γ,hγ,hγ0,hγD⟩ := riemannian_exists_metric_segment (I := 𝓘(ℝ,Model n)) x y
  have hd (s : Icc (0:ℝ) (dist x y)) : dist x (γ s) = s.1 := by
    have hh := hγ.dist_eq (⟨0,⟨le_rfl,dist_nonneg⟩⟩ : Icc (0:ℝ) (dist x y)) s
    simpa only [hγ0,Subtype.dist_eq,Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg s.2.1] using hh
  let R : Set M := riemannianExp (n := n) x '' minimizingVectors x
  have hR : IsCompact R := (isCompact_minimizingVectors x).image (continuous_riemannianExp x)
  let U : Set (Icc (0:ℝ) (dist x y)) := γ ⁻¹' R
  have hU : IsCompact U := (hR.isClosed.preimage hγ.continuous).isCompact
  obtain ⟨δ,hδ,Hlocal⟩ := exists_local_minimizingVectors (n := n) x
  let a : ℝ := min (dist x y/2) (δ/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haD : a ≤ dist x y := (min_le_left _ _).trans (by linarith)
  have haδ : a < δ := (min_le_right _ _).trans_lt (by linarith)
  let s₀ : Icc (0:ℝ) (dist x y) := ⟨a,ha.le,haD⟩
  have hs₀ : s₀ ∈ U := by
    obtain ⟨p,hp,he⟩ := Hlocal (γ s₀) (by rw [Metric.mem_ball,dist_comm,hd]; exact haδ)
    exact ⟨p,hp,he⟩
  obtain ⟨s,hs,hsmax⟩ := hU.exists_isMaxOn ⟨s₀,hs₀⟩ continuous_subtype_val.continuousOn
  have hs0 : 0 < s.1 := ha.trans_le (hsmax hs₀)
  have hsD : s.1 = dist x y := by
    by_contra hsne
    have hslt : s.1 < dist x y := lt_of_le_of_ne s.2.2 hsne
    obtain ⟨p,hp,hps⟩ := hs
    have hpn : ‖p‖ = s.1 := by
      change dist x (riemannianExp x p) = ‖p‖ at hp
      rw [hps,hd] at hp
      exact hp.symm
    let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,s.1⁻¹ • p⟩
    have hzn : ‖z.2‖ = 1 := by
      change ‖s.1⁻¹ • p‖ = 1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs0),hpn,inv_mul_cancel₀ hs0.ne']
    have hzflow : (sprayFlow s.1 z).1 = γ s := by
      rw [←riemannianExp_smul]
      rw [smul_smul,mul_inv_cancel₀ hs0.ne',one_smul,hps]
    have hzmin : dist z.1 (sprayFlow s.1 z).1 = s.1 * ‖z.2‖ := by
      rw [hzflow,hzn,mul_one]; exact hd s
    obtain ⟨η,hη,Hext⟩ := exists_spray_local_extension (E := Model n) (γ s)
    let ε : ℝ := min (η/2) (min (s.1/2) ((dist x y-s.1)/2))
    have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by linarith))
    have hεη : ε < η := (min_le_left _ _).trans_lt (by linarith)
    have hεs : ε < s.1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
    have hεD : s.1+ε < dist x y := by
      have h := (min_le_right (η/2) (min (s.1/2) ((dist x y-s.1)/2))).trans (min_le_right _ _)
      change ε ≤ (dist x y-s.1)/2 at h
      linarith
    let s' : Icc (0:ℝ) (dist x y) := ⟨s.1+ε,by linarith,hεD.le⟩
    let q := sprayFlow s.1 z
    have hqn : ‖q.2‖ = 1 := by rw [sprayFlow_speed]; exact hzn
    have hqback : sprayFlow (-ε) q = sprayFlow (s.1-ε) z := by
      rw [←sprayFlow_add]; congr 1; ring
    have hpre : dist (sprayFlow (-ε) q).1 q.1 = ε := by
      rw [hqback]
      have h := sprayFlow_minimizing_subinterval z (s := s.1-ε) (by linarith) (by linarith) hzmin
      rw [hzn,mul_one] at h
      simpa only [sub_sub_cancel] using h
    have hnext : dist q.1 (γ s') = ε := by
      change dist (sprayFlow s.1 z).1 _ = _
      rw [hzflow,hγ.dist_eq,Subtype.dist_eq,Real.dist_eq]
      change |s.1-(s.1+ε)| = ε
      rw [show s.1-(s.1+ε) = -ε by ring,abs_neg,abs_of_pos hε]
    have hlong : dist (sprayFlow (-ε) q).1 (γ s') = 2*ε := by
      apply le_antisymm
      · exact (dist_triangle _ q.1 _).trans (by rw [hpre,hnext]; linarith)
      · have h := dist_triangle x (sprayFlow (-ε) q).1 (γ s')
        rw [hd,hqback] at h
        have hpref := sprayFlow_minimizing_prefix z (s := s.1-ε) (by linarith) (by linarith) hzmin
        rw [hzn,mul_one] at hpref
        change dist x (sprayFlow (s.1-ε) z).1 = s.1-ε at hpref
        rw [hpref] at h
        change s.1+ε ≤ _ at h
        rw [hqback]
        linarith
    have hext := Hext q hzflow hqn ε hε hεη (γ s') hpre hnext hlong
    have hznext : (sprayFlow (s.1+ε) z).1 = γ s' := by
      rw [add_comm,sprayFlow_add]; exact hext
    have hs' : s' ∈ U := by
      refine ⟨(s.1+ε) • z.2,?_,?_⟩
      · change dist x (riemannianExp x ((s.1+ε) • z.2)) = ‖(s.1+ε) • z.2‖
        rw [riemannianExp_smul,hznext,hd,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < s.1+ε),hzn,mul_one]
      · rw [riemannianExp_smul]; exact hznext
    have hh := hsmax hs'
    change s.1+ε ≤ s.1 at hh
    linarith
  obtain ⟨p,hp,he⟩ := hs
  refine ⟨p,hp,he.trans ?_⟩
  have hsEq : s = ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ := Subtype.ext hsD
  rw [hsEq,hγD]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_UniformShort
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

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizing_near_zero_section (a : M) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ z : TangentBundle 𝓘(ℝ,E) M in 𝓝 ⟨a,0⟩,
      dist z.1 (sprayFlow τ z).1 = τ * ‖z.2‖ := by
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,hode,he,hesub,hed,hei,hsrc,hdiag,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  let A : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
  let c := extChartAt 𝓘(ℝ,E) a
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) A
  have hchart0 : χ A = (c a,0) := by
    rw [tangent_chart_apply]
    change (c a,tangentCoordChange 𝓘(ℝ,E) a a a 0) = (c a,0)
    rw [tangentCoordChange_self (mem_extChartAt_source a)]
  have hbase : ContinuousAt (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) A :=
    (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt
  have hflow₀ : Continuous (fun z : TangentBundle 𝓘(ℝ,E) M => sprayFlow τ z) :=
    contMDiff_sprayFlow.continuous.comp (continuous_const.prodMk continuous_id)
  have hflow : ContinuousAt (fun z : TangentBundle 𝓘(ℝ,E) M => (sprayFlow τ z).1) A :=
    (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt.comp
      hflow₀.continuousAt
  have hnear₁ : ∀ᶠ z in 𝓝 A, z.1 ∈ Metric.ball a δ :=
    hbase.preimage_mem_nhds (Metric.ball_mem_nhds a hδ)
  have hnear₂ : ∀ᶠ z in 𝓝 A, (sprayFlow τ z).1 ∈ Metric.ball a δ :=
    hflow.preimage_mem_nhds (by rw [sprayFlow_zero_velocity_base]; exact Metric.ball_mem_nhds a hδ)
  have hnear₃ : ∀ᶠ z in 𝓝 A, χ z ∈ e.source :=
    (continuousAt_extChartAt A).preimage_mem_nhds
      (e.open_source.mem_nhds (hchart0 ▸ hdiag a (Metric.mem_ball_self hδ)))
  refine ⟨τ,hτ,?_⟩
  filter_upwards [hnear₁,hnear₂,hnear₃] with z hz hy hez
  have hzsrc : z ∈ χ.source := (tangent_chart_source_iff A z).mpr (hsrc hz)
  have hball := hesub hez
  have h₀ : χ.symm (Φ (0,χ z)) = z := by rw [hΦ0 _ hball,χ.left_inv hzsrc]
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have hex := sprayFlow_eq_coordinate_curve A hr
    (fun t ht => (hode t ht (χ z) hball).1)
    (fun t ht => (hode t ht (χ z) hball).2) h₀ ht
  have hchart : χ (sprayFlow τ z) = Φ (τ,χ z) := by
    rw [hex,χ.right_inv ((tangent_chart_target_iff A _).mpr (hode τ ht (χ z) hball).1)]
  have hmet := hdist z.1 hz (sprayFlow τ z).1 hy (χ z).2
  have hcz : (c z.1,(χ z).2) = χ z := by
    exact Prod.ext (congrArg Prod.fst (tangent_chart_apply A z)).symm rfl
  rw [hcz] at hmet
  have hend : (Φ (τ,χ z)).1 = c (sprayFlow τ z).1 := by
    rw [←hchart]; exact congrArg Prod.fst (tangent_chart_apply A _)
  have hh := hmet hez hend
  have hen := coordinate_spray_energy A z (hsrc hz)
  have hfst : (χ z).1 = c z.1 := congrArg Prod.fst (tangent_chart_apply A z)
  rw [hfst] at hen
  rw [hen,Real.sqrt_sq (norm_nonneg _)] at hh
  exact hh

lemma sprayFlow_uniformly_short_minimizing (z₀ : TangentBundle 𝓘(ℝ,E) M) :
    ∀ᶠ p : ℝ × TangentBundle 𝓘(ℝ,E) M in 𝓝 (0,z₀),
      dist p.2.1 (sprayFlow p.1 p.2).1 = |p.1| * ‖p.2.2‖ := by
  obtain ⟨τ,hτ,H⟩ := sprayFlow_minimizing_near_zero_section (E := E) z₀.1
  let S : ℝ × TangentBundle 𝓘(ℝ,E) M → TangentBundle 𝓘(ℝ,E) M :=
    fun p => tangentScale (p.1/τ) p.2
  have hS : ContinuousAt S (0,z₀) :=
    contMDiff_tangentScale.continuous.continuousAt.comp
      ((continuousAt_fst.div_const τ).prodMk continuousAt_snd)
  have hS0 : S (0,z₀) = ⟨z₀.1,0⟩ := by simp [S,tangentScale]
  have hnear := (show Tendsto S (𝓝 (0,z₀)) (𝓝 ⟨z₀.1,0⟩) by
    simpa only [ContinuousAt,hS0] using hS).eventually H
  filter_upwards [hnear] with p hp
  change dist p.2.1 (sprayFlow τ (tangentScale (p.1/τ) p.2)).1 =
    τ * ‖(p.1/τ) • p.2.2‖ at hp
  rw [sprayFlow_scale,div_mul_cancel₀ _ hτ.ne'] at hp
  change dist p.2.1 (sprayFlow p.1 p.2).1 = τ * ‖(p.1/τ) • p.2.2‖ at hp
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos hτ] at hp
  rw [hp, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hτ)]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActionLocalData
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

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_two_short_legs (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {t T δ : ℝ} (ht : 0<t) (hT : t<T) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ε<t ∧ t+ε<T ∧
      (sprayFlow (t+ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈
        Metric.ball (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 δ ∧
      ∀ᶠ v : TangentSpace 𝓘(ℝ,E) x in 𝓝 p,
        (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈
          Metric.ball (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 δ ∧
        (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈
          Metric.ball (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 δ ∧
        HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
          (fun b => dist b (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1^2/2)
          (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1
          (innerSL ℝ ((-ε) • (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2)) ∧
        HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
          (fun q => dist (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 q^2/2)
          (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1
          (innerSL ℝ (ε • (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2)) := by
  let a := sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
  obtain ⟨δs,hδs,Hs⟩ := exists_local_spray_cost_start_gradient (E := E) a.1
  obtain ⟨δe,hδe,He⟩ := exists_local_spray_cost_gradient (E := E) a.1
  let r := min δ (min δs δe)
  have hr : 0 < r := lt_min hδ (lt_min hδs hδe)
  have hι : Continuous (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x =>
      (⟨x,u.2⟩ : TangentBundle 𝓘(ℝ,E) M)) :=
    (contMDiff_fiber_embedding x).continuous.comp continuous_snd
  let F : ℝ × TangentSpace 𝓘(ℝ,E) x → TangentBundle 𝓘(ℝ,E) M :=
    fun u => sprayFlow (t-u.1) ⟨x,u.2⟩
  have hF : Continuous F := contMDiff_sprayFlow.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk hι)
  have hF₀ : F (0,p)=a := by simp [F,a]
  have hpr : Continuous (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) :=
    FiberBundle.continuous_proj E (fun b : M => TangentSpace 𝓘(ℝ,E) b)
  have hFin := (hpr.comp hF).continuousAt.preimage_mem_nhds
    (show Metric.ball a.1 r ∈ 𝓝 (F (0,p)).1 by rw [hF₀]; exact Metric.ball_mem_nhds _ hr)
  have hQ : Continuous (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x =>
      (sprayFlow t (⟨x,u.2⟩ : TangentBundle 𝓘(ℝ,E) M)).1) :=
    hpr.comp ((contMDiff_spray_fiber x t).continuous.comp continuous_snd)
  have hQin := (hQ.continuousAt (x := (0,p))).preimage_mem_nhds (Metric.ball_mem_nhds a.1 hr)
  have hY : Continuous (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x =>
      (sprayFlow (t+u.1) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1) :=
    hpr.comp (contMDiff_sprayFlow.continuous.comp
      ((continuous_const.add continuous_fst).prodMk continuous_const))
  have hYin := (hY.continuousAt (x := (0,p))).preimage_mem_nhds
    (show Metric.ball a.1 r ∈ 𝓝 (sprayFlow (t+(0:ℝ)) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 by
      simpa only [add_zero] using Metric.ball_mem_nhds a.1 hr)
  have htend : Tendsto (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x => (u.1,F u)) (𝓝 (0,p)) (𝓝 (0,a)) := by
    simpa only [ContinuousAt,hF₀] using (continuous_fst.prodMk hF).continuousAt (x := (0,p))
  have hmin := htend.eventually (sprayFlow_uniformly_short_minimizing a)
  have hAll : ∀ᶠ u : ℝ × TangentSpace 𝓘(ℝ,E) x in 𝓝 (0,p),
      (F u).1 ∈ Metric.ball a.1 r ∧
      (sprayFlow t (⟨x,u.2⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈ Metric.ball a.1 r ∧
      (sprayFlow (t+u.1) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈ Metric.ball a.1 r ∧
      dist (F u).1 (sprayFlow u.1 (F u)).1 = |u.1| *‖(F u).2‖ := by
    filter_upwards [hFin,hQin,hYin,hmin] with u h₁ h₂ h₃ h₄
    exact ⟨h₁,h₂,h₃,h₄⟩
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hAll
  obtain ⟨η,hη,hηA⟩ := Metric.mem_nhds_iff.mp hA
  let ε := min η (min t (T-t))/2
  have hε : 0<ε := div_pos (lt_min hη (lt_min ht (sub_pos.mpr hT))) (by norm_num)
  have hεη : ε<η := lt_of_lt_of_le (half_lt_self (lt_min hη (lt_min ht (sub_pos.mpr hT)))) (min_le_left _ _)
  have hεt : ε<t := lt_of_lt_of_le (half_lt_self (lt_min hη (lt_min ht (sub_pos.mpr hT))))
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεT : ε<T-t := lt_of_lt_of_le (half_lt_self (lt_min hη (lt_min ht (sub_pos.mpr hT))))
    ((min_le_right _ _).trans (min_le_right _ _))
  have hεA : ε∈A := hηA (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε] using hεη)
  have hP := hAB (show (ε,p) ∈ A ×ˢ B from ⟨hεA,mem_of_mem_nhds hB⟩)
  have hsubδ : Metric.ball a.1 r ⊆ Metric.ball a.1 δ := Metric.ball_subset_ball (min_le_left _ _)
  have hsubs : Metric.ball a.1 r ⊆ Metric.ball a.1 δs :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsube : Metric.ball a.1 r ⊆ Metric.ball a.1 δe :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε,hε,hεt,by linarith,hsubδ hP.2.2.1,?_⟩
  filter_upwards [hB] with v hv
  have H := hAB (show (ε,v) ∈ A ×ˢ B from ⟨hεA,hv⟩)
  have hflow : sprayFlow ε (F (ε,v)) = sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M) := by
    dsimp [F]
    have htime : ε + (t - ε) = t := by ring
    rw [← sprayFlow_add, htime]
  have hm : dist (F (ε,v)).1 (sprayFlow ε (F (ε,v))).1 = ε*‖(F (ε,v)).2‖ := by
    simpa only [abs_of_pos hε] using H.2.2.2
  have hs := Hs (F (ε,v)) ε hε (hsubs H.1) (by rw [hflow]; exact hsubs H.2.1) hm
  have he := He (F (ε,v)) ε hε (hsube H.1) (by rw [hflow]; exact hsube H.2.1) hm
  rw [hflow] at hs he
  exact ⟨hsubδ H.1,hsubδ H.2.1,hs,he⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayNonconjugacy
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

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_interior_nonconjugate (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {t T : ℝ} (ht : 0<t) (hT : t<T)
    (hmin : dist x (sprayFlow T (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = T*‖p‖) :
    Function.Injective (fderiv ℝ
      (fun v : TangentSpace 𝓘(ℝ,E) x => extChartAt 𝓘(ℝ,E)
        (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1
        (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1) p) := by
  let a := sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
  let c := extChartAt 𝓘(ℝ,E) a.1
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let Q : TangentSpace 𝓘(ℝ,E) x → E := fun v => c (sprayFlow t ⟨x,v⟩).1
  let V : TangentSpace 𝓘(ℝ,E) x → E := fun v => (χ (sprayFlow t ⟨x,v⟩)).2
  let g := riemannianCoordinateMetric (E := E) a.1
  have hsrc : a.1 ∈ c.source := mem_extChartAt_source a.1
  have hQp : Q p = c a.1 := rfl
  have htarget : Q p ∈ c.target := by
    rw [hQp]
    exact c.map_source hsrc
  have hInv : c.symm (Q p)=a.1 := c.left_inv hsrc
  have hΦ : ContDiffAt ℝ ∞ (fun v : TangentSpace 𝓘(ℝ,E) x => χ (sprayFlow t ⟨x,v⟩)) p :=
    ((show ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ a from
      contMDiffAt_extChartAt).comp p (contMDiff_spray_fiber x t p)).contDiffAt
  have hΦeq : (fun v : TangentSpace 𝓘(ℝ,E) x => χ (sprayFlow t ⟨x,v⟩)) = fun v => (Q v,V v) := by
    funext v
    apply Prod.ext
    · exact congrArg Prod.fst (tangent_chart_apply a (sprayFlow t ⟨x,v⟩))
    · rfl
  rw [hΦeq] at hΦ
  have hQ := hΦ.fst
  have hV := hΦ.snd
  obtain ⟨δ,hδ,hC⟩ := exists_local_cost_smooth (E := E) a.1
  obtain ⟨ε,hε,hεt,hεT,hy,hlocal⟩ := exists_two_short_legs x p ht hT hδ
  let L := t-ε
  let y := (sprayFlow (t+ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1
  let b : TangentSpace 𝓘(ℝ,E) x → M := fun v => (sprayFlow L ⟨x,v⟩).1
  let K : E → ℝ := fun q => (dist (c.symm q) y^2/2)/ε
  let B : TangentSpace 𝓘(ℝ,E) x × E → ℝ := fun z =>
    L*‖z.1‖^2/2 + (dist (b z.1) (c.symm z.2)^2/2)/ε + K z.2
  have hL : 0<L := sub_pos.mpr hεt
  have hlp := hlocal.self_of_nhds
  have hb : ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) 𝓘(ℝ,E) ∞ b :=
    (Bundle.contMDiff_proj (fun z : M => TangentSpace 𝓘(ℝ,E) z)).comp (contMDiff_spray_fiber x L)
  have hqδ : c.symm (Q p) ∈ Metric.ball a.1 δ := by rw [hInv]; exact Metric.mem_ball_self hδ
  have hIC := coordinate_cost_contDiffAt hC (hb p) hlp.1 htarget hqδ
  have hK : ContDiffAt ℝ ∞ K (Q p) :=
    (coordinate_outgoing_cost_contDiffAt hC hy htarget hqδ).div_const ε
  have hB : ContDiffAt ℝ 2 B (p,Q p) := by
    have hn : ContDiffAt ℝ ∞ (fun z : TangentSpace 𝓘(ℝ,E) x × E => L*‖z.1‖^2/2) (p,Q p) :=
      (contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (p,Q p) contDiffAt_fst)).div_const 2
    exact ((hn.add (hIC.div_const ε)).add (hK.comp (p,Q p) contDiffAt_snd)).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hm : dist x (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = (L+2*ε)*‖p‖ :=
    sprayFlow_minimizing_prefix (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
      (by positivity) (by dsimp [L] <;> linarith) hmin
  have hBcontact : B (p,Q p)=(L+2*ε)*‖p‖^2/2 := by
    dsimp [B,K]
    rw [hInv]
    have heq₁ : L+ε=t := by dsimp [L] <;> ring
    have heq₂ : L+2*ε=t+ε := by dsimp [L] <;> ring
    convert! spray_split_action_contact x p hL hε hm using 1;
      simp only [heq₁,heq₂,div_div,b,y,a]
  have hBmin : IsLocalMin B (p,Q p) := by
    apply Filter.Eventually.of_forall
    intro z
    rw [hBcontact]
    have heq : L+2*ε=t+ε := by dsimp [L] <;> ring
    convert! spray_split_action_minimum x p hL hε hm z.1 (c.symm z.2) using 1;
      simp only [B,K,b,y,heq,div_div]
  have hnear : ∀ᶠ v : TangentSpace 𝓘(ℝ,E) x in 𝓝 p,
      (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈ c.source :=
    ((Bundle.contMDiff_proj (fun z : M => TangentSpace 𝓘(ℝ,E) z)).comp
      (contMDiff_spray_fiber x t) p).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source a.1).mem_nhds hsrc)
  have hBnear : ∀ᶠ v in 𝓝 p, DifferentiableAt ℝ B (v,Q v) :=
    (continuousAt_id.prodMk hQ.continuousAt).tendsto.eventually
      ((hB.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num)))
  have hKnear : ∀ᶠ v in 𝓝 p, DifferentiableAt ℝ K (Q v) :=
    hQ.continuousAt.tendsto.eventually
      (((hK.of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
        (fun _ h => h.differentiableAt (by norm_num)))
  have hstat : ∀ᶠ v in 𝓝 p, ∀ w : TangentSpace 𝓘(ℝ,E) x, fderiv ℝ B (v,Q v) (w,0)=0 := by
    filter_upwards [hlocal,hnear,hBnear] with v hv hvs hBd
    intro w
    apply fderiv_fst_eq_of_line_stationary hBd
    have hd := (spray_action_line_stationary x v w L ε hε.ne'
      (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 hv.2.2.1).add_const (K (Q v))
    simpa only [B,b,Q,c.left_inv hvs,zero_add] using hd
  have hcot : ∀ᶠ v in 𝓝 p, ∀ u : E,
      fderiv ℝ B (v,Q v) (0,u) = g (Q v) (V v) u + fderiv ℝ K (Q v) u := by
    filter_upwards [hlocal,hnear,hBnear,hKnear] with v hv hvs hBd hKd
    intro u
    have hd := (coordinate_gradient_of_hasMFDerivAt
      (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)) hvs
      (fun q => dist (b v) q^2/2) ε hv.2.2.2).mul_const ε⁻¹
    have hI : HasFDerivAt (fun q : E => (dist (b v) (c.symm q)^2/2)/ε)
        (g (Q v) (V v)) (Q v) := by
      convert! hd using 1
      all_goals try with_reducible_and_instances rfl
      simp only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
      rfl
    have H := ((hasFDerivAt_const (L*‖v‖^2/2) (Q v)).add hI).add hKd.hasFDerivAt
    have H' : HasFDerivAt (fun q : E => B (v,q)) (g (Q v) (V v)+fderiv ℝ K (Q v)) (Q v) := by
      convert! H using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp only [_root_.add_apply, zero_add]
    exact fderiv_snd_eq_of_partial hBd H' u
  have hg : DifferentiableAt ℝ g (Q p) :=
    ((contDiffOn_riemannianCoordinateMetric a.1).contDiffAt
      ((isOpen_extChartAt_target a.1).mem_nhds htarget)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hR : DifferentiableAt ℝ (fderiv ℝ K) (Q p) :=
    (hK.fderiv_right (m := 1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiableAt (by norm_num)
  have hpos : ∀ u : E, u≠0 → 0<g (Q p) u u :=
    fun _ hu => riemannianCoordinateMetric_positive htarget hu
  have himm : Function.Injective (fderiv ℝ (fun v => (Q v,V v)) p) := by
    rw [←hΦeq]
    exact coordinate_spray_fiber_immersion x p t
  exact generating_graph_position_immersion hB hBmin
    (hQ.differentiableAt (by simp)) (hV.differentiableAt (by simp)) hg hR hpos hstat hcot himm

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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma riemannianExp_interior_nonconjugate {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p) := by
  obtain ⟨a,ha,hpa⟩ := hp
  have hm : dist x (sprayFlow a (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 = a*‖p‖ := by
    rw [←riemannianExp_smul]
    exact hpa
  simpa only [riemannianExp_eq_sprayFlow] using
    sprayFlow_interior_nonconjugate x p zero_lt_one ha hm

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_JointExpInverse
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_joint_exp_inverse (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
    let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
    ∃ e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n),
      (e : Model n × Model n → Model n × Model n) =
        (fun q => (q.1, d (riemannianExp (χ.symm q).1 (χ.symm q).2))) ∧
      χ z ∈ e.source ∧ e.source ⊆ χ.target ∧
      (∀ q ∈ e.source, riemannianExp (χ.symm q).1 (χ.symm q).2 ∈ d.source) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let f : Model n × Model n → Model n := fun q =>
    d (riemannianExp (χ.symm q).1 (χ.symm q).2)
  let S := χ.target ∩ (fun q => riemannianExp (χ.symm q).1 (χ.symm q).2) ⁻¹' d.source
  have hχz : χ z ∈ χ.target := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hχ : ContMDiffOn 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm χ.target :=
    contMDiffOn_extChartAt_symm z
  have hE : ContMDiffOn 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞
      (fun q => riemannianExp (χ.symm q).1 (χ.symm q).2) χ.target :=
    contMDiff_riemannianExp.comp_contMDiffOn hχ
  have hS : IsOpen S :=
    hE.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_target z) (isOpen_extChartAt_source _)
  have hzS : χ z ∈ S := ⟨hχz,by change riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2 ∈ d.source; rw [hχinv]; exact mem_extChartAt_source _⟩
  have hd : ContMDiffOn 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d d.source := by
    simpa only [d,extChartAt_source] using (contMDiffOn_extChartAt (I := 𝓘(ℝ,Model n)) (n := ∞) (x := riemannianExp z.1 z.2))
  have hf : ContDiffOn ℝ ∞ f S :=
    (hd.comp (hE.mono (inter_subset_left)) (fun _ hq => hq.2)).contDiffOn
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) z.1
  let L : TangentSpace 𝓘(ℝ,Model n) z.1 ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ z.1 (mem_baseSet_trivializationAt (Model n) _ z.1)
  have hχsecond : (χ z).2=L z.2 := rfl
  have hχfiber (w : Model n) : χ.symm ((χ z).1,w) =
      (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    have hforward : χ (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) = ((χ z).1,w) := by
      apply Prod.ext
      · rfl
      · change L (L.symm w)=w
        exact L.apply_symm_apply w
    rw [←hforward]
    apply χ.left_inv
    exact (tangent_chart_source_iff z _).mpr (mem_extChartAt_source z.1)
  let F : TangentSpace 𝓘(ℝ,Model n) z.1 → Model n :=
    fun v => d (riemannianExp z.1 v)
  have hF : ContDiffAt ℝ ∞ F z.2 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) from
      contMDiffAt_extChartAt).comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hFi : Function.Injective (fderiv ℝ F z.2) := riemannianExp_interior_nonconjugate hz
  have hpart : (fun w => f ((χ z).1,w)) = F ∘ L.symm := by
    funext w
    dsimp [f]
    rw [hχfiber]
  have hpartder : fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2 =
      (fderiv ℝ F z.2).comp (L.symm : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1) := by
    rw [hpart,hχsecond]
    have hF' : HasFDerivAt F (fderiv ℝ F z.2) (L.symm (L z.2)) := by
      simpa only [L.symm_apply_apply] using (hF.differentiableAt (by simp)).hasFDerivAt
    exact (hF'.comp (L z.2) L.symm.hasFDerivAt).fderiv
  have hpi : (fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2).IsInvertible := by
    have hi : Function.Injective (fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2) := by
      rw [hpartder]
      exact hFi.comp L.symm.injective
    have hs := LinearMap.injective_iff_surjective.mp hi
    exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hi)
      (LinearMap.range_eq_top.mpr hs),rfl⟩
  have hi := first_coordinate_preserving_derivative_invertible
    ((hf.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hpi
  obtain ⟨e,he,hz',heS,heD,heInv⟩ := exists_smooth_local_diffeomorphism hS
    (contDiffOn_fst.prodMk hf) hzS hi
  exact ⟨e,he,hz',fun _ hq => (heS hq).1,fun _ hq => (heS hq).2,heD,heInv⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayMinimizerUnique
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_spray_minimizer_unique (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z w : TangentBundle 𝓘(ℝ,E) M,
      z.1 ∈ Metric.ball a δ → (sprayFlow 1 z).1 ∈ Metric.ball a δ →
      z.1=w.1 → (sprayFlow 1 z).1=(sprayFlow 1 w).1 →
      dist z.1 (sprayFlow 1 z).1 = ‖z.2‖ →
      dist w.1 (sprayFlow 1 w).1 = ‖w.2‖ → z=w := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z w hz hf hbase hend hminz hminw
  obtain ⟨G,hG,hGn,_,hD⟩ := H _ hz _ hf
  apply sprayFlow_minimizer_unique_of_gradient z w G hbase hG (hG.trans hend) hminz hminw
  · exact hGn.trans (congrArg (dist z.1) hG.symm)
  · exact hD

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_TotalInjectivity
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma joint_exp_locally_injective (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    ∃ U : Set (TangentBundle 𝓘(ℝ,Model n) M), IsOpen U ∧ z ∈ U ∧
      InjOn (fun q : TangentBundle 𝓘(ℝ,Model n) M => (q.1,riemannianExp q.1 q.2)) U := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  obtain ⟨e,he,hze,_,_,_,_⟩ := exists_joint_exp_inverse z hz
  let U := χ.source ∩ χ ⁻¹' e.source
  have hU : IsOpen U := (continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z) e.open_source
  refine ⟨U,hU,⟨mem_extChartAt_source z,hze⟩,?_⟩
  intro q hq r hr hqr
  apply χ.injOn hq.1 hr.1
  apply e.injOn hq.2 hr.2
  rw [he]
  change ((χ q).1,d (riemannianExp (χ.symm (χ q)).1 (χ.symm (χ q)).2)) =
    ((χ r).1,d (riemannianExp (χ.symm (χ r)).1 (χ.symm (χ r)).2))
  rw [χ.left_inv hq.1,χ.left_inv hr.1]
  apply Prod.ext
  · simp only [χ,tangent_chart_apply]
    exact congrArg (extChartAt 𝓘(ℝ,Model n) z.1) (congrArg Prod.fst hqr)
  · exact congrArg d (congrArg Prod.snd hqr)

end
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_RadialIdentity
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma shifted_exp_endpoint (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) (t : ℝ) :
    riemannianExp (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      ((1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) = riemannianExp x p := by
  rw [riemannianExp_eq_sprayFlow]
  change (sprayFlow 1 (tangentScale (1-t) (sprayFlow t ⟨x,p⟩))).1 = _
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel]
  exact (riemannianExp_eq_sprayFlow x p).symm

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

lemma continuous_graphProjection_family (u : M → ℝ) :
    Continuous (fun q : ℝ × subgradientGraph (n := n) u => graphProjection u q.1 q.2) :=
  contMDiff_riemannianExp.continuous.comp
    (contMDiff_tangentScale.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

end

open Set Filter
open scoped Topology

end WeakMTWTransport

end

end OAI
end


