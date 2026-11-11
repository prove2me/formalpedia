-- Prove2me | Definitions.Def_OAIQ232A024
-- name    : OAIQ232A024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:18:22.458032+00:00
-- url     : https://prove2.me/theorems/b9c3cf7d-c076-4ea0-8295-ceff1c27f4fc
-- title:
--   Definitions bundle OAIQ232A024 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 34 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Coordinates_ExpNonconjugacy`, `BiholderTransport_Coordinates_RadialIdentity`, `BiholderTransport_Coordinates_SplitAction`, `BiholderTransport_Coordinates_TotalInjectivity`, `BiholderTransport_CostGeometry_BranchCost`, `BiholderTransport_CostGeometry_CostGradient`, `BiholderTransport_CostGeometry_CostSmooth`, `BiholderTransport_CostGeometry_FirstCutLower`, `BiholderTransport_CostGeometry_SplitStationary`, `BiholderTransport_CostGeometry_SplitTrial`, `BiholderTransport_Geodesics_ExpInteriorUnique`, `BiholderTransport_Geodesics_InjectivityOpen`, `BiholderTransport_Geodesics_SplitMinimizingAction`, `BiholderTransport_Geodesics_SprayMinimizerUnique`, `BiholderTransport_LinearAlgebra_BranchHessian`, `BiholderTransport_LinearAlgebra_HessianSmooth`, `BiholderTransport_Volume_DiagonalKernel`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A022` and `OAIQ232A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A026` and `OAIQ232A027`; the proofs of `OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix`, `OAI.WeakMTWTransport.continuous_expJacobian`, `OAI.WeakMTWTransport.eventual_lower_bound_of_center_gain`, `OAI.WeakMTWTransport.exists_true_center_limit`, `OAI.WeakMTWTransport.fixedJoinMiddle_uniform_interval_crossing`, `OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing` and `OAI.WeakMTWTransport.moving_center_sequential_semibound`.
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpNonconjugacy
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_coordinate_exp_inverse {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    ∃ e : OpenPartialHomeomorph (TangentSpace 𝓘(ℝ,Model n) x) (Model n),
      (e : TangentSpace 𝓘(ℝ,Model n) x → Model n) =
        (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)) ∧
      p ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (e p) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  let f := fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) (riemannianExp (n := n) x v)
  have hf : ContDiffAt ℝ ∞ f p :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞
      (extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)) (riemannianExp (n := n) x p) from
      contMDiffAt_extChartAt).comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  let D := fderiv ℝ f p
  have hi : Function.Injective D := riemannianExp_interior_nonconjugate hp
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) x
  let L : TangentSpace 𝓘(ℝ,Model n) x ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt (Model n) _ x)
  have hs : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank L.toLinearEquiv.finrank_eq).mp hi
  let A := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs)
  have hd : HasFDerivAt f (A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n) p :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  have he : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,rfl,he,?_⟩
  apply e.contDiffAt_symm (e.map_source he)
  · rw [e.left_inv he]
    convert! hd using 1
  · rw [e.left_inv he]
    exact hf

lemma riemannianExp_locally_injective {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    ∃ U, IsOpen U ∧ p ∈ U ∧ Set.InjOn (riemannianExp (n := n) x) U := by
  obtain ⟨e,he,hp',_⟩ := exists_coordinate_exp_inverse hp
  refine ⟨e.source,e.open_source,hp',?_⟩
  intro v hv w hw h
  apply e.injOn hv hw
  rw [he]
  exact congrArg (extChartAt 𝓘(ℝ,Model n) (riemannianExp (n := n) x p)) h

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_unit_minimizer_unique (z w : TangentBundle 𝓘(ℝ,E) M)
    (hbase : z.1=w.1) (hzn : ‖z.2‖=1) (hwn : ‖w.2‖=1)
    {t T : ℝ} (ht : 0<t) (htT : t<T)
    (hminz : dist z.1 (sprayFlow T z).1 = T)
    (hminw : dist w.1 (sprayFlow t w).1 = t)
    (hend : (sprayFlow t z).1=(sprayFlow t w).1) : z=w := by
  have hzmin : dist z.1 (sprayFlow T z).1 = T*‖z.2‖ := by rw [hzn,mul_one]; exact hminz
  have hwmin : dist w.1 (sprayFlow t w).1 = t*‖w.2‖ := by rw [hwn,mul_one]; exact hminw
  let a := (sprayFlow t z).1
  obtain ⟨δ,hδ,Hext⟩ := exists_spray_local_extension (E := E) a
  obtain ⟨η,hη,Huniq⟩ := exists_local_spray_minimizer_unique (E := E) a
  let ε : ℝ := min (δ/2) (min (η/2) (min (t/2) ((T-t)/2)))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by linarith)))
  have hεδ : ε<δ := (min_le_left _ _).trans_lt (by linarith)
  have hεη : ε<η := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεt : ε<t := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεT : t+ε<T := by
    have hh := (((min_le_right (δ/2) (min (η/2) (min (t/2) ((T-t)/2)))).trans (min_le_right _ _)).trans (min_le_right _ _))
    change ε ≤ (T-t)/2 at hh
    linarith
  let q := sprayFlow t z
  let r := sprayFlow t w
  let b := (sprayFlow (t+ε) z).1
  have hrbase : r.1=a := hend.symm
  have hrn : ‖r.2‖=1 := by rw [sprayFlow_speed]; exact hwn
  have hqnext : dist q.1 b = ε := by
    have hpref := sprayFlow_minimizing_prefix z (show 0≤t+ε by linarith) hεT.le hzmin
    have hh := sprayFlow_minimizing_subinterval z ht.le (show t≤t+ε by linarith) hpref
    rw [hzn,mul_one] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hrback : sprayFlow (-ε) r = sprayFlow (t-ε) w := by
    rw [←sprayFlow_add]; congr 1; ring
  have hback : dist (sprayFlow (-ε) r).1 r.1 = ε := by
    rw [hrback]
    have hh := sprayFlow_minimizing_subinterval w (s := t-ε) (by linarith) (by linarith) hwmin
    rw [hwn,mul_one] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hrnext : dist r.1 b = ε := by rw [hrbase]; exact hqnext
  have hlong : dist (sprayFlow (-ε) r).1 b = 2*ε := by
    apply le_antisymm
    · exact (dist_triangle _ r.1 _).trans (by rw [hback,hrnext]; linarith)
    · have hh := dist_triangle w.1 (sprayFlow (-ε) r).1 b
      have hpre := sprayFlow_minimizing_prefix w (s := t-ε) (by linarith) (by linarith) hwmin
      rw [hwn,mul_one] at hpre
      have hpost := sprayFlow_minimizing_prefix z (s := t+ε) (by linarith) hεT.le hzmin
      rw [hzn,mul_one] at hpost
      rw [hrback,hpre,←hbase] at hh
      change dist z.1 (sprayFlow (t+ε) z).1 ≤ _ at hh
      rw [hpost] at hh
      rw [hrback]
      linarith
  have hrext := Hext r hrbase hrn ε hε hεδ b hback hrnext hlong
  have hqext : (sprayFlow ε q).1 = b := by
    rw [←sprayFlow_add,add_comm]
  have hscale (u : TangentBundle 𝓘(ℝ,E) M) :
      (sprayFlow 1 (tangentScale ε u)).1 = (sprayFlow ε u).1 := by
    rw [sprayFlow_scale,mul_one]; rfl
  have hscalen (u : TangentBundle 𝓘(ℝ,E) M) : ‖(tangentScale ε u).2‖ = ε*‖u.2‖ := by
    change ‖ε • u.2‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  have hscaled := Huniq (tangentScale ε q) (tangentScale ε r)
    (Metric.mem_ball_self hη)
    (by rw [hscale,hqext,Metric.mem_ball,dist_comm]; exact hqnext.trans_lt hεη)
    hend (by rw [hscale,hscale,hqext,hrext])
    (by rw [hscale,hqext,hscalen,sprayFlow_speed,hzn,mul_one]; exact hqnext)
    (by rw [hscale,hrext,hscalen,hrn,mul_one]; exact hrnext)
  have hqr := tangentScale_injective hε.ne' hscaled
  have hh := congrArg (sprayFlow (-t)) hqr
  simpa only [q,r,←sprayFlow_add,neg_add_cancel,sprayFlow_zero] using hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ExpInteriorUnique
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

lemma riemannianExp_interior_unique {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (hq : q ∈ minimizingVectors x)
    (he : riemannianExp x p = riemannianExp x q) : p=q := by
  have hpmin := injectivityDomain_subset_minimizingVectors x hp
  have hn : ‖p‖=‖q‖ := hpmin.symm.trans ((congrArg (dist x) he).trans hq)
  by_cases hp0 : p=0
  · have hq0 : q=0 := norm_eq_zero.mp (by rw [←hn,hp0,norm_zero])
    exact hp0.trans hq0.symm
  have ht : 0<‖p‖ := norm_pos_iff.mpr hp0
  obtain ⟨a,ha,hpa⟩ := hp
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,‖p‖⁻¹ • p⟩
  let w : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,‖p‖⁻¹ • q⟩
  have hzn : ‖z.2‖=1 := by
    change ‖‖p‖⁻¹ • p‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),inv_mul_cancel₀ ht.ne']
  have hwn : ‖w.2‖=1 := by
    change ‖‖p‖⁻¹ • q‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),←hn,inv_mul_cancel₀ ht.ne']
  have hflowz : (sprayFlow ‖p‖ z).1=riemannianExp x p := by
    rw [←riemannianExp_smul,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hfloww : (sprayFlow ‖p‖ w).1=riemannianExp x q := by
    rw [←riemannianExp_smul,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hflowa : (sprayFlow (a*‖p‖) z).1=riemannianExp x (a • p) := by
    rw [←riemannianExp_smul,smul_smul,mul_assoc,mul_inv_cancel₀ ht.ne',mul_one]
  have hzw := sprayFlow_unit_minimizer_unique z w rfl hzn hwn ht
    (lt_mul_of_one_lt_left ht ha)
    (by rw [hflowa]; exact hpa)
    (by rw [hfloww,hn]; exact hq)
    (by rw [hflowz,hfloww]; exact he)
  have hvel : ‖p‖⁻¹ • p = ‖p‖⁻¹ • q := TotalSpace.mk_injective x hzw
  exact (smul_right_inj (inv_ne_zero ht.ne')).mp hvel

lemma riemannianExp_injOn_injectivityDomain (x : M) :
    Set.InjOn (riemannianExp (n := n) x) (injectivityDomain x) := by
  intro p hp q hq he
  exact riemannianExp_interior_unique hp (injectivityDomain_subset_minimizingVectors x hq) he

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_InjectivityOpen
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma injectivityDomain_subset_interior_minimizingVectors (x : M) :
    injectivityDomain (n := n) x ⊆ interior (minimizingVectors x) := by
  intro p hp
  obtain ⟨U,hU,hpU,hinj⟩ := riemannianExp_locally_injective hp
  let K := minimizingVectors (n := n) x \ U
  have hK : IsCompact K := (isCompact_minimizingVectors x).diff hU
  have hclosed : IsClosed (riemannianExp (n := n) x '' K) :=
    (hK.image (continuous_riemannianExp x)).isClosed
  have hnot : riemannianExp x p ∉ riemannianExp x '' K := by
    rintro ⟨q,hq,he⟩
    have heq := riemannianExp_interior_unique hp hq.1 he.symm
    exact hq.2 (heq ▸ hpU)
  have hnear : ∀ᶠ v in 𝓝 p, v ∈ U ∧ riemannianExp x v ∉ riemannianExp x '' K :=
    Filter.Eventually.and (hU.mem_nhds hpU)
      ((continuous_riemannianExp x).continuousAt.preimage_mem_nhds
        (hclosed.isOpen_compl.mem_nhds hnot))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hnear] with v hv
  obtain ⟨q,hq,he⟩ := exists_minimizing_vector (n := n) x (riemannianExp x v)
  have hqU : q ∈ U := by
    by_contra hqU
    exact hv.2 ⟨q,⟨hq,hqU⟩,he⟩
  have hvq := hinj hv.1 hqU he.symm
  exact hvq ▸ hq

lemma injectivityDomain_eq_interior_minimizingVectors (x : M) :
    injectivityDomain (n := n) x = interior (minimizingVectors x) :=
  Set.Subset.antisymm (injectivityDomain_subset_interior_minimizingVectors x)
    (interior_minimizingVectors_subset x)

lemma isOpen_injectivityDomain (x : M) : IsOpen (injectivityDomain (n := n) x) := by
  rw [injectivityDomain_eq_interior_minimizingVectors]
  exact isOpen_interior

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

lemma interior_total_minimizingVectors (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    z ∈ interior {q : TangentBundle 𝓘(ℝ,Model n) M | q.2 ∈ minimizingVectors q.1} := by
  apply interior_of_compact_unique_fiber isCompact_total_minimizingVectors
    ((FiberBundle.continuous_proj _ _).prodMk contMDiff_riemannianExp.continuous)
  · intro y
    obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) y.1 y.2
    exact ⟨⟨y.1,p⟩,hp,Prod.ext rfl he⟩
  · rintro ⟨b,v⟩ hv hqz
    rcases z with ⟨a,u⟩
    have hba : b=a := congrArg Prod.fst hqz
    subst b
    have huv : u=v := riemannianExp_interior_unique hz hv (congrArg Prod.snd hqz).symm
    subst v
    rfl
  · exact joint_exp_locally_injective z hz

lemma total_injectivityDomain_eq_interior :
    {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} =
      interior {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ minimizingVectors z.1} := by
  apply subset_antisymm
  · exact fun z hz => interior_total_minimizingVectors z hz
  · intro z hz
    apply interior_minimizingVectors_subset z.1
    apply mem_interior_iff_mem_nhds.mpr
    exact (FiberBundle.continuous_totalSpaceMk (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) z.1).continuousAt.preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hz)

lemma isOpen_total_injectivityDomain :
    IsOpen {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} := by
  rw [total_injectivityDomain_eq_interior]
  exact isOpen_interior

end
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_CostSmooth
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_contMDiffAt_of_injectivityDomain (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (z.1,riemannianExp z.1 z.2) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let c := extChartAt 𝓘(ℝ,Model n) z.1
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let y : M×M := (z.1,riemannianExp z.1 z.2)
  let J : M×M → Model n × Model n := fun q => (c q.1,d q.2)
  obtain ⟨e,he,hze,_,hend,_,hei⟩ := exists_joint_exp_inverse z hz
  have hχz := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hJy : J y = e (χ z) := by
    rw [he]
    change (c z.1,d (riemannianExp z.1 z.2)) =
      ((χ z).1,d (riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2))
    rw [hχinv]
    rfl
  have hyT : J y ∈ e.target := hJy ▸ e.map_source hze
  have hiy : e.symm (J y)=χ z := by rw [hJy,e.left_inv hze]
  have hJ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,Model n × Model n) ∞ J y := by
    have hc₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ c y.1 := contMDiffAt_extChartAt
    have hd₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y.2 := contMDiffAt_extChartAt
    exact (hc₀.comp y contMDiffAt_fst).prodMk_space (hd₀.comp y contMDiffAt_snd)
  have hi := (hei.contDiffAt (e.open_target.mem_nhds hyT)).contMDiffAt.comp y hJ
  have hc : ContMDiffAt 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm
      (e.symm (J y)) :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt ((isOpen_extChartAt_target z).mem_nhds (hiy ▸ hχz))
  let P : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => χ.symm (e.symm (J q))
  have hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P y :=
    hc.comp y hi
  have hPy : P y = z := by dsimp [P]; rw [hiy,hχinv]
  have hmin : ∀ᶠ q in 𝓝 y, (P q).2 ∈ minimizingVectors (P q).1 := by
    have hC : {r : TangentBundle 𝓘(ℝ,Model n) M | r.2 ∈ minimizingVectors r.1} ∈ 𝓝 (P y) := by
      rw [hPy]
      exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors z hz)
    exact hP.continuousAt.preimage_mem_nhds hC
  have hJnear : ∀ᶠ q in 𝓝 y, J q ∈ e.target := hJ.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hyT)
  have hcharts : ∀ᶠ q : M×M in 𝓝 y, q.1 ∈ c.source ∧ q.2 ∈ d.source := by
    have hcnear : ∀ᶠ q : M×M in 𝓝 y, q.1 ∈ c.source :=
      (continuous_fst : Continuous (fun q : M×M => q.1)).continuousAt.preimage_mem_nhds
        (show c.source ∈ 𝓝 y.1 from extChartAt_source_mem_nhds z.1)
    have hdnear : ∀ᶠ q : M×M in 𝓝 y, q.2 ∈ d.source :=
      (continuous_snd : Continuous (fun q : M×M => q.2)).continuousAt.preimage_mem_nhds
        (show d.source ∈ 𝓝 y.2 from extChartAt_source_mem_nhds (riemannianExp z.1 z.2))
    exact hcnear.and hdnear
  apply ((contMDiff_tangent_energy (P y)).comp y hP).congr_of_eventuallyEq
  filter_upwards [hmin,hJnear,hcharts] with q hqmin hqJ hqc
  have his := e.map_target hqJ
  have hmap := e.right_inv hqJ
  rw [he] at hmap
  have hfirst : (P q).1=q.1 := by
    change (χ.symm (e.symm (J q))).1=q.1
    rw [tangent_chart_symm_base]
    have hf := congrArg Prod.fst hmap
    change (e.symm (J q)).1=c q.1 at hf
    rw [hf,c.left_inv hqc.1]
  have hlast : riemannianExp (P q).1 (P q).2=q.2 := by
    apply d.injOn (hend _ his) hqc.2
    exact congrArg Prod.snd hmap
  change dist q.1 q.2^2/2 = ‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  calc
    dist q.1 q.2^2/2 = dist (P q).1 (riemannianExp (P q).1 (P q).2)^2/2 := by rw [hlast,hfirst]
    _ = _ := by rw [hqmin]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SplitMinimizingAction
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

lemma minimizing_split_contact {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {s : ℝ} (hs : 0 < s) (hs1 : s<1) :
    cost x (riemannianExp x (s • p))/s + (1-s)*‖p‖^2/2 = cost x (riemannianExp x p) := by
  have hsp := minimizingVectors_smul hp hs.le hs1.le
  unfold cost
  rw [hsp,hp,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  field_simp [hs.ne']
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_CostGradient
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_start_gradient_of_injectivityDomain {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun y => cost y (riemannianExp x p))
      x (innerSL ℝ (-p)) := by
  have hpmin := injectivityDomain_subset_minimizingVectors x hp
  obtain ⟨δ,hδ,H⟩ := exists_local_spray_cost_start_gradient (E := Model n) x
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, riemannianExp x (s • p) ∈ Metric.ball x δ := by
    have ht : ContinuousAt (fun s : ℝ => riemannianExp x (s • p)) 0 :=
      ((continuous_riemannianExp x).comp (continuous_id.smul continuous_const)).continuousAt
    have hx : riemannianExp x ((0:ℝ) • p) ∈ Metric.ball x δ := by simpa using hδ
    exact ht.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0,
      riemannianExp x (s • p) ∈ Metric.ball x δ ∧ s<1 ∧ 0 < s :=
    (hnear.filter_mono nhdsWithin_le_nhds).and
      (((show ∀ᶠ r : ℝ in 𝓝 0, r<1 from eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨s,hy,hs1,hs⟩ := hsmall.exists
  have hz : x ∈ Metric.ball x δ := by simpa using hδ
  have hys : (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 ∈ Metric.ball x δ := by
    rwa [←riemannianExp_smul]
  have hmin : dist x (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=s*‖p‖ := by
    rw [←riemannianExp_smul,minimizingVectors_smul hpmin hs.le hs1.le,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  have hD := H ⟨x,p⟩ s hs hz hys hmin
  rw [←riemannianExp_smul] at hD
  dsimp only at hD
  let G : M → ℝ := fun y => cost y (riemannianExp x (s • p))/s+(1-s)*‖p‖^2/2
  have hG : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) G x (innerSL ℝ (-p)) := by
    have HH := (hD.const_smul (s⁻¹)).add
      (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ)) ((1-s)*‖p‖^2/2) x)
    have hGG : G =ᶠ[𝓝 x]
        ((s⁻¹ • fun y => dist y (riemannianExp x (s • p))^2/2) + fun _ => (1-s)*‖p‖^2/2) := by
      apply Filter.Eventually.of_forall
      intro y
      dsimp [G,cost]
      simp only [div_eq_mul_inv]
      ring
    apply (HH.congr_of_eventuallyEq hGG).congr_mfderiv
    have heq : (s⁻¹ • innerSL ℝ ((-s) • p)) + 0 = innerSL ℝ (-p) := by
      ext v
      simp only [_root_.smul_apply,add_zero,innerSL_apply_apply,real_inner_smul_left,inner_neg_left,smul_eq_mul]
      field_simp [ne_of_gt hs]
    convert! heq using 1
    all_goals try with_reducible_and_instances rfl
  have hcost := cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hF : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun y => cost y (riemannianExp x p)) x :=
    ((hcost.comp x (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp))
  have heq := upper_contact_mfderiv hF hG.mdifferentiableAt
    (Filter.Eventually.of_forall (minimizing_split_upper_support hpmin hs hs1))
    (minimizing_split_contact hpmin hs hs1).symm
  exact hF.hasMFDerivAt.congr_mfderiv (heq.trans hG.mfderiv)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianSmooth
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hessianValue_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    ContDiffAt ℝ ∞ (fun v => hessianValue x v xi) p := by
  have exp_smooth := contMDiff_riemannianExp_fiber (n := n) x
  have hA : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x × ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : TangentSpace 𝓘(ℝ,Model n) x × ℝ => riemannianExp x (q.2 • xi)) (p,(0:ℝ)) :=
    (exp_smooth _).comp (p,(0:ℝ)) (contDiffAt_snd.smul contDiffAt_const).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x × ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : TangentSpace 𝓘(ℝ,Model n) x × ℝ => riemannianExp x q.1) (p,(0:ℝ)) :=
    (exp_smooth _).comp (p,(0:ℝ)) contDiffAt_fst.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x ((0:ℝ) • xi),riemannianExp x p) := by
    simpa only [zero_smul,riemannianExp_zero] using hC
  have hF : ContDiffAt ℝ ∞ (Function.uncurry
      (fun v : TangentSpace 𝓘(ℝ,Model n) x => fun t : ℝ =>
        cost (riemannianExp x (t • xi)) (riemannianExp x v))) (p,(0:ℝ)) :=
    by
      have H := (hC'.comp (p,(0:ℝ)) (hA.prodMk hB)).contDiffAt
      apply H.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun _ => rfl)
  exact contDiffAt_iteratedDeriv_parameter hF 2

lemma WeakMTW.transverse_concaveOn_injectivityDomain
    (hmtw : WeakMTW (n := n) (M := M))
    (x : M) (p xi eta : TangentSpace 𝓘(ℝ,Model n) x)
    {D : Set ℝ} (hD : Convex ℝ D)
    (hline : ∀ s ∈ D, p + s • eta ∈ injectivityDomain x)
    (hortho : inner ℝ xi eta = 0) :
    ConcaveOn ℝ D (fun t : ℝ => hessianValue x (p+t • eta) xi) := by
  have hsmooth : ∀ s ∈ D, ContDiffAt ℝ ∞ (fun t : ℝ => hessianValue x (p+t • eta) xi) s := by
    intro s hs
    exact (hessianValue_contDiffAt (hline s hs) xi).comp s
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  apply hmtw.transverse_concaveOn x p xi eta hD
    (fun s hs => hline s (interior_subset hs)) hortho
  · intro s hs
    exact (hsmooth s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact ((hsmooth s (interior_subset hs)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffWithinAt

end

open Set Filter
open scoped ContDiff Topology

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

lemma normalCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) : ContDiffAt ℝ ∞ (normalCost x p) 0 := by
  have hc := cost_contMDiffAt_of_injectivityDomain (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0 : TangentSpace 𝓘(ℝ,Model n) x),riemannianExp x p) := by
    simpa only [riemannianExp_zero] using hc
  exact (hc'.comp 0 ((contMDiff_riemannianExp_fiber x 0).prodMk contMDiffAt_const)).contDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitAction
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma shifted_injectivityDomain_near_one (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    ∀ᶠ t : ℝ in 𝓝 1,
    (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  let Z : ℝ → TangentBundle 𝓘(ℝ,Model n) M := fun t => tangentScale (1-t) (sprayFlow t ⟨x,p⟩)
  have hZ : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp ((contMDiff_const.sub contMDiff_id).prodMk
      (contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const)))
  have hh : Z 1 ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} := by
    change (1-(1:ℝ)) • (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈ injectivityDomain (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    rw [sub_self,zero_smul]
    exact zero_mem_injectivityDomain _
  exact hZ.continuous.continuousAt.preimage_mem_nhds (isOpen_total_injectivityDomain.mem_nhds hh)

lemma exists_minimizing_two_regular_legs {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) : ∃ t : ℝ, 0<t ∧ t<1 ∧
      t • p ∈ injectivityDomain x ∧
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have H : ∀ᶠ t : ℝ in 𝓝[<] 1, 0<t ∧ t<1 ∧
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    filter_upwards [(shifted_injectivityDomain_near_one x p).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht ht0 ht1
    exact ⟨ht0,ht1,ht⟩
  obtain ⟨t,ht0,ht1,ht⟩ := H.exists
  exact ⟨t,ht0,ht1,contracted_minimizer_mem_injectivityDomain hp ht0 ht1,ht⟩

lemma splitNormalAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (fun z : TangentSpace 𝓘(ℝ,Model n) x ×
        (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) =>
      splitNormalAction x t z.1 z.2) (p,(0,p)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let a : V × (V×V) := (p,(0,p))
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×(V×V)) 𝓘(ℝ,Model n) ∞
      (fun z : V×(V×V) => riemannianExp x z.2.1) a :=
    (he _).comp a (contDiffAt_fst.comp a contDiffAt_snd).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×(V×V)) 𝓘(ℝ,Model n) ∞
      (fun z : V×(V×V) => riemannianExp x (t • z.2.2)) a :=
    (he _).comp a (show ContDiffAt ℝ ∞ (fun z : V×(V×V) => t • z.2.2) a from by fun_prop).contMDiffAt
  have hw : ContMDiffAt 𝓘(ℝ,V×(V×V)) 𝓘(ℝ,Model n) ∞
      (fun z : V×(V×V) => riemannianExp x z.1) a :=
    (he _).comp a contDiffAt_fst.contMDiffAt
  have hc₁ := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc₂ := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  have hc₁' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc₁
  have hc₂' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (t • p),riemannianExp x p) := by
    dsimp only at hc₂
    rw [shifted_exp_endpoint] at hc₂
    simpa only [riemannianExp_smul] using hc₂
  exact ((hc₁'.comp a (hu.prodMk hv)).contDiffAt.div_const t).add
    ((hc₂'.comp a (hv.prodMk hw)).contDiffAt.div_const (1-t))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchCost
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_cost_branch (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (z.1,riemannianExp z.1 z.2) ∧
      ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨P,hP,hPz,hleft,hright⟩ := exists_smooth_exp_branch z hz
  let G : M×M → ℝ := fun q => ‖(P q).2‖^2/2
  refine ⟨G,(contMDiff_tangent_energy (P (z.1,riemannianExp z.1 z.2))).comp _ hP,?_⟩
  let F : TangentBundle 𝓘(ℝ,Model n) M → M×M := fun r => (r.1,riemannianExp r.1 r.2)
  have hF : Continuous F :=
    ((Bundle.contMDiff_proj (fun v : M => TangentSpace 𝓘(ℝ,Model n) v)).prodMk contMDiff_riemannianExp).continuous
  have hPnear : ∀ᶠ q in 𝓝 (F z), ContinuousAt P q := by
    have hzero : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 0 P (F z) := hP.of_le bot_le
    exact ((contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mp hzero).mono
      (fun point hpoint => hpoint.continuousAt)
  have hRnear : ∀ᶠ q in 𝓝 (F z), ∀ᶠ q' in 𝓝 q,
      (P q').1=q'.1 ∧ riemannianExp (P q').1 (P q').2=q'.2 :=
    eventually_eventually_nhds.mpr hright
  filter_upwards [hleft,(hF.continuousAt.eventually (hPnear.and hRnear))] with r hr hnear
  intro hrID
  have hC : {v : TangentBundle 𝓘(ℝ,Model n) M | v.2 ∈ minimizingVectors v.1} ∈ 𝓝 (P (F r)) := by
    rw [show P (F r)=r from hr]
    exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors r hrID)
  have hmin := hnear.1.preimage_mem_nhds hC
  filter_upwards [hmin,hnear.2] with q hqmin hq
  change dist q.1 q.2^2/2=‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  have hd : dist q.1 q.2=‖(P q).2‖ :=
    (congrArg₂ dist hq.1.symm hq.2.symm).trans hqmin
  rw [hd]
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BranchHessian
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_hessian_branch {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ A : TangentSpace 𝓘(ℝ,Model n) x → ℝ, ContDiffAt ℝ ∞ A p ∧
      ∀ᶠ w in 𝓝 p, w ∈ injectivityDomain x → hessianValue x w xi=A w := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  obtain ⟨G,hG,hagree⟩ := exists_smooth_cost_branch (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  let A : V → ℝ := fun w => iteratedDeriv 2 (fun s : ℝ => G (riemannianExp x (s • xi),riemannianExp x w)) 0
  have hG' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (riemannianExp x ((0:ℝ) • xi),riemannianExp x p) := by
    simpa only [zero_smul,riemannianExp_zero] using hG
  have hLs : ContMDiffAt 𝓘(ℝ,V×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : V×ℝ => riemannianExp x (q.2 • xi)) (p,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (p,0) (contDiffAt_snd.smul contDiffAt_const).contMDiffAt
  have hLw : ContMDiffAt 𝓘(ℝ,V×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : V×ℝ => riemannianExp x q.1) (p,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (p,0) contDiffAt_fst.contMDiffAt
  have hGA : ContDiffAt ℝ ∞ (fun q : V×ℝ => G (riemannianExp x (q.2 • xi),riemannianExp x q.1)) (p,0) :=
    (hG'.comp (p,0) (hLs.prodMk hLw)).contDiffAt
  refine ⟨A,contDiffAt_iteratedDeriv_parameter hGA 2,?_⟩
  have hinc : Continuous (fun w : V => (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    FiberBundle.continuous_totalSpaceMk (Model n) (fun y : M => TangentSpace 𝓘(ℝ,Model n) y) x
  filter_upwards [hinc.continuousAt.eventually hagree] with w hw
  intro hwID
  have hcost := hw hwID
  have hcurve : ContinuousAt (fun s : ℝ => (riemannianExp x (s • xi),riemannianExp x w)) 0 :=
    ((contMDiff_riemannianExp_fiber x).continuous.continuousAt.comp
      (show ContinuousAt (fun s : ℝ => s • xi) 0 from by fun_prop)).prodMk continuousAt_const
  have hcurve' : Tendsto (fun s : ℝ => (riemannianExp x (s • xi),riemannianExp x w)) (𝓝 0)
      (𝓝 (x,riemannianExp x w)) := by simpa only [zero_smul,riemannianExp_zero] using hcurve.tendsto
  exact Filter.EventuallyEq.iteratedDeriv_eq 2 (hcost.comp_tendsto hcurve')

lemma nonconjugate_inward_hessian_bounded {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x)
    (hreg : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[<] 1, |hessianValue x (r • p) xi|≤C := by
  obtain ⟨A,hA,hagree⟩ := exists_smooth_hessian_branch hreg xi
  have hline : Tendsto (fun r : ℝ => r • p) (𝓝[<] 1) (𝓝 p) := by
    simpa only [one_smul] using
      (show ContinuousAt (fun r : ℝ => r • p) 1 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hb := ((hA.continuousAt.abs.tendsto).comp hline).eventually_lt_const (show |A p| < |A p|+1 by linarith)
  refine ⟨|A p|+1,?_⟩
  filter_upwards [hline.eventually hagree,hb,
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hr hrB hr0 hr1
  rw [hr (contracted_minimizer_mem_injectivityDomain hp hr0 hr1)]
  exact hrB.le
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_SplitStationary
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma split_regular_legs_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x ∧
      (1-t) • (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have hscale : Continuous (fun v : TangentSpace 𝓘(ℝ,Model n) x => t • v) := by fun_prop
  have h₁ : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x :=
    hscale.continuousAt.preimage_mem_nhds
      ((isOpen_injectivityDomain x).mem_nhds hleft)
  have hZ := contMDiff_tangentScale.comp ((contMDiff_const (c := 1-t)).prodMk (contMDiff_spray_fiber (E := Model n) x t))
  have h₂ : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p,
      (1-t) • (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 :=
    (hZ.continuous.continuousAt (x := p)).preimage_mem_nhds
      (isOpen_total_injectivityDomain.mem_nhds hright)
  exact h₁.and h₂

lemma diagonalSplitAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (diagonalSplitAction x t) (p,p) :=
  (splitNormalAction_contDiffAt hleft hright).comp (p,p)
    (contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_snd))

lemma diagonalSplitAction_stationary {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (diagonalSplitAction x t) (p,p) (0,xi)=0 := by
  have hD := cost_start_gradient_of_injectivityDomain hright
  rw [shifted_exp_endpoint] at hD
  have hD' : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun b => dist b (riemannianExp x p)^2/2)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ ((-(1-t)) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) := by
    simpa only [cost,neg_smul] using hD
  have H := spray_action_line_stationary x p xi t (1-t) (sub_pos.mpr ht1).ne' (riemannianExp x p) hD'
  have hline : ContinuousAt (fun s : ℝ => p+s • xi) 0 := by fun_prop
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, t • (p+s • xi) ∈ injectivityDomain x := by
    have hn := (split_regular_legs_near hleft hright).mono (fun _ h => h.1)
    have hl : Tendsto (fun s : ℝ => p+s • xi) (𝓝 0) (𝓝 p) := by simpa only [ContinuousAt,zero_smul,add_zero] using hline
    exact hl.eventually hn
  have heq : (fun s : ℝ => diagonalSplitAction x t (p,p+s • xi)) =ᶠ[𝓝 0]
      (fun s : ℝ => t*‖p+s • xi‖^2/2 +
        dist (sprayFlow t (⟨x,p+s • xi⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 (riemannianExp x p)^2/2/(1-t)) := by
    filter_upwards [hnear] with s hs
    have hm := injectivityDomain_subset_minimizingVectors x hs
    change dist x (riemannianExp x (t • (p+s • xi)))=‖t • (p+s • xi)‖ at hm
    simp only [diagonalSplitAction,splitNormalAction,riemannianExp_zero,cost]
    rw [hm,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    rw [riemannianExp_smul]
    field_simp
  have hstat := H.congr_of_eventuallyEq heq
  have hp₀ : HasDerivAt (fun s : ℝ => (p,p+s • xi)) (0,xi) 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).prodMk
      ((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const xi)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hf := ((diagonalSplitAction_contDiffAt hleft hright).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hf' : HasFDerivAt (diagonalSplitAction x t)
      (fderiv ℝ (diagonalSplitAction x t) (p,p)) (p,p+(0:ℝ) • xi) := by
    simpa only [zero_smul,add_zero] using hf
  exact (hf'.comp_hasDerivAt (f := fun s : ℝ => (p,p+s • xi)) 0 hp₀).unique hstat

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_DiagonalKernel
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma second_leg_cost_smooth {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (t • p),riemannianExp x p) := by
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  dsimp only at hc
  rw [shifted_exp_endpoint] at hc
  simpa only [riemannianExp_smul] using hc

lemma diagonalSplitAction_endpoint_kernel {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p,
      fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0)=0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  have he := (contMDiff_riemannianExp_fiber (n := n) x).mdifferentiable (by simp)
  have hc := (second_leg_cost_smooth hright).of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hcn : ∀ᶠ z : M×M in 𝓝 (riemannianExp x (t • p),y),
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) 1
        (fun q : M×M => cost q.1 q.2) z :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hc
  have hj : Continuous (fun v : V => (riemannianExp x (t • v),y)) :=
    ((continuous_riemannianExp x).comp (by fun_prop)).prodMk continuous_const
  have hcnear := hj.continuousAt.eventually hcn
  have hF := diagonalSplitAction_contDiffAt hleft hright
  have hFn := (hF.of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)
  have hL : Continuous (fun v : V => (p,v)) := continuous_const.prodMk continuous_id
  have hFnear := hL.continuousAt.eventually hFn
  filter_upwards [hcnear,hFnear] with v hcv hFv
  change ContDiffAt ℝ 1 (diagonalSplitAction x t) (p,v) at hFv
  have hcost := (hcv.comp y (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by norm_num)
  have hD := hcost.hasMFDerivAt.comp p (he p).hasMFDerivAt
  have hD' : HasFDerivAt (fun w : V => cost (riemannianExp x (t • v)) (riemannianExp x w))
      ((mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun z => cost (riemannianExp x (t • v)) z) y).comp
        (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp x) p)) p := by
    convert! hD.hasFDerivAt using 1
    all_goals try with_reducible_and_instances rfl
  have hpart := (hD'.mul_const (1-t)⁻¹).const_add
    (cost x (riemannianExp x (t • v))/t)
  have heqfun : (fun w : V => diagonalSplitAction x t (w,v)) =
      (fun w : V => cost x (riemannianExp x (t • v))/t +
        cost (riemannianExp x (t • v)) (riemannianExp x w)*(1-t)⁻¹) := by
    funext w
    simp only [diagonalSplitAction,splitNormalAction,riemannianExp_zero,div_eq_mul_inv]
  rw [←heqfun] at hpart
  have hl := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const v p)
  have hfull := (hFv.differentiableAt (by norm_num)).hasFDerivAt.comp
    (f := fun w : V => (w,v)) p hl
  have hh := congrArg (fun A : V →L[ℝ] ℝ => A k) (hfull.unique hpart)
  change fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0) =
    (1-t)⁻¹ • (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun z => cost (riemannianExp x (t • v)) z) y)
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp x) p k) at hh
  rw [hk,map_zero,smul_zero] at hh
  exact hh

lemma diagonalSplitAction_conjugate_hessian_null {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,k) (0,k)=0 := by
  apply diagonal_stationary_hessian_null
    ((diagonalSplitAction_contDiffAt hleft hright).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  · exact (split_regular_legs_near hleft hright).mono
      (fun v hv => diagonalSplitAction_stationary ht ht1 hv.1 hv.2 k)
  · exact diagonalSplitAction_endpoint_kernel hleft hright hk

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_SplitTrial
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitTrialValue_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi k : TangentSpace 𝓘(ℝ,Model n) x) :
    ContDiffAt ℝ ∞ (splitTrialValue x t xi k) p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hp := splitNormalAction_contDiffAt hleft hright
  have hl : ContDiffAt ℝ ∞ (fun q : V×ℝ => (q.1,(q.2 • xi,q.1+q.2 • k))) (p,0) := by fun_prop
  have hs : ContDiffAt ℝ ∞ (fun q : V×ℝ => splitNormalAction x t q.1 (q.2 • xi,q.1+q.2 • k)) (p,0) := by
    have hp' : ContDiffAt ℝ ∞ (fun z : V×(V×V) => splitNormalAction x t z.1 z.2)
        (p,((0:ℝ) • xi,p+(0:ℝ) • k)) := by simpa using hp
    exact hp'.comp (p,0) hl
  exact contDiffAt_iteratedDeriv_parameter hs 2

lemma splitTrialValue_middle_eq_diagonal {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    splitTrialValue x t 0 k p =
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,k) (0,k) := by
  simpa only [splitTrialValue,diagonalSplitAction,Prod.fst_add,Prod.smul_fst,
    Prod.snd_add,Prod.smul_snd,smul_zero,add_zero] using
    iteratedDeriv_two_affine_line ((diagonalSplitAction_contDiffAt hleft hright).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ((0 : TangentSpace 𝓘(ℝ,Model n) x),k)

lemma splitTrialValue_conjugate_null {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    splitTrialValue x t 0 k p=0 := by
  rw [splitTrialValue_middle_eq_diagonal hleft hright]
  exact diagonalSplitAction_conjugate_hessian_null ht ht1 hleft hright hk

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_FirstCutLower
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.contracted_segment_concaveOn (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e xi : TangentSpace 𝓘(ℝ,Model n) x} {a b r : ℝ}
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hr : 0 < r) (hr1 : r<1) (hortho : inner ℝ xi e=0) :
    ConcaveOn ℝ (Icc a b) (fun s => hessianValue x (r • (p+s • e)) xi) := by
  have heq (s : ℝ) : r • p+s • (r • e)=r • (p+s • e) := by
    simp only [smul_add,smul_smul,mul_comm]
  have H := hmtw.transverse_concaveOn_injectivityDomain x (r • p) xi (r • e) (convex_Icc a b)
    (fun s hs => by rw [heq]; exact contracted_minimizer_mem_injectivityDomain (hseg s hs) hr hr1)
    (by simp only [real_inner_smul_right,hortho,mul_zero])
  simpa only [heq] using H

lemma WeakMTW.firstcut_transverse_lower (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e xi : TangentSpace 𝓘(ℝ,Model n) x} {a b : ℝ}
    (ha : a<0) (hb : 0<b)
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hleft : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x v)) (p+a • e)))
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hortho : inner ℝ xi e=0) :
    ∃ L : ℝ, ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ s ∈ Icc a b,
      L≤hessianValue x (r • (p+s • e)) xi := by
  have hab : a≤b := (ha.trans hb).le
  obtain ⟨C,hC⟩ := nonconjugate_inward_hessian_bounded (hseg a ⟨le_rfl,hab⟩) hleft xi
  obtain ⟨D,hD⟩ := nonconjugate_inward_hessian_bounded (hseg b ⟨hab,le_rfl⟩) hright xi
  refine ⟨min (-C) (-D),?_⟩
  filter_upwards [hC,hD,
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hrC hrD hr0 hr1
  intro s hs
  have H := (hmtw.contracted_segment_concaveOn hseg hr0 hr1 hortho).min_le_of_mem_Icc
    (show a ∈ Icc a b from ⟨le_rfl,hab⟩) (show b ∈ Icc a b from ⟨hab,le_rfl⟩) hs
  exact (min_le_min (neg_le_of_abs_le hrC) (neg_le_of_abs_le hrD)).trans H

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end


