-- Prove2me | Definitions.Def_OAIQ232A007
-- name    : OAIQ232A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:45:17.794194+00:00
-- url     : https://prove2.me/theorems/5f10e428-fd79-4a20-a1c0-f0367b49f3b6
-- title:
--   Definitions bundle OAIQ232A007 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 9 definitions, 2 inductive types or structures and 25 theorems. The definitions and types are `OAI.WeakMTWTransport.MaximumFamily`, `OAI.WeakMTWTransport.MaximumRow`, `OAI.WeakMTWTransport.actionKernelBilinearNormedAddCommGroup`, `OAI.WeakMTWTransport.chartCenterEnvelope`, `OAI.WeakMTWTransport.chartOuterEnvelope`, `OAI.WeakMTWTransport.graphProjection`, `OAI.WeakMTWTransport.modifiedExcess`, `OAI.WeakMTWTransport.normalCost`, `OAI.WeakMTWTransport.pathLinearApply`, `OAI.WeakMTWTransport.pathLinearApplyL`, `OAI.WeakMTWTransport.regularizedComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_PartialCalculus`, `BiholderTransport_Calculus_PathCalculus`, `BiholderTransport_Contact_GraphProjection`, `BiholderTransport_Convexity_JensenPackage`, `BiholderTransport_Coordinates_CoordinateVariation`, `BiholderTransport_Coordinates_Coordinates`, `BiholderTransport_Coordinates_RadialIdentity`, `BiholderTransport_Geodesics_GaussLemma`, `BiholderTransport_Geodesics_SprayEnergy`, `BiholderTransport_Geodesics_SprayMinimizing`, `BiholderTransport_Geodesics_SprayProjection`, `BiholderTransport_LinearAlgebra_LocalNormalChart`, `BiholderTransport_LocalFlow_SmoothIntegralCurve`, `BiholderTransport_Regularity_ActionKernel`, `BiholderTransport_Regularity_ActualParameter`, `BiholderTransport_Regularity_MaximumFamily`, `BiholderTransport_Regularity_MaximumRow`, `BiholderTransport_Regularity_MetricDefinitions`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A000`, `OAIQ232A001` and `OAIQ232A002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A013`, `OAIQ232A014`, `OAIQ232A015` and `OAIQ232A016`; the statement `OAI.WeakMTWTransport.WeakMTW.exists_maximum_family`.
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
import Definitions.Def_OAIQ232A002

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PartialCalculus
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma directionalDerivative_commute {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (u v : E) :
    directionalDerivative (directionalDerivative f u) v x =
      directionalDerivative (directionalDerivative f v) u x := by
  change (fderiv ℝ (directionalDerivative f u) x) v =
    (fderiv ℝ (directionalDerivative f v) x) u
  rw [(hasFDerivAt_directionalDerivative hf u).fderiv,
    (hasFDerivAt_directionalDerivative hf v).fderiv]
  exact (hf.isSymmSndFDerivAt (by simp)).eq v u

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PathCalculus
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

namespace WeakMTWTransport
universe u w
variable {K : Type w} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedAddCommGroupContinuousLinearMap
attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedSpaceContinuousLinearMap
local instance pathCalculusNormedAddCommGroupContinuousMap_r07ecef_1 :
    NormedAddCommGroup C(K,E →L[ℝ] F) := ContinuousMap.instNormedAddCommGroup
def pathLinearApply (A : C(K,E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E) →ₗ[ℝ] C(K,F) :=
    { toFun := fun u => ⟨fun t => A t (u t),A.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; exact map_add (A t) (u t) (v t)
      map_smul' := by intro c u; ext t; exact map_smul (A t) c (u t) }
  exact L.mkContinuous ‖A‖ (by
      intro u
      change ‖(⟨fun t => A t (u t),A.continuous.clm_apply u.continuous⟩ : C(K,F))‖ ≤ ‖A‖ * ‖u‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact (A t).le_opNorm (u t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] lemma pathLinearApply_apply (A : C(K,E →L[ℝ] F)) (u : C(K,E)) (t : K) :
    pathLinearApply A u t = A t (u t) := rfl

lemma norm_pathLinearApply_le (A : C(K,E →L[ℝ] F)) : ‖pathLinearApply A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact (A t).le_opNorm (u t) |>.trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

def pathLinearApplyL : C(K,E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E →L[ℝ] F) →ₗ[ℝ] C(K,E) →L[ℝ] C(K,F) :=
    { toFun := fun (A : C(K,E →L[ℝ] F)) => pathLinearApply A
      map_add' := by intro A B; ext u t; rfl
      map_smul' := by intro c A; ext u t; rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K,E →L[ℝ] F)) (F := C(K,E) →L[ℝ] C(K,F)) L 1 ?_
  intro A
  change ‖pathLinearApply A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using norm_pathLinearApply_le A

lemma hasFDerivAt_path_comp (f : C(E,F)) (f' : C(E,E →L[ℝ] F))
    (hder : ∀ x, HasFDerivAt f (f' x) x) (u : C(K,E)) :
    HasFDerivAt (fun v : C(K,E) => f.comp v) (pathLinearApply (f'.comp u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hc : IsCompact (range u) := isCompact_range u.continuous
  have huni := hc.uniformContinuousAt_of_continuousAt f'
    (fun _ _ => f'.continuous.continuousAt)
    (r := {z : (E →L[ℝ] F) × (E →L[ℝ] F) | dist z.1 z.2 < ε})
    (Metric.mem_uniformity_dist.mpr ⟨ε,hε,fun {_ _} h => h⟩)
  obtain ⟨δ,hδ,hclose⟩ := Metric.mem_uniformity_dist.mp huni
  filter_upwards [Metric.ball_mem_nhds (0:C(K,E)) hδ] with v hv
  have hvnorm : ‖v‖ < δ := by simpa using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro t
  have hbound : ∀ z ∈ Metric.ball (u t) δ, ‖f' z - f' (u t)‖ ≤ ε := by
    intro z hz
    have hh := hclose (by simpa only [Metric.mem_ball,dist_comm] using hz) (mem_range_self t)
    change dist (f' (u t)) (f' z) < ε at hh
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hh)
  have hb : u t + v t ∈ Metric.ball (u t) δ := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
    exact (v.norm_coe_le_norm t).trans_lt hvnorm
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z (_ : z ∈ Metric.ball (u t) δ) => (hder z).hasFDerivWithinAt)
    hbound (convex_ball (u t) δ) (Metric.mem_ball_self hδ) hb
  have heq : ((f.comp (u+v) - f.comp u - pathLinearApply (f'.comp u) v) t) =
      f (u t + v t) - f (u t) - f' (u t) ((u t + v t) - u t) := by
    simp only [ContinuousMap.sub_apply,ContinuousMap.comp_apply,ContinuousMap.add_apply,
      pathLinearApply_apply,add_sub_cancel_left]
  rw [heq]
  exact hm.trans (by simpa only [add_sub_cancel_left] using
    mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Coordinates
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceReal_solutions
attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceRealContinuousLinearMapId_solutions_2
lemma coordinateChristoffel_self_metric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x v : E) (hg : (g x).IsInvertible) :
    2 * g x (coordinateChristoffel g x v v) v = (fderiv ℝ g x) v v v := by
  have hh := coordinateChristoffel_metric g x v v v hg
  linarith

attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
lemma metric_speed_derivative {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {γ v : ℝ → E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (γ t)) (hi : (g (γ t)).IsInvertible)
    (hs : ∀ a b, g (γ t) a b = g (γ t) b a)
    (hγ : HasDerivAt γ (v t) t)
    (hv : HasDerivAt v (-coordinateChristoffel g (γ t) (v t) (v t)) t) :
    HasDerivAt (fun s => g (γ s) (v s) (v s)) 0 t := by
  have hgγ : HasDerivAt (fun s => g (γ s)) ((fderiv ℝ g (γ t)) (v t)) t :=
    hg.hasFDerivAt.comp_hasDerivAt t hγ
  have hgv : HasDerivAt (fun s => g (γ s) (v s))
      ((fderiv ℝ g (γ t)) (v t) (v t) +
        g (γ t) (-coordinateChristoffel g (γ t) (v t) (v t))) t :=
    hgγ.clm_apply hv
  have h : HasDerivAt (fun s => g (γ s) (v s) (v s))
      (((fderiv ℝ g (γ t)) (v t) (v t) +
        g (γ t) (-coordinateChristoffel g (γ t) (v t) (v t))) (v t) +
        g (γ t) (v t) (-coordinateChristoffel g (γ t) (v t) (v t))) t :=
    hgv.clm_apply hv
  have hid := coordinateChristoffel_self_metric g (γ t) (v t) hi
  have heq : ((fderiv ℝ g (γ t)) (v t) (v t) +
      g (γ t) (-coordinateChristoffel g (γ t) (v t) (v t))) (v t) +
      g (γ t) (v t) (-coordinateChristoffel g (γ t) (v t) (v t)) = 0 := by
    simp only [add_apply,map_neg,neg_apply]
    rw [hs (v t) (coordinateChristoffel g (γ t) (v t) (v t))]
    linarith
  exact heq ▸ h

lemma coordinate_geodesic_speed_constant
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {γ v : ℝ → E} {a b s t : ℝ}
    (hg : ∀ r ∈ Ioo a b, DifferentiableAt ℝ g (γ r))
    (hi : ∀ r ∈ Ioo a b, (g (γ r)).IsInvertible)
    (hs : ∀ r ∈ Ioo a b, ∀ u w, g (γ r) u w = g (γ r) w u)
    (hder : ∀ r ∈ Ioo a b, HasDerivAt γ (v r) r ∧
      HasDerivAt v (-coordinateChristoffel g (γ r) (v r) (v r)) r)
    (hs_mem : s ∈ Ioo a b) (ht_mem : t ∈ Ioo a b) :
    g (γ s) (v s) (v s) = g (γ t) (v t) (v t) := by
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (fun q => g (γ q) (v q) (v q)) 0 r :=
    fun r hr => metric_speed_derivative (hg r hr) (hi r hr) (hs r hr)
      (hder r hr).1 (hder r hr).2
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs_mem ht_mem

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GaussLemma
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.gaussLemmaNormedSpace
attribute [local instance] OAI.WeakMTWTransport.gaussLemmaDualNormedAddCommGroup
attribute [local instance] OAI.WeakMTWTransport.gaussLemmaDualNormedSpace
attribute [local instance] OAI.WeakMTWTransport.gaussLemmaBilinearNormedAddCommGroup
attribute [local instance] OAI.WeakMTWTransport.gaussLemmaBilinearNormedSpace
local instance gaussLemmaTrilinearNormedAddCommGroup_r07ecef_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance gaussLemmaTrilinearNormedSpace_r07ecef_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
lemma metric_geodesic_variation_derivative {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {γ V J : ℝ → E} {t : ℝ} {W : E}
    (hg : DifferentiableAt ℝ g (γ t)) (hi : (g (γ t)).IsInvertible)
    (hγ : HasDerivAt γ (V t) t)
    (hV : HasDerivAt V (-coordinateChristoffel g (γ t) (V t) (V t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun q => g (γ q) (V q) (J q))
      ((1/2:ℝ) * (fderiv ℝ g (γ t)) (J t) (V t) (V t) + g (γ t) (V t) W) t := by
  have h := ((hg.hasFDerivAt.comp_hasDerivAt t hγ).clm_apply hV).clm_apply hJ
  have hk := coordinateChristoffel_metric g (γ t) (V t) (V t) (J t) hi
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [Function.comp_apply,add_apply,map_neg,neg_apply]
  linarith

lemma variation_mixed_derivative {A V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hAV : ∀ z ∈ U, HasDerivAt (fun t => A (t,z.2)) (V z) z.1)
    {t s : ℝ} (hz : (t,s) ∈ U) :
    HasDerivAt (fun q => directionalDerivative A (0,1) (q,s))
      (directionalDerivative V (0,1) (t,s)) t := by
  have hAt := hA.contDiffAt (hU.mem_nhds hz)
  have heq : directionalDerivative A (1,0) =ᶠ[𝓝 (t,s)] V := by
    filter_upwards [hU.mem_nhds hz] with z hz
    exact (hasDerivAt_slice_left ((hA.contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).unique (hAV z hz)
  have hm := directionalDerivative_commute hAt (0,1) (1,0)
  have heval : directionalDerivative (directionalDerivative A (1,0)) (0,1) (t,s) =
      directionalDerivative V (0,1) (t,s) := by
    unfold directionalDerivative
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] E => L (0,1)) heq.fderiv_eq
  rw [heval] at hm
  exact hm ▸ hasDerivAt_slice_left
    ((contDiffAt_directionalDerivative hAt (0,1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma coordinate_gauss_variation
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {A V : ℝ × ℝ → E} {a b c d : ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo c d))
    (hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo c d))
    (himg : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c d, A (t,s) ∈ S)
    (hode : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c d,
      HasDerivAt (fun q => A (q,s)) (V (t,s)) t ∧
      HasDerivAt (fun q => V (q,s))
        (-coordinateChristoffel g (A (t,s)) (V (t,s)) (V (t,s))) t)
    {x : E} {ν : ℝ → E}
    (h0 : 0 ∈ Ioo a b) (hA0 : ∀ s ∈ Ioo c d, A (0,s) = x)
    (hV0 : ∀ s ∈ Ioo c d, V (0,s) = ν s)
    {s t : ℝ} {w : E} (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d)
    (hν : HasDerivAt ν w s) :
    g (A (t,s)) (V (t,s)) (directionalDerivative A (0,1) (t,s)) =
      t * g x (ν s) w := by
  have hopen : IsOpen (Ioo a b ×ˢ Ioo c d) := isOpen_Ioo.prod isOpen_Ioo
  have hgd : ∀ q ∈ Ioo a b, ∀ r ∈ Ioo c d, DifferentiableAt ℝ g (A (q,r)) :=
    fun q hq r hr => (hg.contDiffAt (hS.mem_nhds (himg q hq r hr))).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ∀ q ∈ Ioo a b, ∀ r ∈ Ioo c d,
      g (A (q,r)) (V (q,r)) (V (q,r)) = g x (ν r) (ν r) := by
    intro q hq r hr
    have hh := coordinate_geodesic_speed_constant
      (fun p hp => hgd p hp r hr) (fun p hp => hi _ (himg p hp r hr))
      (fun p hp => hsym _ (himg p hp r hr)) (fun p hp => hode p hp r hr) hq h0
    simpa only [hA0 r hr,hV0 r hr] using hh
  have hder : ∀ q ∈ Ioo a b,
      HasDerivAt (fun p => g (A (p,s)) (V (p,s))
        (directionalDerivative A (0,1) (p,s))) (g x (ν s) w) q := by
    intro q hq
    let J := directionalDerivative A (0,1) (q,s)
    let W := directionalDerivative V (0,1) (q,s)
    have hAr := hasDerivAt_slice_right
      ((hA.contDiffAt (hopen.mem_nhds ⟨hq,hs⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hVr := hasDerivAt_slice_right
      ((hV.contDiffAt (hopen.mem_nhds ⟨hq,hs⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hE := (((hgd q hq s hs).hasFDerivAt.comp_hasDerivAt s hAr).clm_apply hVr).clm_apply hVr
    have hE0 := ((hasDerivAt_const s (g x)).clm_apply hν).clm_apply hν
    have heq : (fun r => g (A (q,r)) (V (q,r)) (V (q,r))) =ᶠ[𝓝 s]
        (fun r => g x (ν r) (ν r)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact he q hq r hr
    have hval := (hE.congr_of_eventuallyEq heq.symm).unique hE0
    have hJ := variation_mixed_derivative hopen hA
      (fun z hz => (hode z.1 hz.1 z.2 hz.2).1) (hz := ⟨hq,hs⟩)
    have hG := metric_geodesic_variation_derivative
      (γ := fun p => A (p,s)) (V := fun p => V (p,s))
      (J := fun p => directionalDerivative A (0,1) (p,s)) (hgd q hq s hs)
      (hi _ (himg q hq s hs)) (hode q hq s hs).1 (hode q hq s hs).2 hJ
    have hval' : (1/2:ℝ) * (fderiv ℝ g (A (q,s))) J (V (q,s)) (V (q,s)) +
        g (A (q,s)) (V (q,s)) W = g x (ν s) w := by
      simp only [Function.comp_apply,add_apply,zero_apply,zero_add] at hval
      rw [hsym _ (himg q hq s hs) W (V (q,s)),
        hsym x (hA0 s hs ▸ himg 0 h0 s hs) w (ν s)] at hval
      linarith
    exact hval' ▸ hG
  have hJ0 : directionalDerivative A (0,1) (0,s) = 0 := by
    have hAr := hasDerivAt_slice_right
      ((hA.contDiffAt (hopen.mem_nhds ⟨h0,hs⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have heq : (fun r => A (0,r)) =ᶠ[𝓝 s] (fun _ => x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact hA0 r hr
    exact (hAr.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s x)
  have hd : ∀ q ∈ Ioo a b,
      HasDerivAt (fun p => g (A (p,s)) (V (p,s))
        (directionalDerivative A (0,1) (p,s)) - p * g x (ν s) w) 0 q := by
    intro q hq
    convert (hder q hq).sub ((hasDerivAt_id q).mul_const (g x (ν s) w)) using 1 <;>
      first | rfl | simp only [one_mul,sub_self]
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun q hq => (hd q hq).differentiableAt.differentiableWithinAt)
    (fun q hq => (hd q hq).deriv) ht h0
  simpa only [hJ0,map_zero,zero_mul,sub_zero,sub_eq_zero] using heq

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LocalNormalChart
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positive_bilinear_cauchy_schwarz (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v : E, v ≠ 0 → 0 < g v v)
    (hsym : ∀ u v, g u v = g v u) (u v : E) :
    (g u v)^2 ≤ g u u * g v v := by
  by_cases hv : v = 0
  · simp only [hv,map_zero,mul_zero,zero_pow,le_refl,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  have hgv : 0 < g v v := hg v hv
  have h := positive_bilinear_nonneg g hg ((g v v) • u - (g u v) • v)
  simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul] at h
  rw [hsym v u] at h
  have hmul : 0 ≤ g v v * (g u u * g v v - (g u v)^2) := by nlinarith [h]
  have hsub : 0 ≤ g u u * g v v - (g u v)^2 := (mul_nonneg_iff_of_pos_left hgv).mp hmul
  linarith

lemma positive_bilinear_abs_le (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v : E, v ≠ 0 → 0 < g v v)
    (hsym : ∀ u v, g u v = g v u) (u v : E) :
    |g u v| ≤ Real.sqrt (g u u) * Real.sqrt (g v v) := by
  have hu := positive_bilinear_nonneg g hg u
  have hv := positive_bilinear_nonneg g hg v
  have h := positive_bilinear_cauchy_schwarz g hg hsym u v
  have hsq : (Real.sqrt (g u u) * Real.sqrt (g v v))^2 = g u u * g v v := by
    rw [mul_pow,Real.sq_sqrt hu,Real.sq_sqrt hv]
  have hn : 0 ≤ Real.sqrt (g u u) * Real.sqrt (g v v) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (g u v)]

end WeakMTWTransport

open MeasureTheory
open scoped ContDiff ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateVariation
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceReal_solutions_1
local instance instNormedSpaceRealContinuousLinearMapId_solutions_3_r07ecef_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_3_r07ecef_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_4_r07ecef_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_4_r07ecef_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_5_r07ecef_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_5_r07ecef_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
lemma coordinateChristoffel_smul_left (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) (c : ℝ) :
    coordinateChristoffel g x (c • u) v = c • coordinateChristoffel g x u v := by
  unfold coordinateChristoffel
  rw [←map_smul]
  congr 1
  ext w
  simp only [smul_apply,map_smul,sub_apply,add_apply,flip_apply,smul_eq_mul]
  ring

lemma coordinateChristoffel_smul_right (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x u v : E) (c : ℝ) :
    coordinateChristoffel g x u (c • v) = c • coordinateChristoffel g x u v := by
  unfold coordinateChristoffel
  rw [←map_smul]
  congr 1
  ext w
  simp only [smul_apply,map_smul,sub_apply,add_apply,flip_apply,smul_eq_mul]
  ring
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayEnergy
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_spray_energy_symm (a : TangentBundle 𝓘(ℝ,E) M) (q : E × E)
    (hq : q.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target) :
    riemannianCoordinateMetric a.1 q.1 q.2 q.2 =
      ‖((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm q).2‖ ^ 2 := by
  rw [riemannianCoordinateMetric_apply]
  have hbase : (extChartAt 𝓘(ℝ,E) a.1).symm q.1 ∈
      (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a.1).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) a.1).map_target hq
  rw [Trivialization.symmL_apply _ hbase]
  have he : (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a.1).symm
      ((extChartAt 𝓘(ℝ,E) a.1).symm q.1) q.2 =
      tangentCoordChange 𝓘(ℝ,E) a.1 ((extChartAt 𝓘(ℝ,E) a.1).symm q.1)
        ((extChartAt 𝓘(ℝ,E) a.1).symm q.1) q.2 :=
    (tangentBundleCore 𝓘(ℝ,E) M).localTriv_symm_apply (i := achart E a.1) hbase q.2
  rw [he]
  change inner ℝ ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm q).2
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm q).2 = _
  exact real_inner_self_eq_norm_sq _

lemma coordinate_spray_energy (a z : TangentBundle 𝓘(ℝ,E) M)
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source) :
    riemannianCoordinateMetric a.1
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).1
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).2
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).2 = ‖z.2‖ ^ 2 := by
  rw [coordinate_spray_energy_symm a _ ((extChartAt 𝓘(ℝ,E) a.1).map_source hz)]
  rw [(extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).left_inv
    ((tangent_chart_source_iff a z).mpr hz)]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_SmoothIntegralCurve
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  {v : (x : M) → TangentSpace I x}

variable (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

omit [CompleteSpace E] [HasContDiffBump E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
lemma completeFlow_zero (x : M) : completeFlow hc 0 x = x := (Classical.choose_spec (hc x)).1

omit [CompleteSpace E] [HasContDiffBump E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
lemma completeFlow_curve (x : M) : IsMIntegralCurve (fun t => completeFlow hc t x) v :=
  (Classical.choose_spec (hc x)).2

variable (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
include hv

omit [CompleteSpace E] [HasContDiffBump E] in
lemma completeFlow_add (s t : ℝ) (x : M) :
    completeFlow hc (s+t) x = completeFlow hc s (completeFlow hc t x) := by
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ((completeFlow_curve hc x).comp_add t)
    (completeFlow_curve hc (completeFlow hc t x))
    (by simpa only [Function.comp_apply,zero_add] using
      (completeFlow_zero hc (completeFlow hc t x)).symm)
  exact congrFun he s

omit [CompleteSpace E] [HasContDiffBump E] in
lemma completeFlow_eq_local {r : ℝ} (hr : 0 < r) {U : Set M} {Φ : ℝ × M → M}
    (hΦ0 : ∀ x ∈ U, Φ (0,x) = x)
    (hΦode : ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t,x)) v (Ioo (-r) r))
    {x : M} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-r) r) :
    completeFlow hc t x = Φ (t,x) := by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨neg_lt_zero.mpr hr,hr⟩ (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((completeFlow_curve hc x).isMIntegralCurveOn _) (hΦode x hx) _ ht
  exact (completeFlow_zero hc x).trans (hΦ0 x hx).symm

omit [CompleteSpace E] [HasContDiffBump E] in
lemma completeFlow_smooth_step {r : ℝ} (hr : 0 < r) {U : Set M} (hU : IsOpen U)
    {Φ : ℝ × M → M}
    (hΦ : ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ Φ (Ioo (-r) r ×ˢ U))
    (hΦ0 : ∀ x ∈ U, Φ (0,x) = x)
    (hΦode : ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t,x)) v (Ioo (-r) r))
    {s t : ℝ} {a : M} (hs : ContMDiffAt I I ∞ (completeFlow hc s) a)
    (ha : completeFlow hc s a ∈ U) (ht : t-s ∈ Ioo (-r) r) :
    ContMDiffAt I I ∞ (completeFlow hc t) a := by
  have hsm := (hΦ.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht,ha⟩)).comp a
    (contMDiffAt_const.prodMk hs)
  apply hsm.congr_of_eventuallyEq
  have hnear := hs.continuousAt.preimage_mem_nhds (hU.mem_nhds ha)
  filter_upwards [hnear] with x hx
  change completeFlow hc t x = Φ (t-s,completeFlow hc s x)
  rw [← completeFlow_eq_local hc hv hr hΦ0 hΦode hx ht,← completeFlow_add hc hv,sub_add_cancel]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayProjection
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

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma coordinate_geodesic_scale {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {q : ℝ → E × E} {t c : ℝ}
    (hq : HasDerivAt q (coordinateGeodesicField g (q (c*t))) (c*t)) :
    HasDerivAt (fun s => ((q (c*s)).1,c • (q (c*s)).2))
      (coordinateGeodesicField g ((q (c*t)).1,c • (q (c*t)).2)) t := by
  have hq₁ : HasDerivAt (fun s => (q s).1) (q (c*t)).2 (c*t) :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt (c*t) hq
  have hq₂ : HasDerivAt (fun s => (q s).2)
      (-coordinateChristoffel g (q (c*t)).1 (q (c*t)).2 (q (c*t)).2) (c*t) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt (c*t) hq
  have h₁ := hq₁.scomp t ((hasDerivAt_id t).const_mul c)
  have h₂ := (hq₂.scomp t ((hasDerivAt_id t).const_mul c)).const_smul c
  have h := h₁.prodMk h₂
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [coordinateGeodesicField,coordinateChristoffel_smul_left,
    coordinateChristoffel_smul_right,mul_one,smul_neg]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayMinimizing
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

lemma coordinate_geodesic_affine {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {q : ℝ → E × E} {s t c : ℝ}
    (hq : HasDerivAt q (coordinateGeodesicField g (q (s+c*t))) (s+c*t)) :
    HasDerivAt (fun w => ((q (s+c*w)).1,c • (q (s+c*w)).2))
      (coordinateGeodesicField g ((q (s+c*t)).1,c • (q (s+c*t)).2)) t := by
  have hq₁ : HasDerivAt (fun w => (q w).1) (q (s+c*t)).2 (s+c*t) :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt (s+c*t) hq
  have hq₂ : HasDerivAt (fun w => (q w).2)
      (-coordinateChristoffel g (q (s+c*t)).1 (q (s+c*t)).2 (q (s+c*t)).2) (s+c*t) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt (s+c*t) hq
  have h₁ := hq₁.scomp t (((hasDerivAt_id t).const_mul c).const_add s)
  have h₂ := (hq₂.scomp t (((hasDerivAt_id t).const_mul c).const_add s)).const_smul c
  convert! h₁.prodMk h₂ using 1
  all_goals try with_reducible_and_instances rfl
  simp only [coordinateGeodesicField,coordinateChristoffel_smul_left,
    coordinateChristoffel_smul_right,mul_one,smul_neg]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActionKernel
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.WeakMTWTransport.actionKernelDualNormedAddCommGroup
attribute [local instance] OAI.WeakMTWTransport.actionKernelDualNormedSpace
local instance actionKernelBilinearNormedAddCommGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

end

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

def normalCost (x : M) (p u : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x u) (riemannianExp x p)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
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

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

lemma exists_cTransform_contact {v : M → ℝ} (hv : Continuous v) (x : M) :
    ∃ y, cTransform v x = -cost x y - v y ∧
      ∀ z, -cost x z - v z ≤ cTransform v x := by
  obtain ⟨y, _, hy⟩ := isCompact_univ.exists_isMaxOn
    Set.univ_nonempty (((continuous_cost_right x).neg.sub hv).continuousOn)
  have hg : IsGreatest (Set.range (fun y => -cost x y - v y)) (-cost x y - v y) := by
    refine ⟨Set.mem_range_self y, ?_⟩
    rintro a ⟨z, rfl⟩
    exact hy (Set.mem_univ z)
  refine ⟨y, hg.csSup_eq, ?_⟩
  intro z
  rw [cTransform, hg.csSup_eq]
  exact hy (Set.mem_univ z)

lemma cTransform_gap_nonneg {v : M → ℝ} (hv : Continuous v) (x y : M) :
    0 ≤ contactGap (cTransform v) v x y := by
  obtain ⟨_, _, hmax⟩ := exists_cTransform_contact hv x
  dsimp [contactGap]
  linarith [hmax y]

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

def graphProjection (u : M → ℝ) (t : ℝ) (z : subgradientGraph (n := n) u) : M :=
  riemannianExp z.1.1 (t • z.1.2)

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenPackage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev chartOuterEnvelope (v : M → ℝ) (t : ℝ) (a : M) : Model n → ℝ :=
  fun z=>hopfLax t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm z)
abbrev chartCenterEnvelope (g : M → ℝ) (t : ℝ) (a : M) : Model n → ℝ :=
  fun z=>hopfLax (1-t) g ((extChartAt 𝓘(ℝ,Model n) a).symm z)
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

def modifiedExcess (v : M → ℝ) (a D b : ℝ) (Bc Bo : ℝ → ℝ) (y : M) : ℝ :=
  modifiedDatum v a D b Bc y-cTransform (cTransform (modifiedDatum v a D b Bo)) y

def regularizedComparison (v : M → ℝ) (a D bplus t : ℝ)
    (Bc Bo : ℝ → ℝ) (q : ℝ×M) : ℝ :=
  hopfLax t (cTransform (modifiedDatum v a D q.1 Bo)) q.2+
    hopfLax (1-t) (modifiedDatum v a D q.1 Bc) q.2-parameterPenalty bplus q.1

end CompactEnvelopes

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumRow
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

structure MaximumRow (v : M → ℝ) (a D b bplus t : ℝ) (Bc Bo : ℝ → ℝ) (z : M) where
  q : subgradientGraph (n := n) (cTransform (modifiedDatum v a D b Bo))
  minimizing : q.1.2∈minimizingVectors q.1.1
  projection : graphProjection (cTransform (modifiedDatum v a D b Bo)) t q=z
  activeHull : q.1.2∈convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) q.1.1)
  center : ∀ w,hopfLax (1-t) (modifiedDatum v a D b Bc) z=
    modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=riemannianExp q.1.1 q.1.2
  value : regularizedComparison v a D bplus t Bc Bo (b,z)=
    modifiedExcess v a D b Bc Bo (riemannianExp q.1.1 q.1.2)-parameterPenalty bplus b
  parameter : ∀ (ι : Type) [Fintype ι] [Nonempty ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) q.1.1) (weights : ι → ℝ),
    (∀ i,0<weights i) → (∑ i,weights i=1) → (∑ i,weights i • pj i=q.1.2) →
    (∀ i,pj i∈activeLogs (modifiedDatum v a D b Bo) q.1.1) →
    1/4096+4*b/bplus ≤ Bc ((v (riemannianExp q.1.1 q.1.2)-a)/D)-
      ∑ i,weights i*Bo ((v (riemannianExp q.1.1 (pj i))-a)/D)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumFamily
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

structure MaximumFamily (v : M → ℝ) (α D bminus bplus : ℝ) (Bc Bo : ℝ → ℝ) where
  t : ℕ → ℝ
  b : ℕ → ℝ
  z : ℕ → M
  prefixTime : ∀ k,0<t k ∧ t k<1
  parameter : ∀ k,b k∈Ioo bminus bplus
  time : Tendsto t atTop (𝓝 1)
  positive : ∀ k,0 < regularizedComparison v α D bplus (t k) Bc Bo (b k,z k)
  maximum : ∀ k,∀ w:ℝ×M,w.1∈Icc bminus bplus →
    regularizedComparison v α D bplus (t k) Bc Bo w≤
      regularizedComparison v α D bplus (t k) Bc Bo (b k,z k)
  row : ∀ k,MaximumRow (n := n) v α D (b k) bplus (t k) Bc Bo (z k)

end WeakMTWTransport

end

end OAI
end


