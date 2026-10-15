-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Functor
-- name    : OAI_Analysis_LipschitzFree_Functor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:36:55.423103+00:00
-- url     : https://prove2.me/theorems/609cdf5c-af36-4a80-b961-e95c82461ef8
-- title:
--   Linearization of base-point-preserving $1$-Lipschitz maps between Lipschitz-free spaces
-- statement:
--   For a pointed metric space $(M,o)$, $\mathrm{Lip}_0(M,o)$ denotes the real Banach space of Lipschitz functions $g\colon M\to\mathbb{R}$ with $g(o)=0$, normed by the best Lipschitz constant $\|g\|=\sup_{x\neq y}|g(x)-g(y)|/d(x,y)$; for $x\in M$ the evaluation $\delta_x(g)=g(x)$ is a bounded linear functional on it, and the Lipschitz-free space $\mathcal{F}(M,o)$ is the closed linear span of $\{\delta_x: x\in M\}$ in the dual space $\mathrm{Lip}_0(M,o)^*$.
--
--   Let $(M,o)$ and $(N,b)$ be pointed metric spaces and let $f\colon M\to N$ be a $1$-Lipschitz map with $f(o)=b$.
--
--   1. **Composition operator.** $f^{\#}\colon\mathrm{Lip}_0(N,b)\to\mathrm{Lip}_0(M,o)$, $f^{\#}g=g\circ f$, is a bounded linear operator with $\|f^{\#}\|\le1$; explicitly $(f^{\#}g)(x)=g(f(x))$.
--   2. **Free spaces are preserved.** For every $u\in\mathcal{F}(M,o)$, the functional $u\circ f^{\#}$ on $\mathrm{Lip}_0(N,b)$ belongs to $\mathcal{F}(N,b)$.
--   3. **Linearization.** The operator $\widehat f\colon\mathcal{F}(M,o)\to\mathcal{F}(N,b)$, $\widehat f(u)=u\circ f^{\#}$, is bounded and linear with $\|\widehat f\|\le1$, and it acts on point evaluations by
--   $$
--   \widehat f(\delta_x)=\delta_{f(x)}\qquad(x\in M).
--   $$
--   4. **Determination by point evaluations.** If $E$ is a real normed space and $T,U\colon\mathcal{F}(M,o)\to E$ are bounded linear operators with $T\delta_x=U\delta_x$ for every $x\in M$, then $T=U$.
--
--   This is the functoriality of the Lipschitz-free construction for contractions: a $1$-Lipschitz retraction of metric spaces becomes a norm-one projection between free spaces, and identities between composites of such maps can be checked on point evaluations. It is used for the inclusions, retractions and finite-component projections of metric wedges.
--
--   **Formalization Note** The objects are `Lip0 o`, `FreeSpace o`, `delta o x`, `lipPullback o b f hbase hf` (item 1, with `lipPullback_apply` and `lipPullback_bound`), `pullback_mem_free` (item 2), `freeMap o b f hbase hf` with `freeMap_delta` (item 3) and `freeMap_ext` (item 4). The norm on `Lip0 o` is the supremum norm of the slope function $(x,y)\mapsto (g(x)-g(y))/d(x,y)$, whose diagonal values are $0$ by the convention $0/0=0$. The bound $\|\widehat f\|\le1$ is built into the definition via `LinearMap.mkContinuous` with constant $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Functor.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Functor.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction

namespace OAI

/-!
# Contractive linearization of pointed Lipschitz maps
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

def lipPullback (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : Lip0 b →L[ℝ] Lip0 o :=
  LinearMap.mkContinuous
    { toFun := fun g => Lip0.ofBound o (fun x => g (f x)) (by simp [hbase])
        ‖g‖ (norm_nonneg _) (fun x y => (Lip0.sub_le g (f x) (f y)).trans
          (mul_le_mul_of_nonneg_left (by simpa using hf.dist_le_mul x y) (norm_nonneg _)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun g => by
      rw [one_mul]
      apply (Lip0.norm_le_iff _ (norm_nonneg _)).mpr
      intro x y
      exact (Lip0.sub_le g (f x) (f y)).trans
        (mul_le_mul_of_nonneg_left (by simpa using hf.dist_le_mul x y) (norm_nonneg _)))

@[simp] theorem lipPullback_apply (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) (g : Lip0 b) (x : M) :
    lipPullback o b f hbase hf g x = g (f x) := rfl

theorem lipPullback_bound (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : ‖lipPullback o b f hbase hf‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro g
  rw [one_mul]
  apply (Lip0.norm_le_iff _ (norm_nonneg _)).mpr
  intro x y
  exact (Lip0.sub_le g (f x) (f y)).trans
    (mul_le_mul_of_nonneg_left (by simpa using hf.dist_le_mul x y) (norm_nonneg _))

theorem pullback_mem_free (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) (u : FreeSpace o) :
    u.val.comp (lipPullback o b f hbase hf) ∈ freeSubmodule b := by
  let L : FreeSpace o →L[ℝ] (Lip0 b →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ (Lip0 b) (Lip0 o) ℝ).flip
      (lipPullback o b f hbase hf)).comp (freeSubmodule o).subtypeL
  change L u ∈ freeSubmodule b
  apply freeSpace_induction (fun v => L v ∈ freeSubmodule b)
    ((Submodule.isClosed_topologicalClosure _).preimage L.continuous)
    (by simp) (fun v w hv hw => by simpa using (freeSubmodule b).add_mem hv hw)
    (fun c v hv => by simpa using (freeSubmodule b).smul_mem c hv) (fun x => ?_) u
  change evaluation b (f x) ∈ freeSubmodule b
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self _))

def freeMap (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) : FreeSpace o →L[ℝ] FreeSpace b :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨u.val.comp (lipPullback o b f hbase hf), pullback_mem_free o b f hbase hf u⟩
      map_add' := fun u v => by apply Subtype.ext; ext g; rfl
      map_smul' := fun c u => by apply Subtype.ext; ext g; rfl }
    1 (fun u => by
      change ‖u.val.comp (lipPullback o b f hbase hf)‖ ≤ 1*‖u‖
      calc
        _ ≤ ‖u.val‖*‖lipPullback o b f hbase hf‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖u.val‖*1 := mul_le_mul_of_nonneg_left (lipPullback_bound o b f hbase hf) (norm_nonneg _)
        _ = _ := by simp; rfl)

@[simp] theorem freeMap_delta (o : M) (b : N) (f : M → N) (hbase : f o = b)
    (hf : LipschitzWith 1 f) (x : M) :
    freeMap o b f hbase hf (delta o x) = delta b (f x) := rfl

theorem freeMap_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (o : M)
    {T U : FreeSpace o →L[ℝ] E} (h : ∀ x, T (delta o x) = U (delta o x)) : T = U := by
  ext u
  exact freeSpace_induction (fun u => T u = U u) (isClosed_eq T.continuous U.continuous)
    (by simp) (fun u v hu hv => by simp [hu,hv])
    (fun c u hu => by simp [hu]) h u

end DiscreteFree
end

end

end OAI


