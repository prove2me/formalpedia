-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Functor__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Functor__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:33:08.634577+00:00
-- url     : https://prove2.me/theorems/e19c05e9-2274-454a-a51e-60de46cf6d75
-- title:
--   Linearization of base-point-preserving $1$-Lipschitz maps between Lipschitz-free spaces
-- statement:
--   For a pointed metric space $(M,o)$, $\mathrm{Lip}_0(M,o)$ is the real normed space of functions $g\colon M\to\mathbb{R}$ with $g(o)=0$ that are Lipschitz for some constant, normed by the best Lipschitz constant $\|g\|=\sup_{x\neq y}|g(x)-g(y)|/d(x,y)$. For $x\in M$ the evaluation $\delta_x(g)=g(x)$ is a bounded linear functional on $\mathrm{Lip}_0(M,o)$, and the Lipschitz-free space $\mathcal{F}(M,o)$ is the closure of the linear span of $\{\delta_x:x\in M\}$ in the dual space $\mathrm{Lip}_0(M,o)^\ast$.
--
--   Let $(M,o)$ and $(N,b)$ be pointed metric spaces and $f\colon M\to N$ a $1$-Lipschitz map with $f(o)=b$.
--
--   1. **Composition operator.** $f^{\#}\colon\mathrm{Lip}_0(N,b)\to\mathrm{Lip}_0(M,o)$, $(f^{\#}g)(x)=g(f(x))$, is a bounded linear operator with $\|f^{\#}\|\le1$.
--   2. **Free spaces are preserved.** For every $u\in\mathcal{F}(M,o)$, the functional $u\circ f^{\#}\colon g\mapsto u(g\circ f)$ on $\mathrm{Lip}_0(N,b)$ belongs to $\mathcal{F}(N,b)$.
--   3. **Linearization.** The operator $\widehat f\colon\mathcal{F}(M,o)\to\mathcal{F}(N,b)$, $\widehat f(u)=u\circ f^{\#}$, is bounded and linear with $\|\widehat f\|\le1$, and on point evaluations
--   $$
--   \widehat f(\delta_x)=\delta_{f(x)}\qquad(x\in M).
--   $$
--   4. **Determination by point evaluations.** If $E$ is a real normed space and $T,U\colon\mathcal{F}(M,o)\to E$ are bounded linear operators with $T\delta_x=U\delta_x$ for every $x\in M$, then $T=U$.
--
--   This is the functoriality of the Lipschitz-free construction for base-point-preserving contractions: a $1$-Lipschitz retraction of pointed metric spaces becomes a norm-one projection of free spaces, and identities between composites of linearized maps can be checked on point evaluations alone. It is used to linearize the inclusions, retractions and finite-component collapses of metric wedges.
--
--   **Formalization Note** The objects are `lipPullback o b f hbase hf` (item 1, with `lipPullback_apply` and `lipPullback_bound`), `pullback_mem_free` (item 2), `freeMap o b f hbase hf` with `freeMap_delta` (item 3) and `freeMap_ext` (item 4); `hbase : f o = b` and `hf : LipschitzWith 1 f`. The norm on `Lip0 o` is the supremum norm of the slope function $(x,y)\mapsto (g(x)-g(y))/d(x,y)$, whose diagonal values are $0$ by the convention $0/0=0$. The bound $\|\widehat f\|\le1$ is built into the definition through `LinearMap.mkContinuous` with constant $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Functor.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Functor.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction__RealL1Renorming

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


