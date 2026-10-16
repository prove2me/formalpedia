-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T11:51:00.044378+00:00
-- url     : https://prove2.me/theorems/dc034fbe-3e2f-4c74-ad6b-ff6609a1f692
-- title:
--   Isometric embedding $x\mapsto\delta_x$ into the Lipschitz-free space, completeness and closed-span induction
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$. Write $\mathrm{Lip}_0(M)$ for the space of real Lipschitz functions on $M$ vanishing at $o$, normed by the best Lipschitz constant, $e_x(f)=f(x)$ for the evaluation functional at $x\in M$, and $\mathcal{F}(M)$ for the Lipschitz-free space, the closed linear span of the $e_x$ in the dual $\mathrm{Lip}_0(M)^{*}$ with the operator norm; $\delta_x$ is $e_x$ viewed as an element of $\mathcal{F}(M)$. This file establishes the basic metric and topological properties of $\mathcal{F}(M)$.
--
--   1. **Distance test functions.** For $y\in M$ the function $\phi_y(z)=d(z,y)-d(o,y)$ belongs to $\mathrm{Lip}_0(M)$ and $\|\phi_y\|\le 1$.
--
--   2. **Isometric embedding.** For all $x,y\in M$,
--   $$\|\delta_x-\delta_y\|_{\mathcal{F}(M)}=\|e_x-e_y\|_{\mathrm{Lip}_0(M)^{*}}=d(x,y),\qquad \|\delta_x\|=\|e_x\|=d(x,o),$$
--   and $\delta_o=0$. Thus $x\mapsto\delta_x$ is an isometric embedding of $M$ into $\mathcal{F}(M)$ sending the base point to $0$.
--
--   3. **Completeness.** $\mathcal{F}(M)$ is complete, i.e. a real Banach space.
--
--   4. **Closed-span induction.** Let $P$ be a property of elements of $\mathcal{F}(M)$ such that the set $\{u\in\mathcal{F}(M) : P(u)\}$ is closed, $P(0)$ holds, $P(u)$ and $P(v)$ imply $P(u+v)$, $P(u)$ implies $P(c\,u)$ for every $c\in\mathbb{R}$, and $P(\delta_x)$ holds for every $x\in M$. Then $P(u)$ holds for every $u\in\mathcal{F}(M)$.
--
--   Item 2 is the fundamental isometry of Lipschitz-free spaces, and item 4 is the tool for proving identities between bounded linear operators on $\mathcal{F}(M)$: two such operators agree as soon as they agree on all $\delta_x$, because equality is a closed linear condition.
--
--   **Formalization Note** `distanceTest o y` is $\phi_y$ with `distanceTest_norm_le`; `evaluation_sub_norm` and `evaluation_norm` are the isometry statements in the dual, and `delta_sub_norm`, `delta_norm`, `delta_base` restate them in `FreeSpace o`. Completeness is registered as a `CompleteSpace` instance, and item 4 is `freeSpace_induction`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Evaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Evaluation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming

namespace OAI

/-!
# Evaluation isometries, completeness, and closed-span induction
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section EvaluationGeometry

variable {M : Type*} [MetricSpace M]

def distanceTest (o y : M) : Lip0 o :=
  Lip0.ofBound o (fun z => dist z y - dist o y) (by simp) 1 (by norm_num)
    (fun x z => by simpa using abs_dist_sub_le x z y)

@[simp] theorem distanceTest_apply (o y z : M) :
    distanceTest o y z = dist z y - dist o y := rfl

theorem distanceTest_norm_le (o y : M) : ‖distanceTest o y‖ ≤ 1 := by
  apply (Lip0.norm_le_iff _ (by norm_num)).mpr
  intro x z
  simpa using abs_dist_sub_le x z y

theorem evaluation_sub_norm (o x y : M) : ‖evaluation o x - evaluation o y‖ = dist x y := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ dist_nonneg
    intro f
    change ‖f x - f y‖ ≤ dist x y * ‖f‖
    rw [Real.norm_eq_abs, mul_comm]
    exact Lip0.sub_le f x y
  · have h := (evaluation o x - evaluation o y).le_opNorm_of_le (distanceTest_norm_le o y)
    simpa [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h

@[simp] theorem evaluation_norm (o x : M) : ‖evaluation o x‖ = dist x o := by
  simpa using evaluation_sub_norm o x o

@[simp] theorem delta_base (o : M) : delta o o = 0 := by
  apply Subtype.ext
  exact evaluation_base o

@[simp] theorem delta_sub_norm (o x y : M) : ‖delta o x - delta o y‖ = dist x y :=
  evaluation_sub_norm o x y

@[simp] theorem delta_norm (o x : M) : ‖delta o x‖ = dist x o := evaluation_norm o x

instance (o : M) : CompleteSpace (FreeSpace o) :=
  (Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (evaluation o)))).completeSpace_coe

theorem freeSpace_induction {o : M} (P : FreeSpace o → Prop)
    (hclosed : IsClosed {u | P u}) (hzero : P 0)
    (hadd : ∀ u v, P u → P v → P (u + v))
    (hsmul : ∀ (c : ℝ) u, P u → P (c • u)) (heval : ∀ x, P (delta o x)) :
    ∀ u, P u := by
  let S : Submodule ℝ (FreeSpace o) :=
    { carrier := {u | P u}, zero_mem' := hzero, add_mem' := fun {u v} => hadd u v, smul_mem' := hsmul }
  let incl : FreeSpace o →L[ℝ] (Lip0 o →L[ℝ] ℝ) :=
    (freeSubmodule o).subtypeL
  have hinc : IsClosedMap incl :=
    (Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range (evaluation o)))).isClosedEmbedding_subtypeVal.isClosedMap
  have himage : IsClosed (S.map incl.toLinearMap : Set (Lip0 o →L[ℝ] ℝ)) :=
    by
      change IsClosed (incl '' {u | P u})
      exact hinc _ hclosed
  have hspan : Submodule.span ℝ (Set.range (evaluation o)) ≤ S.map incl.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨delta o x, heval x, rfl⟩
  have hAll : freeSubmodule o ≤ S.map incl.toLinearMap :=
    Submodule.topologicalClosure_minimal _ hspan himage
  intro u
  obtain ⟨v, hv, hvu⟩ := hAll u.property
  have hvu' : v = u := Subtype.ext hvu
  change P v at hv
  simpa [hvu'] using hv

end EvaluationGeometry

end DiscreteFree

end

end OAI


