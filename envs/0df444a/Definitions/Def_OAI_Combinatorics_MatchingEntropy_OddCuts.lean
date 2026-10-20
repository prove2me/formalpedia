-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
-- name    : OAI_Combinatorics_MatchingEntropy_OddCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:29:35.043606+00:00
-- url     : https://prove2.me/theorems/c77ebd13-8e3c-4dc6-aee1-d80755858334
-- title:
--   Degree and odd-cut constraints are valid for the perfect matching polytope
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two endpoints $\ell(e)\neq r(e)$ in $V$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb{R}^E$ for the indicator vector of $M$ ($\mathbf 1_M(e)=1$ if $e\in M$ and $0$ otherwise). The *perfect matching polytope* is $P(G)=\operatorname{conv}\{\mathbf 1_M:\ M\in\mathcal M(G)\}\subseteq\mathbb{R}^E$; it is empty when $G$ has no perfect matching.
--
--   For a finite set $S\subseteq V$, an edge $e$ *crosses* $S$ if exactly one of its endpoints lies in $S$, and the *cut* $\delta(S)\subseteq E$ is the set of crossing edges. For $x\in\mathbb{R}^E$ the $x$-degree of a vertex and the $x$-mass of a cut are
--   $$
--   \deg_x(v)=\sum_{e\in E:\ v\in\{\ell(e),r(e)\}}x_e,\qquad x\big(\delta(S)\big)=\sum_{e\in\delta(S)}x_e .
--   $$
--
--   1. *The degree and odd-cut constraint system.*
--   $$
--   Q(G)=\Big\{x\in\mathbb{R}^E:\ x_e\ge0\ \ \forall e\in E,\quad \deg_x(v)=1\ \ \forall v\in V,\quad x\big(\delta(S)\big)\ge1\ \ \forall S\subseteq V\text{ finite with }|S|\text{ odd}\Big\}.
--   $$
--   2. *Cuts.* $e\in\delta(S)$ if and only if $e$ crosses $S$; when $V$ is finite, an edge crosses $V\setminus S$ if and only if it crosses $S$, so $\delta(V\setminus S)=\delta(S)$.
--   3. *Linearity.* For all real $a,b$ and $x,y\in\mathbb{R}^E$: $\deg_{ax+by}(v)=a\deg_x(v)+b\deg_y(v)$ and $(ax+by)(\delta(S))=a\,x(\delta(S))+b\,y(\delta(S))$.
--   4. *Counting with a perfect matching.* For every edge $e$, the number of vertices of $S$ incident to $e$ is $[\ell(e)\in S]+[r(e)\in S]$, where $[\,\text{condition}\,]$ equals $1$ if the condition holds and $0$ otherwise. For every $M\in\mathcal M(G)$ one has $\deg_{\mathbf 1_M}(v)=1$ for all $v$, and
--   $$
--   \sum_{e\in M}\big([\ell(e)\in S]+[r(e)\in S]\big)=|S| ;
--   $$
--   consequently, if $|S|$ is odd, some edge of $M$ crosses $S$.
--   5. *Validity.* $Q(G)$ is convex, every indicator vector $\mathbf 1_M$ lies in $Q(G)$, and therefore
--   $$
--   P(G)\subseteq Q(G).
--   $$
--
--   This is the easy inclusion in Edmonds' description of the perfect matching polytope by nonnegativity, degree and odd-cut constraints: every point of $P(G)$ has all vertex degrees equal to $1$ and puts mass at least $1$ on every odd cut. The odd sets include the singletons and, when $|V|$ is odd, the whole of $V$, whose cut is empty; in that case $Q(G)$ is empty, consistent with the absence of perfect matchings.
--
--   **Formalization Note** The constraint system is `constraintPolytope`, with $S$ ranging over `Finset V`; crossing, `cut`, `degree` and `cutMass` come from the project's base definitions. The listed facts are `mem_cut`, `crosses_compl`, `cut_compl`, `degree_linear`, `cutMass_linear`, `incidence_sum` (stated with natural-number counts), `degree_indicator`, `matching_incidence_count`, `matching_crosses_odd`, `convex_constraintPolytope`, `indicator_mem_constraintPolytope` and `polytope_subset_constraintPolytope`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/OddCuts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/OddCuts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def constraintPolytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v = 1) ∧
    (∀ S : Finset V, Odd S.card → 1 ≤ G.cutMass x S)}

omit [Fintype V] [DecidableEq E] in
@[simp] theorem mem_cut (G : LooplessGraph V E) (S : Finset V) (e : E) :
    e ∈ G.cut S ↔ G.Crosses S e := by simp [cut]

omit [Fintype E] [DecidableEq E] in
theorem crosses_compl (G : LooplessGraph V E) (S : Finset V) (e : E) :
    G.Crosses Sᶜ e ↔ G.Crosses S e := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

omit [DecidableEq E] in
@[simp] theorem cut_compl (G : LooplessGraph V E) (S : Finset V) :
    G.cut Sᶜ = G.cut S := by ext; simp [crosses_compl]

omit [Fintype V] in
theorem degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
  rw [degree, Finset.sum_eq_single e]
  · simp [hev, indicator, he]
  · intro e' _ hne
    by_cases hv : G.Incident v e'
    · have hh : e' ∉ M.val := by
        intro hm
        exact hne (huniq e' ⟨hm, hv⟩)
      simp [hv, indicator, hh]
    · simp [hv]
  · simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidence_sum (G : LooplessGraph V E) (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0) =
      (if G.left e ∈ S then 1 else 0) + (if G.right e ∈ S then 1 else 0) := by
  have hv : ∀ v, (if G.Incident v e then (1:ℕ) else 0) =
      (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incidence_count (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) :
    (∑ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0))) = S.card := by
  have hsum : ∀ v, (∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0) = 1 := by
    intro v
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro e' he' hh
      have hv : ¬G.Incident v e' := fun hv => hh (hu e' ⟨he', hv⟩)
      simp [hv]
    · simp [he]
  calc
    _ = ∑ e ∈ M.val, ∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0 := by
      simp_rw [incidence_sum]
    _ = ∑ v ∈ S, ∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0 := Finset.sum_comm
    _ = S.card := by simp_rw [hsum]; simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_crosses_odd (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) (hS : Odd S.card) : ∃ e ∈ M.val, G.Crosses S e := by
  by_contra h
  push Not at h
  have heq : ∀ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) = 2*(if G.left e ∈ S then 1 else 0) := by
    intro e he
    have hc := h e he
    simp only [Crosses] at hc
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
      simp_all
  have hh := G.matching_incidence_count M S
  have heqsum := Finset.sum_congr rfl heq
  rw [heqsum, ← Finset.mul_sum] at hh
  obtain ⟨k, hk⟩ := hS
  omega

omit [Fintype V] [DecidableEq E] in
theorem degree_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (v : V) :
    G.degree (a • x+b • y) v = a*G.degree x v+b*G.degree y v := by
  have he : ∀ e, (if G.Incident v e then (a • x+b • y) e else 0) =
      a*(if G.Incident v e then x e else 0)+b*(if G.Incident v e then y e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h]
  simp only [degree, he, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem cutMass_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    G.cutMass (a • x+b • y) S = a*G.cutMass x S+b*G.cutMass y S := by
  simp [cutMass, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem convex_constraintPolytope (G : LooplessGraph V E) :
    Convex ℝ G.constraintPolytope := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_, ?_⟩
  · intro v
    rw [degree_linear, hx.2.1, hy.2.1, mul_one, mul_one, hab]
  · intro S hS
    rw [cutMass_linear]
    calc
      1 = a*1+b*1 := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 S hS) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 S hS) hb)

omit [Fintype V] in
theorem indicator_mem_constraintPolytope (G : LooplessGraph V E) (M : G.Matching) :
    G.indicator M ∈ G.constraintPolytope := by
  refine ⟨?_, G.degree_indicator M, ?_⟩
  · intro e; simp [indicator]; split <;> norm_num
  · intro S hS
    obtain ⟨e, he, hc⟩ := G.matching_crosses_odd M S hS
    have h := Finset.single_le_sum (f := G.indicator M)
      (s := G.cut S) (a := e) (by intro e' _; simp [indicator]; split <;> norm_num)
      ((G.mem_cut S e).mpr hc)
    simpa only [cutMass, indicator, he, ite_true] using h

omit [Fintype V] in
theorem polytope_subset_constraintPolytope (G : LooplessGraph V E) :
    G.polytope ⊆ G.constraintPolytope := by
  apply convexHull_min
  · rintro x ⟨M, rfl⟩
    exact G.indicator_mem_constraintPolytope M
  · exact G.convex_constraintPolytope

end MatchingEntropyBounds.LooplessGraph

end

end OAI


