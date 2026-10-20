-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
-- name    : OAI_Combinatorics_MatchingEntropy_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:28:19.777226+00:00
-- url     : https://prove2.me/theorems/309d2b8a-6e78-4b20-8c15-14f982e086e8
-- title:
--   The perfect matching polytope as the set of edge marginals of random perfect matchings
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two endpoints $\ell(e)\neq r(e)$ in $V$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb{R}^E$ for the indicator vector of $M$ ($\mathbf 1_M(e)=1$ if $e\in M$ and $0$ otherwise). The *perfect matching polytope* is $P(G)=\operatorname{conv}\{\mathbf 1_M:\ M\in\mathcal M(G)\}\subseteq\mathbb{R}^E$; it is empty when $G$ has no perfect matching.
--
--   For a finite set $I$, $\Delta(I)=\{w\in\mathbb{R}^I:\ w_i\ge0\text{ for all }i,\ \sum_{i\in I}w_i=1\}$ is the probability simplex, and for $p\in\mathbb{R}^{\mathcal M(G)}$ the edge-marginal (mean) vector is $\operatorname{mean}_G(p)_e=\sum_{M\in\mathcal M(G)}p_M\,\mathbf 1_M(e)$. For $y\in\mathbb{R}^E$ let $\mathcal F_G(y)=\{p\in\Delta(\mathcal M(G)):\ \operatorname{mean}_G(p)=y\}$ be the set of feasible laws.
--
--   This module proves the following basic facts.
--
--   1. *Indicator bounds.* $0\le\mathbf 1_M(e)\le1$ for every $M\in\mathcal M(G)$ and $e\in E$.
--   2. *Linearity.* The mean map $p\mapsto\operatorname{mean}_G(p)$ is a linear map $\mathbb{R}^{\mathcal M(G)}\to\mathbb{R}^E$.
--   3. *Point masses.* $\operatorname{mean}_G(\delta_M)=\mathbf 1_M$, where $\delta_M$ is the unit vector at $M$.
--   4. *Means of laws lie in the polytope.* If $p\in\Delta(\mathcal M(G))$, then $\operatorname{mean}_G(p)\in P(G)$.
--   5. *Characterization of the polytope.* For every $y\in\mathbb{R}^E$,
--   $$
--   y\in P(G)\iff\mathcal F_G(y)\neq\varnothing,
--   $$
--   that is, $y$ lies in the perfect matching polytope if and only if $y=\operatorname{mean}_G(p)$ for some probability vector $p$ on $\mathcal M(G)$.
--
--   The characterization lets one pass freely between a point of the polytope and a random perfect matching whose edge-inclusion probabilities are the coordinates of that point. Arguments about points of $P(G)$ can then pick such a law and reason about the perfect matchings it charges.
--
--   **Formalization Note** The polytope is `G.polytope`, the convex hull of the range of `G.indicator`. The module provides the linear map `meanLinear` (whose underlying function is `mean`), the simp lemmas `indicator_nonneg`, `indicator_le_one` and `mean_single`, and the results `mean_mem_polytope` and `mem_polytope_iff`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_nonneg (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    0 ≤ G.indicator M e := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_le_one (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    G.indicator M e ≤ 1 := by
  simp only [indicator]
  split <;> norm_num

def meanLinear (G : LooplessGraph V E) : (G.Matching → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := G.mean
  map_add' p q := by
    ext e
    simp [mean, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext e
    simp [mean, mul_assoc, Finset.mul_sum]

omit [Fintype V] [DecidableEq V] in
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]

omit [Fintype V] [DecidableEq V] in

theorem mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  classical
  constructor
  · intro hy
    have hc : Convex ℝ (G.mean '' probabilitySimplex G.Matching) :=
      (convex_probabilitySimplex G.Matching).linear_image G.meanLinear
    have hs : Set.range G.indicator ⊆ G.mean '' probabilitySimplex G.Matching := by
      rintro _ ⟨M, rfl⟩
      exact ⟨Pi.single M 1, single_mem_probabilitySimplex M, G.mean_single M⟩
    obtain ⟨p, hp, rfl⟩ := convexHull_min hs hc hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact G.mean_mem_polytope hp

end MatchingEntropyBounds.LooplessGraph

end

end OAI


