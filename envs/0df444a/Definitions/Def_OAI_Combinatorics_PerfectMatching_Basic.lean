-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
-- name    : OAI_Combinatorics_PerfectMatching_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:44:15.190073+00:00
-- url     : https://prove2.me/theorems/17dfe88d-49ba-4caa-982d-3e86d7213d9e
-- title:
--   Mean map from weights on perfect matchings to edge marginals
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; $\mathcal M(G)$ denotes the finite set of perfect matchings and $\mathbf 1_M\in\{0,1\}^E$ the indicator vector of $M$.
--
--   This module adds the following basic facts and one linear map.
--
--   1. *Indicator bounds.* For every perfect matching $M$ and edge $e$, $0\le\mathbf 1_M(e)\le1$.
--   2. *The mean map as a linear map.* The mean of a real weight vector $p\in\mathbb{R}^{\mathcal M(G)}$ is the edge vector
--   $$
--   \operatorname{mean}_G(p)_e=\sum_{M\in\mathcal M(G)}p_M\,\mathbf 1_M(e)\qquad(e\in E),
--   $$
--   and $\operatorname{mean}_G:\mathbb{R}^{\mathcal M(G)}\to\mathbb{R}^E$ is linear. Here $p$ is an arbitrary real vector and need not be a probability vector.
--   3. *Means of point masses.* If $\delta_M$ is the unit vector at $M$ (the point mass on $M$), then $\operatorname{mean}_G(\delta_M)=\mathbf 1_M$.
--
--   The mean map sends the probability simplex on $\mathcal M(G)$ to the edge marginals of random perfect matchings. Linearity and the point-mass identity are what identify its image with the perfect matching polytope $\operatorname{conv}\{\mathbf 1_M\}$, and they allow laws to be mixed and perturbed while their means are tracked.
--
--   **Formalization Note** The loopless multigraph, perfect matchings, indicators, the function `mean`, the polytope and the feasible laws are introduced in the project's base definitions. This module packages `mean` as the linear map `meanLinear`, provides the decidability instance `incidentDecidable` for incidence, and proves the simp lemmas `indicator_nonneg`, `indicator_le_one` and `mean_single`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model

namespace OAI

/-!
Finite loopless multigraphs, perfect matching indicators, and their convex hull.
The edge type distinguishes parallel edges. Feasible laws are probability vectors
on perfect matchings with a prescribed mean.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

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
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]

end LooplessGraph

end MatchingEntropy

end

end OAI


