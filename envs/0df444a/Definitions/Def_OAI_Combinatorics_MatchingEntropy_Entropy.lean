-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
-- name    : OAI_Combinatorics_MatchingEntropy_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:33:31.965991+00:00
-- url     : https://prove2.me/theorems/67240847-44b7-4200-acfb-6417f7941b0a
-- title:
--   Coordinates of points of the perfect matching polytope lie in $[0,1]$
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two endpoints $\ell(e)\neq r(e)$ in $V$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb{R}^E$ for the indicator vector of $M$ ($\mathbf 1_M(e)=1$ if $e\in M$ and $0$ otherwise). The *perfect matching polytope* is $P(G)=\operatorname{conv}\{\mathbf 1_M:\ M\in\mathcal M(G)\}\subseteq\mathbb{R}^E$; it is empty when $G$ has no perfect matching.
--
--   This module proves that every coordinate of a point of the polytope is between $0$ and $1$: for every $y\in P(G)$ and every edge $e\in E$,
--   $$
--   0\le y_e\le1 .
--   $$
--
--   Each point $y\in P(G)$ is the vector of edge-inclusion probabilities of some random perfect matching, so its coordinates are genuine probabilities. The bound is used whenever coordinates of a polytope point are treated as probabilities, for instance to conclude that a coordinate which is not strictly between $0$ and $1$ must equal $0$ or $1$.
--
--   **Formalization Note** The lemma is `LooplessGraph.coordinate_mem_Icc`, stated as $y_e\in[0,1]$ (`Set.Icc 0 1`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Entropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Entropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2

end LooplessGraph

end MatchingEntropyBounds

end

end OAI


