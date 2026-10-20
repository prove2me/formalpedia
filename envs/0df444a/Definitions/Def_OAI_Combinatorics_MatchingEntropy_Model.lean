-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
-- name    : OAI_Combinatorics_MatchingEntropy_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:25:18.943848+00:00
-- url     : https://prove2.me/theorems/599e90f7-eb2f-4fac-bc95-e1befb8db318
-- title:
--   Laws on perfect matchings: the probability simplex, edge marginals and feasible laws
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two endpoints $\ell(e)\neq r(e)$ in $V$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb{R}^E$ for the indicator vector of $M$ ($\mathbf 1_M(e)=1$ if $e\in M$ and $0$ otherwise).
--
--   This module introduces three objects.
--
--   1. *Edge marginals (the mean map).* For a real weight vector $p\in\mathbb{R}^{\mathcal M(G)}$ and an edge $e\in E$,
--   $$
--   \operatorname{mean}_G(p)_e=\sum_{M\in\mathcal M(G)}p_M\,\mathbf 1_M(e)=\sum_{M\in\mathcal M(G):\ e\in M}p_M .
--   $$
--   2. *Probability simplex.* For a finite index set $I$,
--   $$
--   \Delta(I)=\Big\{w\in\mathbb{R}^I:\ w_i\ge0\ \text{for all } i\in I,\ \ \sum_{i\in I}w_i=1\Big\}.
--   $$
--   3. *Feasible laws.* For a target edge vector $y\in\mathbb{R}^E$, the feasible laws are the probability vectors on perfect matchings whose edge marginals equal $y$:
--   $$
--   \mathcal F_G(y)=\big\{p\in\Delta(\mathcal M(G)):\ \operatorname{mean}_G(p)=y\big\}.
--   $$
--
--   When $p\in\Delta(\mathcal M(G))$ is the law of a random perfect matching $\mathbf M$, the number $\operatorname{mean}_G(p)_e$ is the probability that $e\in\mathbf M$. These objects set up the probabilistic description of the perfect matching polytope $\operatorname{conv}\{\mathbf 1_M:\ M\in\mathcal M(G)\}$: a vector $y$ lies in it exactly when $\mathcal F_G(y)$ is nonempty (a fact established separately), and statements about $y$ can then be proved by reasoning about the laws in $\mathcal F_G(y)$ and the matchings they charge.
--
--   **Formalization Note** The definitions are `LooplessGraph.mean`, `probabilitySimplex` and `LooplessGraph.feasibleLaws`. The multigraph structure `LooplessGraph`, the type `Matching` of perfect matchings and `indicator` come from the project's base definitions. The weight vector $p$ in `mean` is an arbitrary real function and need not be a probability vector.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uIndex uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (e : E) : ℝ :=
  ∑ M, p M * G.indicator M e

end LooplessGraph

def probabilitySimplex (Index : Type uIndex) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

namespace LooplessGraph

def feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}

end LooplessGraph

namespace Refined

end Refined

end MatchingEntropyBounds

end

end OAI


