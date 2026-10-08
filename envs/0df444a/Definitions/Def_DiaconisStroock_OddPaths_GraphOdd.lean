-- Prove2me | Definitions.Def_DiaconisStroock_OddPaths_GraphOdd
-- name    : DiaconisStroock_OddPaths_GraphOdd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:56.262162+00:00
-- url     : https://prove2.me/theorems/02ba6a95-33f8-4ad4-ad00-82d3a129c986
-- title:
--   Corollary 2, p. 41 — degree distribution d(x)/2|E|, longest odd path σ_*, and edge load b_*
-- statement:
--   Let $G=(X,E)$ be a finite simple graph and let $\Sigma=(\sigma_x)_{x\in X}$ be a system of closed paths, one for each vertex. Three quantities of the graph case are defined.
--
--   1. The distribution $\pi(x)=\dfrac{d(x)}{2|E|}$, where $d(x)$ is the degree of $x$; the random walk (1.6) on $G$ is reversible with respect to it (p. 39).
--   2. $\sigma_*$, the maximum number of edges in any $\sigma\in\Sigma$.
--   3. The edge load
--   $$
--   b_*=\max_e\,\sharp\{\sigma\in\Sigma:e\in\sigma\},
--   $$
--   the largest number of paths of $\Sigma$ that traverse a single edge $e$.
--
--   These are the combinatorial quantities in which Corollary 2 expresses the bound of Proposition 2 for the random walk on a graph.
--
--   **Formalization Note** As for $\iota$, edges are directed: $b_*$ counts the vertices $x$ whose path $\sigma_x$ traverses the ordered pair $e=(u,v)$, and the maximum is over all ordered pairs. Counting traversals of the unordered edge $\{u,v\}$ instead gives a number at least as large, so the bound of Corollary 2 with this $b_*$ implies the bound with the unordered count. The quantities are natural numbers, cast to reals in Corollary 2.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 39, (1.6) and π(x) = d(x)/2|E|; p. 41, Corollary 2, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_OddPaths_Iota

namespace DiaconisStroock.OddPaths

/-- The stationary distribution `π(x) = d(x) / (2|E|)` of the random walk (1.6) on a graph
(Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1
(1991), §1B, p. 39). -/
noncomputable def degreeDist {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) : ℝ :=
  (G.degree x : ℝ) / (2 * G.edgeFinset.card)

/-- `σ_*` of Corollary 2 (p. 41): the maximum number of edges in any path `σ_x` of `Σ`. -/
def maxOddPathEdges {V : Type*} [Fintype V] (S : V → List V) : ℕ :=
  Finset.univ.sup fun x : V => (DiaconisStroock.Poincare.pathEdges (S x)).length

/-- `b_* = max_e ♯{σ ∈ Σ : e ∈ σ}` of Corollary 2 (p. 41): the maximum, over directed edges `e`,
of the number of points `x` whose path `σ_x` traverses `e`. -/
def oddCongestion {V : Type*} [Fintype V] [DecidableEq V] (S : V → List V) : ℕ :=
  Finset.univ.sup fun e : V × V =>
    (Finset.univ.filter fun x : V => e ∈ DiaconisStroock.Poincare.pathEdges (S x)).card

end DiaconisStroock.OddPaths


