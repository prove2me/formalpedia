-- Prove2me | Definitions.Def_DiaconisStroock_Poincare_GraphPaths
-- name    : DiaconisStroock_Poincare_GraphPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:40.711586+00:00
-- url     : https://prove2.me/theorems/12a3e28a-d27f-47a8-9d5b-aa20f412d7fe
-- title:
--   Corollary 1, p. 39 — greatest path length and directed-edge path count
-- statement:
--   For a collection $\Gamma$ of paths between distinct ordered endpoints in a finite graph, let $\gamma_*$ be the greatest number of edges in one path, and let $b$ be the greatest number of paths that traverse one directed edge:
--
--   $$
--   \gamma_* = \max_{x\ne y}|\gamma_{xy}|,\qquad
--   b=\max_e\#\{(x,y):x\ne y,\ e\in\gamma_{xy}\}.
--   $$
--
--   These quantities appear in the graph specialization of Proposition 1.
--
--   **Formalization Note** The maxima are implemented as finite supremums. Pairs with equal endpoints contribute zero, and a non-edge is traversed by no valid path.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 39, Corollary 1, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Kappa

namespace DiaconisStroock.Poincare

/-- The greatest number of edges among paths for distinct ordered endpoints, γ_* of Corollary 1. -/
def maxPathEdges {V : Type*} [Fintype V] [DecidableEq V] (Γ : V → V → List V) : ℕ :=
  Finset.univ.sup fun xy : V × V =>
    if xy.1 ≠ xy.2 then (pathEdges (Γ xy.1 xy.2)).length else 0

/-- The greatest number of ordered-pair paths crossing one directed edge, b of Corollary 1. -/
def edgeCongestion {V : Type*} [Fintype V] [DecidableEq V] (Γ : V → V → List V) : ℕ :=
  Finset.univ.sup fun e : V × V =>
    (Finset.univ.filter fun xy : V × V =>
      xy.1 ≠ xy.2 ∧ e ∈ pathEdges (Γ xy.1 xy.2)).card

end DiaconisStroock.Poincare


