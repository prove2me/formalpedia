-- Prove2me | Definitions.Def_QuantumMaxCutEdgeLoads
-- name    : QuantumMaxCutEdgeLoads
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T01:50:22.321195+00:00
-- url     : https://prove2.me/theorems/c2a08b7d-08c5-445e-a496-97f2921722f1
-- title:
--   Vertex loads $\mathrm{load}_x(v)=\sum_{e\ni v}x_e$ of a fractional edge weight
-- statement:
--   **Vertex loads of a fractional edge weight** (the easy half of Edmonds' matching polytope).
--
--   For a graph on $n$ vertices and a weight $x$ on its edges, the *load* of a vertex $v$ is the total
--   $x$-mass of the edges incident to $v$:
--   $$\mathrm{load}_x(v)=\sum_{e\ni v}x_e .$$
--
--   A nonnegative $x$ satisfies Edmonds' *vertex* constraints exactly when $\mathrm{load}_x(v)\le 1$ for every
--   $v$. Together with the odd-set constraints $\sum_{e\subseteq S}x_e\le\frac{|S|-1}{2}$ (odd $S$) these
--   describe the fractional matching polytope, the object in which the matching state of the Lee–Parekh
--   $0.595$ quantum max-cut analysis lives: the positive Pauli-moment excesses $h^{+}$ have loads at most
--   $\tfrac12$, so $2h^{+}$ has loads at most $1$.
--
--   The load is the quantity that the circulation perturbation of
--   `QuantumMaxCutEnergy.matching_balanced_split` preserves, and the quantity appearing in the odd-set
--   counting argument of `QuantumMaxCutEnergy.small_odd_sets`.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965) (matching polytope); Lee-Parekh arXiv:2401.03616 Section 2.3 (the matching state of the level-2 analysis, where loads come from the star monogamy bound).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-!
# Vertex loads of a fractional edge weight

For the matching state of the quantum max-cut analysis, a nonnegative weight `x` on the edges of a
graph is constrained by its *vertex loads*: the total `x`-mass of the edges at each vertex. This file
fixes that quantity as a definition, so that the fractional-matching and odd-set statements of the
campaign can share it.

`x` lies in the (fractional) matching polytope when every vertex load is at most `1` and, for every
odd set `S` of vertices, the `x`-mass of the edges inside `S` is at most `(|S| - 1)/2` — Edmonds'
odd-set description. The load is the easy half of that description; see
`QuantumMaxCutEnergy.matching_balanced_split` for the perturbation that the odd-set half controls.
-/

namespace QuantumMaxCutEnergy

/-- The total `x`-mass of the edges incident to the vertex `v`. -/
def loadAt {n : ℕ} (x : Edge n → ℝ) (v : Fin n) : ℝ :=
  ∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0

end QuantumMaxCutEnergy


