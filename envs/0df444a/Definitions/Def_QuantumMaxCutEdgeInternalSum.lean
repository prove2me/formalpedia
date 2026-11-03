-- Prove2me | Definitions.Def_QuantumMaxCutEdgeInternalSum
-- name    : QuantumMaxCutEdgeInternalSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T04:54:41.471541+00:00
-- url     : https://prove2.me/theorems/01a56a64-3b01-400e-9807-b5c4fe1769e4
-- title:
--   Internal edge mass $\mathrm{internalSum}\,x\,S=\sum_{\{a,b\}\subseteq S}x_{\{a,b\}}$ of a vertex set
-- statement:
--   **Internal edge mass of a vertex set** (the left-hand side of Edmonds' odd-set constraints).
--
--   For a weight $x$ on the edges of a graph on $n$ vertices and a set $S$ of vertices,
--   $$\mathrm{internalSum}\,x\,S=\sum_{\{a,b\}\subseteq S}x_{\{a,b\}},$$
--   the total $x$-mass of the edges with both endpoints in $S$.
--
--   **Role.** Edmonds' odd-set constraint for $S$ is $\mathrm{internalSum}\,x\,S\le(|S|-1)/2$, and this is the
--   quantity that the uncrossing argument manipulates: for any two vertex sets $A,B$ one has
--   $$\mathrm{internalSum}\,x\,A+\mathrm{internalSum}\,x\,B\;\le\;\mathrm{internalSum}\,x\,(A\cup B)+\mathrm{internalSum}\,x\,(A\cap B),$$
--   because the edges joining $A\setminus B$ to $B\setminus A$ are counted on the right and not on the left. That
--   inequality, with the odd-set constraints, lets two *crossing* tight odd sets be replaced by their intersection
--   and union — the step that makes the family of tight odd sets laminar, which is the route to Edmonds' exactness
--   of the matching polytope beyond the bipartite case.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965) (odd-set constraints); Schrijver, Combinatorial Optimization, Ch. 25 (uncrossing of tight odd sets).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-!
# Internal edge mass of a vertex set

For a nonnegative weight `x` on the edges of a graph, `internalSum x S` is the total `x`-mass of the edges
with both endpoints in the vertex set `S`. This is the quantity in Edmonds' odd-set constraints
`internalSum x S ≤ (|S| - 1)/2`, and the quantity that the uncrossing argument of the matching-polytope
exactness theorem manipulates: for any two vertex sets `A`, `B`,
`internalSum x A + internalSum x B ≤ internalSum x (A ∪ B) + internalSum x (A ∩ B)`
(`QuantumMaxCutEnergy.internalSum_add_le`), with equality of the difference carried by the edges crossing
between `A \ B` and `B \ A`.
-/

namespace QuantumMaxCutEnergy

/-- The `x`-mass of the edges with both endpoints in `S`. -/
def internalSum {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S), x e

end QuantumMaxCutEnergy


