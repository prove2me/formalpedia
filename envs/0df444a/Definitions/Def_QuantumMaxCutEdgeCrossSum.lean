-- Prove2me | Definitions.Def_QuantumMaxCutEdgeCrossSum
-- name    : QuantumMaxCutEdgeCrossSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:19:13.557044+00:00
-- url     : https://prove2.me/theorems/0e10434c-b3a4-4f96-9d05-d3a83464b2e4
-- title:
--   Edge mass $\mathrm{crossSum}\,x\,S$ leaving a vertex set $S$
-- statement:
--   **Edge mass leaving a vertex set.**
--
--   For a weight $x$ on the edges of a graph on $n$ vertices and a set $S$ of vertices,
--   $$\mathrm{crossSum}\,x\,S=\sum_{\substack{\{a,b\}\\ |\{a,b\}\cap S|=1}}x_{\{a,b\}},$$
--   the total $x$-mass of the edges with exactly one endpoint in $S$.
--
--   **Role.** Together with the internal mass this gives the double-counting identity
--   $$2\,\mathrm{internalSum}\,x\,S+\mathrm{crossSum}\,x\,S=\sum_{v\in S}\mathrm{load}_x(v),$$
--   because an edge inside $S$ contributes twice to the load mass on $S$, an edge leaving $S$ once, and an edge
--   outside not at all. For a *tight* odd set, $\mathrm{internalSum}\,x\,S=(|S|-1)/2$, this specializes to
--   $$\mathrm{crossSum}\,x\,S=1-\sum_{v\in S}\bigl(1-\mathrm{load}_x(v)\bigr)\;\le\;1:$$
--   a tight odd set sends at most one unit of mass outside itself. That is the structural fact behind the odd-cycle
--   case of Edmonds' exactness: on an odd cycle whose vertices are all saturated it forces the alternating values on
--   the cycle to be $0$ and $1$, so the point is integral.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25 (the cut/internal double counting for tight odd sets).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-!
# Edge mass leaving a vertex set

`crossSum x S` is the total `x`-mass of the edges with exactly one endpoint in `S`. Together with
`QuantumMaxCutEdgeInternalSum` it gives the double-counting identity
`2 * internalSum x S + crossSum x S = ∑ v ∈ S, loadAt x v`
(`QuantumMaxCutEnergy.sum_load_eq_two_mul_internal_add_cross`), whose consequence for a tight odd set
`internalSum x S = (|S|-1)/2` is `crossSum x S = 1 - ∑_{v ∈ S} (1 - loadAt x v) ≤ 1`: a tight odd set
sends at most one unit of mass outside itself. That is the structural fact behind the odd-cycle case of
Edmonds' exactness — on a saturated odd cycle it forces the alternating `0/1` pattern.
-/

namespace QuantumMaxCutEnergy

/-- The `x`-mass of the edges with exactly one endpoint in `S`. -/
def crossSum {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edge n =>
    (e.val.1 ∈ S ∧ e.val.2 ∉ S) ∨ (e.val.1 ∉ S ∧ e.val.2 ∈ S)), x e

end QuantumMaxCutEnergy


