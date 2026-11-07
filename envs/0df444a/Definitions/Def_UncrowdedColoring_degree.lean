-- Prove2me | Definitions.Def_UncrowdedColoring_degree
-- name    : UncrowdedColoring_degree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:22.89219+00:00
-- url     : https://prove2.me/theorems/e715d606-3e0b-4856-be2b-4de50ced30cd
-- title:
--   Degree of a vertex in a hypergraph
-- statement:
--   For a vertex $v$ of a hypergraph $H$, $E(H,v)$ is the set of edges of $H$ containing $v$, and $\deg(H,v)=|E(H,v)|$.
--
--   "Maximum degree at most $\Delta$" in the goal theorem means $\deg(H,v)\le\Delta$ for every vertex $v$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), §3.1, p.13

import Mathlib

namespace UncrowdedColoring

/-- `E(H, v)`: the set of edges of `H` incident to `v` (§3.1, p.13). (Dhawan, Methuku, Vo, manuscript
sha256 2e7243ce…, p.13.) -/
def edgesAt {V : Type*} (H : Hypergraph V) (v : V) : Set (Set V) :=
  {e | e ∈ H.edgeSet ∧ v ∈ e}

/-- `deg(H, v) = |E(H, v)|` (§3.1, p.13).

**Formalization Note.** `Set.ncard` is the true count for a finite hypergraph, the only case the
mission uses (`H.vertexSet.Finite` makes `H.edgeSet` finite). -/
noncomputable def degree {V : Type*} (H : Hypergraph V) (v : V) : ℕ :=
  (edgesAt H v).ncard

end UncrowdedColoring


