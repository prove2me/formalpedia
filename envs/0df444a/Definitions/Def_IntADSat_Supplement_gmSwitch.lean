-- Prove2me | Definitions.Def_IntADSat_Supplement_gmSwitch
-- name    : IntADSat_Supplement_gmSwitch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:45:45.095578+00:00
-- url     : https://prove2.me/theorems/1bdbebdb-6c7e-4891-8fc3-68eed004600b
-- title:
--   Godsil–McKay switch on a vertex set
-- statement:
--   For a graph $G$ and a vertex set $S$, the **Godsil–McKay switch** on $S$ is the graph on the same vertex set obtained as follows: edges with both ends in $S$ and edges with both ends outside $S$ are unchanged; for each vertex $x\notin S$ with exactly two neighbours in $S$, the edges from $x$ to $S$ are replaced by the edges from $x$ to the other vertices of $S$; vertices outside $S$ with any other number of neighbours in $S$ keep their edges to $S$.
--
--   For $|S|=4$, the case of Theorem S6.5, an outside vertex with two neighbours in $S$ is joined instead to the other two vertices of $S$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem S6.5, p.44 (PDF 45)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The **Godsil–McKay switch** of `G` on a vertex set `S` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem S6.5, p.44 (PDF 45)): the graph on
the same vertex set that keeps every edge inside `S` and every edge inside `V ∖ S`, and, for each vertex
`x ∉ S` with exactly two neighbours in `S`, replaces those two edges by the edges from `x` to the other
vertices of `S`; vertices outside `S` with any other number of neighbours in `S` keep their edges to `S`.

**Formalization Note** For `|S| = 4` (the case of Theorem S6.5) "the other vertices" are the other two.
A pair `{x, y}` with `x ∉ S`, `y ∈ S` is an edge of the switch iff it is an edge of `G` exclusive-or `x` has
exactly two neighbours in `S`. Built with `SimpleGraph.fromRel` from a symmetric loopless relation. -/
noncomputable def gmSwitch {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin n) := by
  classical
  exact SimpleGraph.fromRel fun x y =>
    if (x ∈ S ↔ y ∈ S) then G.Adj x y
    else
      let o := if x ∈ S then y else x
      (G.Adj x y ↔ ¬ (S.filter fun s => G.Adj o s).card = 2)

end IntADSat.Supplement


