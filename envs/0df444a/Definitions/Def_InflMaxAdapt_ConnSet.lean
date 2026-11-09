-- Prove2me | Definitions.Def_InflMaxAdapt_ConnSet
-- name    : InflMaxAdapt_ConnSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:20.991063+00:00
-- url     : https://prove2.me/theorems/87833da9-4782-4bb1-99f5-855060bfb388
-- title:
--   Connection to a set $u \leftrightarrow S$
-- statement:
--   For a set $E$ of live undirected edges, a vertex $u$ and a set $S \subseteq V$, $u \leftrightarrow S$ means that $u$ is connected by a path of live edges to some vertex of $S$; equivalently $u \in C(S)$. It is false when $S = \emptyset$. The negation is written $u \not\leftrightarrow S$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_Conn

namespace InflMaxAdapt

/-- `u ↔ S` (Section 2, printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): `u` is connected by a path of live
edges to some vertex of `S` (equivalently `u ∈ C(S)`); false for `S = ∅`. -/
def ConnSet {V : Type} (E : Finset (Sym2 V)) (u : V) (S : Finset V) : Prop :=
  ∃ s ∈ S, Conn E u s

end InflMaxAdapt


