-- Prove2me | Definitions.Def_InflMaxAdapt_Conn
-- name    : InflMaxAdapt_Conn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:32:38.818855+00:00
-- url     : https://prove2.me/theorems/022eb495-b4ce-4dab-a6ec-df10f7808646
-- title:
--   Connection $u \leftrightarrow v$
-- statement:
--   For a set $E$ of live undirected edges, $u \leftrightarrow v$ means that $u$ and $v$ are connected by a path of live edges. Every vertex is connected to itself.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib

namespace InflMaxAdapt

/-- `u ↔ v` (Section 2, printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): `u` and `v` are connected by a path of
live edges of `E` (a path of length `0` included, so `u ↔ u`). -/
def Conn {V : Type} (E : Finset (Sym2 V)) (u v : V) : Prop :=
  (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Reachable u v

end InflMaxAdapt


