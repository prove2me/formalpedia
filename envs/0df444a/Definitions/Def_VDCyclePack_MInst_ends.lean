-- Prove2me | Definitions.Def_VDCyclePack_MInst_ends
-- name    : VDCyclePack_MInst_ends
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:51.235308+00:00
-- url     : https://prove2.me/theorems/feb5aac6-3870-4054-9bbe-94e21ff43009
-- title:
--   End map of an encoded multigraph
-- statement:
--   The unordered pair of ends of the edge with a given index of an encoded multigraph.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib
import Definitions.Def_VDCyclePack_MInst

namespace VDCyclePack

/-- **End map of an encoded multigraph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10.

`I.ends e` is the unordered pair of ends of the edge with index `e`. -/
def MInst.ends (I : MInst) (e : Fin I.edges.length) : Sym2 (Fin I.n) :=
  s(I.edges[e].1, I.edges[e].2)

end VDCyclePack


