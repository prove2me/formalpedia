-- Prove2me | Definitions.Def_VDCyclePack_familyOf
-- name    : VDCyclePack_familyOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:10:39.834011+00:00
-- url     : https://prove2.me/theorems/19ff69a4-ff0c-4beb-ace2-9a967780fa3c
-- title:
--   The family of cycles described by a list of vertex lists
-- statement:
--   For a list of vertex lists, the set of cycles of the encoded graph represented by at least one of them. It decodes the family $S$ of Theorem 4.2 and the marked packing $H$ in Lemma 4.3 and Proposition 6.3.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 4.2, p.12, and Proposition 6.3, p.18

import Mathlib
import Definitions.Def_VDCyclePack_Represents
import Definitions.Def_VDCyclePack_cycles

namespace VDCyclePack

open Classical in
/-- **The family of cycles described by a list of vertex lists.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 4.2, p.12 ("an explicitly given family of cycles"), Proposition 6.3, p.18
("Given a marked packing H").

`familyOf I ls` is the set of cycles of `I.toGraph` represented by some entry of `ls`. -/
noncomputable def familyOf (I : GraphInst) (ls : List (List ℕ)) : Finset I.toGraph.Subgraph :=
  (cycles I.toGraph).filter fun C => ∃ l ∈ ls, Represents I l C

end VDCyclePack


