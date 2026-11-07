-- Prove2me | Definitions.Def_VDCyclePack_IsCubic
-- name    : VDCyclePack_IsCubic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:48.066135+00:00
-- url     : https://prove2.me/theorems/4fac8625-da9f-4a78-aa99-6355729c57e2
-- title:
--   Cubic multigraph
-- statement:
--   A multigraph is **cubic** if every vertex has degree three (loops counting two). Lemma 6.2 finds many disjoint cycles in large cubic multigraphs.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib
import Definitions.Def_VDCyclePack_mdeg

namespace VDCyclePack

/-- **Cubic multigraph.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "A multigraph is cubic if every vertex has degree three."

`IsCubic ends` says every vertex has multigraph degree three (loops counted twice). -/
def IsCubic {W E : Type*} [Fintype E] (ends : E → Sym2 W) : Prop :=
  ∀ v : W, mdeg ends v = 3

end VDCyclePack


