-- Prove2me | Definitions.Def_TreeMultiflow_IsInternalEdge
-- name    : TreeMultiflow_IsInternalEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:52.919212+00:00
-- url     : https://prove2.me/theorems/6bcde8de-54de-49ff-a05c-f568d3d3787d
-- title:
--   Internal edge of a tree
-- statement:
--   An edge of a tree is **internal** if both of its endpoints are internal vertices (have degree at least two). All other edges are incident to at least one leaf.
--
--   Condition (iii) of Theorem 3.1 bounds the load on internal edges only.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 3, p.6 (An edge is internal if both endpoints are internal vertices)

import Mathlib
import Definitions.Def_TreeMultiflow_IsInternal

namespace TreeMultiflow

/-- **Internal edge.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 3,
p.6: "An edge is internal if both endpoints are internal vertices."

`IsInternalEdge G e` says that `e` is an edge of `G` and both of its endpoints have degree at
least two. -/
def IsInternalEdge {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∀ v ∈ e, IsInternal G v

end TreeMultiflow


