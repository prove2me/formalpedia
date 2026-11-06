-- Prove2me | Definitions.Def_TreeMultiflow_IsLeaf
-- name    : TreeMultiflow_IsLeaf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:06.140248+00:00
-- url     : https://prove2.me/theorems/70e0e91d-a346-4c4f-aa1c-4bdf6de58473
-- title:
--   Leaf of a tree
-- statement:
--   A vertex $v$ of a tree is a **leaf** if it has degree one, i.e. exactly one neighbour.
--
--   The paths of Theorems 2.2, 3.1 and 5.2 join two distinct leaves, and bins are formed at leaves.
--
--   **Formalization Note** The degree is the cardinality of the neighbour set; it is used only for finite trees.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 3, p.6 (leaves; A vertex is internal if it has degree at least two)

import Mathlib

namespace TreeMultiflow

/-- **Leaf of a tree.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 3,
p.6: "A vertex is internal if it has degree at least two. … All other edges are incident to at
least one leaf." A leaf is a vertex of degree one.

`IsLeaf G v` says that `v` has exactly one neighbour in `G`.

**Formalization Note.** The degree is `(G.neighborSet v).ncard`, which needs no `Fintype`
instance; it is used only for finite trees (`[Fintype V]`), where it is the usual degree. -/
def IsLeaf {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  (G.neighborSet v).ncard = 1

end TreeMultiflow


