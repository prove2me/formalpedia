-- Prove2me | Definitions.Def_TreeMultiflow_IsInternal
-- name    : TreeMultiflow_IsInternal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:09.338966+00:00
-- url     : https://prove2.me/theorems/582a8a69-0fcb-43ed-bfbe-cdd7765e5832
-- title:
--   Internal vertex of a tree
-- statement:
--   A vertex is **internal** if it has degree at least two.
--
--   **Formalization Note** The degree is the cardinality of the neighbour set; it is used only for finite trees.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 3, p.6 (A vertex is internal if it has degree at least two)

import Mathlib

namespace TreeMultiflow

/-- **Internal vertex.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 3,
p.6: "A vertex is internal if it has degree at least two."

**Formalization Note.** The degree is `(G.neighborSet v).ncard`; it is used only for finite trees
(`[Fintype V]`), where it is the usual degree. -/
def IsInternal {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  2 ≤ (G.neighborSet v).ncard

end TreeMultiflow


