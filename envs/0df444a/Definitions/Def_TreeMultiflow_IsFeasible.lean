-- Prove2me | Definitions.Def_TreeMultiflow_IsFeasible
-- name    : TreeMultiflow_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:38.585662+00:00
-- url     : https://prove2.me/theorems/533cc279-9e69-4674-a55b-576cbb6f23c3
-- title:
--   Feasible set of requests
-- statement:
--   A set $S$ of requests is **feasible** for the capacities $u_e$ if
--   $$
--   \bigl|\{f\in S : e\in\mathrm{Path}(f)\}\bigr|\le u_e\qquad\text{for every edge } e
--   $$
--   of the tree.
--
--   Theorem 1.2 asks for a feasible set of large weight; the colour classes of Theorems 2.2 and 5.2 are required to be feasible.
--
--   **Formalization Note** Capacities are a function on unordered vertex pairs; only its values on edges of the tree are constrained.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (A subset S is feasible if …)

import Mathlib
import Definitions.Def_TreeMultiflow_load

namespace TreeMultiflow

/-- **Feasible set of requests.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2: "A subset S is feasible if |{f ∈ S : e ∈ Path(f)}| ≤ uₑ for every edge e."

`IsFeasible G u src dst S` says that the load of `S` on every edge `e` of the tree is at most the
capacity `u e`.

**Formalization Note.** Capacities are a function `u : Sym2 V → ℕ`; only its values on the edges
`G.edgeSet` are constrained, the others are irrelevant. -/
def IsFeasible {V F : Type*} (G : SimpleGraph V) (u : Sym2 V → ℕ) (src dst : F → V)
    (S : Finset F) : Prop :=
  ∀ e ∈ G.edgeSet, load G src dst S e ≤ u e

end TreeMultiflow


