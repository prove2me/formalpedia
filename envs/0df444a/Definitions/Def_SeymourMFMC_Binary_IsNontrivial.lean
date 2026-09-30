-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsNontrivial
-- name    : SeymourMFMC_Binary_IsNontrivial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:39:19.496562+00:00
-- url     : https://prove2.me/theorems/f0785304-debe-431c-a35e-84c3480c7751
-- title:
--   Nontrivial clutter: L ≠ ∅ and L ≠ {∅}
-- statement:
--   A clutter is **nontrivial** if it is neither of the two trivial clutters $\emptyset$ and $\{\emptyset\}$:
--
--   $$
--   \mathbf L \neq \emptyset \quad\text{and}\quad \mathbf L \neq \{\emptyset\}.
--   $$
--
--   **Formalization Note** The paper does not define "nontrivial". It calls $\{\emptyset\}$ and $\emptyset$ the trivial clutters (p. 192), and the proof of (4.6) uses nontriviality exactly as "$B \neq \emptyset$", i.e. $\mathbf L \neq \emptyset$, together with $\mathbf L \neq \{\emptyset\}$ so that $\tau$ is defined.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1 (trivial clutters); used in (4.6), p. 208

import Mathlib

namespace SeymourMFMC.Binary

/-- `IsNontrivial L`: `L` is neither of the two trivial clutters `∅` and `{∅}` (Seymour 1977,
p. 192, where these are called the trivial clutters; "nontrivial" is used in (4.6)–(4.7),
p. 208). -/
def IsNontrivial {α : Type*} (L : Finset (Finset α)) : Prop :=
  L ≠ ∅ ∧ L ≠ {∅}

end SeymourMFMC.Binary


