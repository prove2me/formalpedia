-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsClutter
-- name    : SeymourMFMC_Binary_IsClutter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T00:49:15.950558+00:00
-- url     : https://prove2.me/theorems/d1263ee8-88a3-4598-96b4-e9a752b62f62
-- title:
--   Clutter (Sperner family): no member contains another
-- statement:
--   A finite collection $\mathbf L$ of finite sets is a **clutter** (also called a Sperner family) if no member is contained in a different member:
--
--   $$
--   A_1 \not\subseteq A_2 \quad \text{for distinct } A_1, A_2 \in \mathbf L .
--   $$
--
--   The two trivial clutters $\emptyset$ (no members) and $\{\emptyset\}$ (the empty set as its only member) are both clutters, as the paper stipulates. Clutters are the objects to which the packing, blocking and minor notions of the paper apply.
--
--   **Formalization Note** Stated as: for all $A, B \in \mathbf L$, $A \subseteq B$ implies $A = B$.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1

import Mathlib

namespace SeymourMFMC.Binary

/-- `IsClutter L`: the finite family `L` of finite sets is a **clutter** (Sperner family,
Seymour 1977, p. 192): no member is included in another, i.e. `A₁ ⊄ A₂` for distinct
`A₁, A₂ ∈ L`. Both `∅` (no members) and `{∅}` (the single member `∅`) are clutters, as the paper
stipulates. -/
def IsClutter {α : Type*} (L : Finset (Finset α)) : Prop :=
  ∀ A ∈ L, ∀ B ∈ L, A ⊆ B → A = B

end SeymourMFMC.Binary


