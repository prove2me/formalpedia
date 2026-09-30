-- Prove2me | Definitions.Def_SeymourMFMC_Binary_Meets
-- name    : SeymourMFMC_Binary_Meets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T00:58:50.526886+00:00
-- url     : https://prove2.me/theorems/49d099a3-97db-46b9-81bd-9e8c37f984d8
-- title:
--   B meets every member of L (transversal)
-- statement:
--   A set $B$ **meets** a collection $\mathbf L$ if it intersects every member:
--
--   $$
--   A \cap B \neq \emptyset \quad \text{for all } A \in \mathbf L .
--   $$
--
--   Every set meets the empty collection, and no set meets $\{\emptyset\}$. This is the transversal condition used to define the blocker.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1 (definition of b(L))

import Mathlib

namespace SeymourMFMC.Binary

/-- `Meets L B`: the set `B` intersects every member of the family `L` (Seymour 1977, p. 192,
in the definition of the blocker). Every set meets the empty family; no set meets `{∅}`. -/
def Meets {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (B : Finset α) : Prop :=
  ∀ A ∈ L, (A ∩ B).Nonempty

instance {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (B : Finset α) :
    Decidable (Meets L B) := by
  unfold Meets; infer_instance

end SeymourMFMC.Binary


