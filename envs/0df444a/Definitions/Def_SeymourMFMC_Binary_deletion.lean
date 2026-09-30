-- Prove2me | Definitions.Def_SeymourMFMC_Binary_deletion
-- name    : SeymourMFMC_Binary_deletion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:26:35.868993+00:00
-- url     : https://prove2.me/theorems/82c536c3-7405-4b78-a0e0-14c8f39849e9
-- title:
--   Deletion L\Z = {A ∈ L : A ∩ Z = ∅}
-- statement:
--   For a clutter $\mathbf L$ and an arbitrary set $Z$, the **deletion** of $Z$ is
--
--   $$
--   \mathbf L \setminus Z = \{ A \in \mathbf L : A \cap Z = \emptyset \}.
--   $$
--
--   It is a clutter. $Z$ need not be a subset of $E(\mathbf L)$. Deletion and contraction generate the minor relation.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 194, Section 2

import Mathlib

namespace SeymourMFMC.Binary

/-- `deletion L Z` is the deletion `L\Z = {A ∈ L : A ∩ Z = ∅}` (Seymour 1977, p. 194), for an
arbitrary set `Z` (not necessarily inside `E(L)`). -/
def deletion {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (Z : Finset α) :
    Finset (Finset α) :=
  L.filter (fun A => Disjoint A Z)

end SeymourMFMC.Binary


