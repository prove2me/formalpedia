-- Prove2me | Definitions.Def_SeymourMFMC_Binary_contraction
-- name    : SeymourMFMC_Binary_contraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:35:25.597899+00:00
-- url     : https://prove2.me/theorems/7941ab5f-91c8-484d-ac94-a8e4bafa8c5b
-- title:
--   Contraction L/Z: the minimal members of {A − Z : A ∈ L}
-- statement:
--   For a clutter $\mathbf L$ and an arbitrary set $Z$, the **contraction** $\mathbf L / Z$ is the collection of minimal members of
--
--   $$
--   \{ A - Z : A \in \mathbf L \}.
--   $$
--
--   Minimal, not minimal *nonempty*, as the paper stresses (unlike matroid contraction): if some member of $\mathbf L$ is contained in $Z$, then $\mathbf L / Z = \{\emptyset\}$. It is a clutter.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 194, Section 2

import Mathlib

namespace SeymourMFMC.Binary

/-- `contraction L Z` is the contraction `L/Z` (Seymour 1977, p. 194): the collection of
minimal members of `{A − Z : A ∈ L}`, for an arbitrary set `Z`. Minimal, **not** minimal
nonempty: if some member of `L` is included in `Z`, then `L/Z = {∅}`. -/
def contraction {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (Z : Finset α) :
    Finset (Finset α) :=
  (L.image (· \ Z)).filter (fun A => ∀ A' ∈ L.image (· \ Z), A' ⊆ A → A' = A)

end SeymourMFMC.Binary


