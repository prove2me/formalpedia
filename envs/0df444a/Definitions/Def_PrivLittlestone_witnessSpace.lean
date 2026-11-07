-- Prove2me | Definitions.Def_PrivLittlestone_witnessSpace
-- name    : PrivLittlestone_witnessSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:34.519185+00:00
-- url     : https://prove2.me/theorems/de739017-585f-4ebe-aca2-9b2a71b000a0
-- title:
--   Witness space $W_h$
-- statement:
--   For a witness set $A_h$, the **witness space** of $h$ is $W_h = \{ f \in U : f|_{A_h} = h|_{A_h} \}$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma A.1, p.17

import Mathlib
import Definitions.Def_PrivLittlestone_localUniverse

namespace PrivLittlestone

/-- The **witness space** `W_h = {f ∈ U : f|_{A_h} = h|_{A_h}}` of a witness set `A_h` (He–He,
*Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), Lemma A.1, p.17), for a public witness assignment
`Aw : h ↦ A_h`. -/
def witnessSpace {X : Type*} (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (h : X → Bool) : Set (X → Bool) :=
  {f ∈ localUniverse H d | ∀ x ∈ Aw h, f x = h x}

end PrivLittlestone


