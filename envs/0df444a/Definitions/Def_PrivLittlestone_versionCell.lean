-- Prove2me | Definitions.Def_PrivLittlestone_versionCell
-- name    : PrivLittlestone_versionCell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:31.833356+00:00
-- url     : https://prove2.me/theorems/62e6f58c-9560-4ded-820e-fa255dd1e720
-- title:
--   Version space $V_v(S)$
-- statement:
--   For a sample $S = ((x_i, y_i))_{i=1}^n$ and a label vector $v \in \{0,1\}^n$,
--   $$
--   V_v(S) = \{ h \in U : h(x_i) = v_i \text{ for every } i \in [n] \},
--   $$
--   irrespective of the observed labels. The nonempty version spaces partition $U$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.2, p.18

import Mathlib
import Definitions.Def_PrivLittlestone_localUniverse

namespace PrivLittlestone

/-- The **version space** `V_v(S) = {h ∈ U : h(x_i) = v_i for every i ∈ [n]}` of a sample
`S = ((x_i, y_i))_{i=1}^n` and a label vector `v ∈ {0,1}^n` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Appendix A.2.2, p.18), irrespective of the observed labels `y_i`. -/
def versionCell {X : Type*} (H : Set (X → Bool)) (d : ℕ) (S : List (X × Bool))
    (v : Fin S.length → Bool) : Set (X → Bool) :=
  {h ∈ localUniverse H d | ∀ i : Fin S.length, h (S.get i).1 = v i}

end PrivLittlestone


