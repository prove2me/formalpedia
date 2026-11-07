-- Prove2me | Definitions.Def_PrivLittlestone_selD
-- name    : PrivLittlestone_selD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:37:30.144904+00:00
-- url     : https://prove2.me/theorems/3e6bb582-bedc-485a-ac82-3ad684d5d6cd
-- title:
--   Selected set $D(V) = \bigcup_{s=0}^d T_s(V)$
-- statement:
--   The **selected set** of a version space $V$ is $D(V) = \bigcup_{s=0}^{d} T_s(V)$. The candidate set of the Littlestone construction is $C(S) = \bigcup_{v : V_v(S) \ne \emptyset} D(V_v(S))$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (20), p.18

import Mathlib
import Definitions.Def_PrivLittlestone_selDesc

namespace PrivLittlestone

/-- The **selected set** `D(V) = ⋃_{s=0}^{d} T_s(V)` of a version space (He–He, *Private Online
Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), (20), p.18). -/
def selD {X : Type*} (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) : Set (X → Bool) :=
  selDesc H d Aw V d

end PrivLittlestone


