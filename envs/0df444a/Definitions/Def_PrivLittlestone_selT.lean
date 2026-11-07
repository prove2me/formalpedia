-- Prove2me | Definitions.Def_PrivLittlestone_selT
-- name    : PrivLittlestone_selT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:37:53.714651+00:00
-- url     : https://prove2.me/theorems/0fe87024-f4f8-4687-9907-40493d97e51e
-- title:
--   Selected layer $T_s(V)$
-- statement:
--   The **selected layer** of rank $s$ of a version space $V$ is
--   $$
--   T_s(V) = \Big\{ h \in V : \rho(h) = s,\ h \notin \bigcup_{g \in D_{>s}(V)} W_g \Big\}, \qquad D_{>d}(V) = \emptyset .
--   $$
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (20), p.18

import Mathlib
import Definitions.Def_PrivLittlestone_selDesc

namespace PrivLittlestone

/-- The **selected layer** `T_s(V) = {h ∈ V : ρ(h) = s, h ∉ ⋃_{g ∈ D_{>s}(V)} W_g}` with
`D_{>s}(V) = ⋃_{t=s+1}^{d} T_t(V)` (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (20), p.18);
`D_{>d}(V) = ∅`, and `D_{>s}(V) = selDesc V (d − s − 1)` for `s < d`. -/
def selT {X : Type*} (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (s : ℕ) : Set (X → Bool) :=
  {h ∈ V | rankOf H d h = s ∧
    ∀ g, s < d → g ∈ selDesc H d Aw V (d - s - 1) → h ∉ witnessSpace H d Aw g}

end PrivLittlestone


