-- Prove2me | Definitions.Def_PrivLittlestone_IsRealizableBy
-- name    : PrivLittlestone_IsRealizableBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:47.362031+00:00
-- url     : https://prove2.me/theorems/6d2be6b7-aa83-4973-ad4d-48fbb8b94c6d
-- title:
--   Realizability of a stream by a class $H$
-- statement:
--   A stream $z = ((x_t, y_t))_{t=1}^T$ is **realizable** by a class $H \subseteq \{0,1\}^X$ if one member $h \in H$ labels the entire sequence: $h(x_t) = y_t$ for every $t$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §1.1, p.1, and §2.1, p.4

import Mathlib

namespace PrivLittlestone

/-- A stream is **realizable** by a class `H` (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §1.1, p.1,
and §2.1, p.4): one member of `H` labels the entire sequence. -/
def IsRealizableBy {X : Type*} {T : ℕ} (H : Set (X → Bool)) (z : Fin T → X × Bool) : Prop :=
  ∃ h ∈ H, ∀ t : Fin T, h (z t).1 = (z t).2

end PrivLittlestone


