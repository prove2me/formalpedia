-- Prove2me | Definitions.Def_PrivLittlestone_IsAdjacent
-- name    : PrivLittlestone_IsAdjacent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:51.853843+00:00
-- url     : https://prove2.me/theorems/18651b56-6cf4-41cc-8751-cda4d93e7e5e
-- title:
--   Replacement adjacency of streams
-- statement:
--   Two length-$T$ streams $z, z'$ are **adjacent under replacement** if they differ in at most one record: there is an index $i$ with $z_j = z'_j$ for every $j \neq i$.
--
--   **Formalization Note** Equal streams count as adjacent; the privacy inequality is then trivial for $\varepsilon, \delta \ge 0$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib

namespace PrivLittlestone

/-- **Replacement adjacency** of fixed streams (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §2.1, p.4):
two length-`T` streams differ in (at most) one record.

**Formalization Note** `z = z'` is allowed; the privacy inequality then holds trivially for
`ε, δ ≥ 0`, so this adds nothing. -/
def IsAdjacent {R : Type*} {T : ℕ} (z z' : Fin T → R) : Prop :=
  ∃ i : Fin T, ∀ j : Fin T, j ≠ i → z j = z' j

end PrivLittlestone


