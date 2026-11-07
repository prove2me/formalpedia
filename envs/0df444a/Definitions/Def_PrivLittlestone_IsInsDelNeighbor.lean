-- Prove2me | Definitions.Def_PrivLittlestone_IsInsDelNeighbor
-- name    : PrivLittlestone_IsInsDelNeighbor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:58.494352+00:00
-- url     : https://prove2.me/theorems/fc6b2f57-3fd0-4ede-8784-497fdf4362c1
-- title:
--   Insertion/deletion neighbors of record sequences
-- statement:
--   Two finite record sequences $S, S'$ are **insertion/deletion neighbors** if one is obtained from the other by inserting a single record at an arbitrary position.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Definition 2.2 and Lemma 2.3, p.5; Appendix A.3, p.21

import Mathlib

namespace PrivLittlestone

/-- **Insertion/deletion neighbors** (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Definition 2.2 and
Lemma 2.3, p.5; Appendix A.3, p.21: "insertion at an arbitrary position"): the finite record
sequence `S'` is `S` with one record inserted at any position, or `S` is `S'` with one record
inserted at any position. The relation is between ordered pairs and is symmetric. -/
def IsInsDelNeighbor {Z : Type*} (S S' : List Z) : Prop :=
  (∃ l r : List Z, ∃ u : Z, S = l ++ r ∧ S' = l ++ u :: r) ∨
    (∃ l r : List Z, ∃ u : Z, S' = l ++ r ∧ S = l ++ u :: r)

end PrivLittlestone


