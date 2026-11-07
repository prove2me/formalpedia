-- Prove2me | Definitions.Def_PrivLittlestone_AtMostOneDelIns
-- name    : PrivLittlestone_AtMostOneDelIns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:00.460018+00:00
-- url     : https://prove2.me/theorems/70707f87-72fd-4ce2-88d5-02f81557cd18
-- title:
--   At most one deletion and one insertion
-- statement:
--   A record sequence $S''$ arises from $S$ by **at most one deletion and one insertion** if deleting at most one record of $S$ (at any position) and then inserting at most one record (at any position) gives $S''$.
--
--   This is the change in the retained sequence caused by changing one raw record (§4.1, Lemma B.1).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 2.3, p.5; §4.1, p.7; Lemma B.1, p.21

import Mathlib

namespace PrivLittlestone

/-- **At most one deletion and one insertion** (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Lemma 2.3,
p.5; §4.1, p.7; Lemma B.1, p.21): `S''` arises from `S` by deleting at most one record (at any
position) and then inserting at most one record (at any position). -/
def AtMostOneDelIns {Z : Type*} (S S'' : List Z) : Prop :=
  ∃ S₁ : List Z,
    (S₁ = S ∨ ∃ l r : List Z, ∃ u : Z, S = l ++ u :: r ∧ S₁ = l ++ r) ∧
      (S'' = S₁ ∨ ∃ l r : List Z, ∃ u : Z, S₁ = l ++ r ∧ S'' = l ++ u :: r)

end PrivLittlestone


