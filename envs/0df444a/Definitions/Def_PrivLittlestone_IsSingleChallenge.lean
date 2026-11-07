-- Prove2me | Definitions.Def_PrivLittlestone_IsSingleChallenge
-- name    : PrivLittlestone_IsSingleChallenge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:53.976774+00:00
-- url     : https://prove2.me/theorems/7edaf3ed-4ef5-4904-9c60-ab73ce0537f7
-- title:
--   Single-challenge condition on an adversary
-- statement:
--   An adversary strategy is **single-challenge** if, along every possible transcript, at most one supplied pair has unequal records: for every sequence of released classifiers there is at most one round $t$ with $z^0_t \neq z^1_t$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Definition 2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_Adversary

namespace PrivLittlestone

/-- The **single-challenge condition** (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Definition 2.1, p.4):
"Along every possible transcript, at most one supplied pair may have unequal records": for every
sequence of released classifiers, at most one round's pair has `z⁰_t ≠ z¹_t`. -/
def IsSingleChallenge {X : Type*} {T : ℕ} (adv : Adversary X T) : Prop :=
  ∀ gs : Fin T → X → Bool, ∀ i j : Fin T,
    (adv i (fun k => gs (Fin.castLE i.isLt k))).1 ≠ (adv i (fun k => gs (Fin.castLE i.isLt k))).2 →
    (adv j (fun k => gs (Fin.castLE j.isLt k))).1 ≠ (adv j (fun k => gs (Fin.castLE j.isLt k))).2 →
    i = j

end PrivLittlestone


