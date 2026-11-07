-- Prove2me | Definitions.Def_PrivLittlestone_retainedSeq
-- name    : PrivLittlestone_retainedSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:11.312069+00:00
-- url     : https://prove2.me/theorems/6faba39f-009c-429a-ae47-74f415b9cd8a
-- title:
--   Retained sequence replayed from a public history
-- statement:
--   Given released classifiers $g_1, \dots, g_T$ and records $z_1, \dots, z_T$, the **retained sequence through round $t$** lists, in order, the records $\kappa(g_i, z_i)$ for the rounds $i \le t$ on which $g_i$ errs on $z_i$ and $\kappa(g_i, z_i) \neq \bot$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.1 and its proof, p.21

import Mathlib

namespace PrivLittlestone

/-- The **retained sequence replayed from a public history** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Lemma B.1 and its proof, p.21): over the rounds `i < t`, in order, the record `κ(g_i, z_i)` is
appended whenever the public classifier `g_i` errs on `z_i` and the filter does not return `⊥`. -/
def retainedSeq {X Z : Type*} {T : ℕ} (κ : (X → Bool) → X × Bool → Option Z)
    (gs : Fin T → X → Bool) (recs : Fin T → X × Bool) (t : ℕ) : List Z :=
  ((List.finRange T).filter fun i : Fin T => decide ((i : ℕ) < t)).flatMap fun i : Fin T =>
    if gs i (recs i).1 ≠ (recs i).2 then (κ (gs i) (recs i)).toList else []

end PrivLittlestone


