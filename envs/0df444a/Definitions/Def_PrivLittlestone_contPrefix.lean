-- Prove2me | Definitions.Def_PrivLittlestone_contPrefix
-- name    : PrivLittlestone_contPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:08.400494+00:00
-- url     : https://prove2.me/theorems/ca59bf16-9d8a-418a-82c7-f40366288867
-- title:
--   Classifiers on the continuation with a fixed aggregate
-- statement:
--   For a phase starting at round $t_0$ with aggregate $g$, the **continuation with a fixed aggregate** releases the past classifiers before $t_0$ and $g$ at every round from $t_0$ on: this is the hypothetical continuation in which every threshold answer of the phase is Below. At round $t$ it shows the classifiers $g_1, \dots, g_t$ of this continuation.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (A2), p.7; proof of Lemma B.2, p.22

import Mathlib

namespace PrivLittlestone

/-- The classifiers `g_0, …, g_t` seen at round `t` on the **continuation with a fixed aggregate**
(He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), (A2), p.7, and proof of Lemma B.2, p.22: "Follow the
hypothetical continuation in which every threshold answer in this phase is Below"): the past
classifiers before the phase-start round `t₀`, and the phase aggregate `g` from `t₀` on. -/
def contPrefix {X : Type*} {T : ℕ} (past : Fin T → X → Bool) (t₀ : ℕ) (g : X → Bool)
    (t : Fin T) : Fin (t.val + 1) → X → Bool :=
  fun j => if (j : ℕ) < t₀ then past (Fin.castLE t.isLt j) else g

end PrivLittlestone


