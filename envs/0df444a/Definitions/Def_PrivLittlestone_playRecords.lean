-- Prove2me | Definitions.Def_PrivLittlestone_playRecords
-- name    : PrivLittlestone_playRecords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:23.08069+00:00
-- url     : https://prove2.me/theorems/8ef7bc50-0069-43f3-8fa4-7afb6f5fcc76
-- title:
--   Records supplied in the adaptive game
-- statement:
--   In the adaptive game between an online learner and an input strategy, the **record at round $t$** is the record $z_t$ the strategy supplies after seeing the released classifiers $g_1, \dots, g_t$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_playClassifiers

namespace PrivLittlestone

/-- The **records supplied in the adaptive game** (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §2.1, p.4):
the record `z_t` the input strategy supplies at round `t`, after seeing `g_0, …, g_t`. -/
def playRecords {X : Type*} {T : ℕ} (A : OnlineLearner X) (inp : InputStrategy X T) (ω : A.Ω) :
    Fin T → X × Bool :=
  fun t => inp t (fun j => playClassifiers A inp ω (Fin.castLE t.isLt j))

end PrivLittlestone


