-- Prove2me | Definitions.Def_PrivLittlestone_gameMistakes
-- name    : PrivLittlestone_gameMistakes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:26.312738+00:00
-- url     : https://prove2.me/theorems/cfc52499-9a51-4a10-b663-24514249fa4f
-- title:
--   Number of mistakes $M_T$ in the adaptive game
-- statement:
--   In the adaptive game, the **number of mistakes** is $M_T = \sum_{t=1}^T \mathbf 1\{g_t(x_t) \neq y_t\}$, where $g_t$ is the released classifier and $z_t = (x_t, y_t)$ the record supplied at round $t$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §1.1, p.1, and §2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_playRecords

namespace PrivLittlestone

/-- The **number of mistakes** `M_T` in the adaptive game (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§1.1, p.1, and §2.1, p.4): the rounds `t` with `g_t(x_t) ≠ y_t`. -/
def gameMistakes {X : Type*} {T : ℕ} (A : OnlineLearner X) (inp : InputStrategy X T)
    (ω : A.Ω) : ℕ :=
  (Finset.univ.filter fun t : Fin T =>
    playClassifiers A inp ω t (playRecords A inp ω t).1 ≠ (playRecords A inp ω t).2).card

end PrivLittlestone


