-- Prove2me | Definitions.Def_PrivLittlestone_transcript
-- name    : PrivLittlestone_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:32.263854+00:00
-- url     : https://prove2.me/theorems/a899e6ce-aaee-4659-bdfa-c77291a68e25
-- title:
--   Classifier transcript $(g_1,\dots,g_T)$ on a fixed stream
-- statement:
--   For an online learner $A$, a fixed stream $z = (z_1, \dots, z_T)$ and coins $\omega$, the **classifier transcript** is the sequence $(g_1, \dots, g_T)$, where $g_t$ is released from the first $t-1$ records of $z$ and $\omega$.
--
--   It is the output protected by replacement privacy on fixed streams, and the object whose mistakes Theorem 1.1 counts.
--
--   **Formalization Note** Entry $t$ ($0$-based) is the paper's $g_{t+1}$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner

namespace PrivLittlestone

/-- The **classifier transcript** `(g_1, …, g_T)` of an online learner on a fixed length-`T`
stream `z` (He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027
submission manuscript (sha256 21480556…c562), §2.1, p.4): at round `t` the learner releases the
classifier computed from the first `t` records of `z` and its coins.

**Formalization Note** 0-based rounds: entry `t` is the paper's `g_{t+1}`. -/
def transcript {X : Type*} {T : ℕ} (A : OnlineLearner X) (z : Fin T → X × Bool) (ω : A.Ω) :
    Fin T → X → Bool :=
  fun t => A.release t (fun i => z (Fin.castLE t.isLt.le i)) ω

end PrivLittlestone


