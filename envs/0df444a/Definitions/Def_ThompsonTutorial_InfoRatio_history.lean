-- Prove2me | Definitions.Def_ThompsonTutorial_InfoRatio_history
-- name    : ThompsonTutorial_InfoRatio_history
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:09:17.259274+00:00
-- url     : https://prove2.me/theorems/9bec8fad-1b44-4543-871a-a2c86799e1f5
-- title:
--   History $H_t=(Z_1,\dots,Z_t)$ of a process
-- statement:
--   Let $(Z_s)_{s\ge1}$ be a sequence of random elements $Z_s:\Omega\to B$. The **history** up to period $t$ is the random tuple
--   $$
--   H_t\;=\;(Z_1,\dots,Z_t)\in B^t .
--   $$
--   In the online decision problem $Z_s=(x_s,y_s)$ is the action and outcome of period $s$, so $H_{t-1}$ is everything observed before the action of period $t$ is chosen; the algorithm chooses its action as a function of this history, and the information ratio (8.7) conditions on it.
--
--   **Formalization Note** Periods are 1-based: $H_t$ is indexed by `Fin t`, its $i$-th entry is `Z (i+1)`, $H_0$ is the empty history, and `Z 0` is never used.
-- source:
--   Russo, Van Roy, Kazerouni, Osband, Wen, A Tutorial on Thompson Sampling, Found. Trends Mach. Learn. 11(1) (2018), §8.1.2, p. 71 (PDF p. 74) "the history of actions and observed outcomes"; H_{t−1} in (8.7), p. 75 (PDF p. 78)

import Mathlib

namespace ThompsonTutorial.InfoRatio

/-- **The history `H_t = (Z_1, …, Z_t)` of a process.**
Russo, Van Roy, Kazerouni, Osband, Wen, *A Tutorial on Thompson Sampling*, Found. Trends Mach.
Learn. 11(1) (2018), §8.1.2, p. 71 (PDF p. 74): "an action as a function of the history of
actions and observed outcomes"; `H_{t−1}` in (8.7), p. 75 (PDF p. 78).

`history Z t ω` is the tuple `(Z_1(ω), …, Z_t(ω))`, indexed by `i : Fin t` with
`(history Z t ω) i = Z (i + 1) ω`. In the online decision problem `Z_s = (x_s, y_s)`, so `H_t`
records the first `t` actions and outcomes.

**Formalization Note.** Periods are 1-based: `Z 1` is the first observation, `history Z 0` is the
empty history (the unique element of `Fin 0 → B`), and `Z 0` is never used. -/
def history {Ω B : Type*} (Z : ℕ → Ω → B) (t : ℕ) : Ω → (Fin t → B) :=
  fun ω i => Z ((i : ℕ) + 1) ω

end ThompsonTutorial.InfoRatio


