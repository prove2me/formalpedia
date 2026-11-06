-- Prove2me | Definitions.Def_DelayedGamesMAO_q
-- name    : DelayedGamesMAO_q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:31.419729+00:00
-- url     : https://prove2.me/theorems/ad65e4e7-65d7-4cee-879b-5ee05c489051
-- title:
--   Number of active rounds $q_t=|A_t|$
-- statement:
--   For a delay sequence $(d_s)$, the **number of active rounds** at round $t$ is $q_t=|A_t|$, where $A_t$ is the active set. Since $t\in A_t$, $q_t=\sigma_t+1\ge1$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib
import Definitions.Def_DelayedGamesMAO_active

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Number of active rounds** `q_t := |A_t|`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3. -/
def q (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  (active d t).card

end DelayedGamesMAO


