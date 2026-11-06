-- Prove2me | Definitions.Def_DelayedGamesMAO_sigma
-- name    : DelayedGamesMAO_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:42.262853+00:00
-- url     : https://prove2.me/theorems/c2672bcc-a144-459b-9d7c-6b364b022dc7
-- title:
--   Number of pending rounds $\sigma_t=|P_t|$
-- statement:
--   For a delay sequence $(d_s)$, the **number of pending rounds** at round $t$ is $\sigma_t=|P_t|$, where $P_t$ is the pending set.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib
import Definitions.Def_DelayedGamesMAO_pending

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Number of pending rounds** `σ_t := |P_t|`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3. -/
def sigma (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  (pending d t).card

end DelayedGamesMAO


