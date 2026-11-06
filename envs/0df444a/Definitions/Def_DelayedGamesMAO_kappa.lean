-- Prove2me | Definitions.Def_DelayedGamesMAO_kappa
-- name    : DelayedGamesMAO_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:11.027863+00:00
-- url     : https://prove2.me/theorems/92dd26eb-f5a6-40a4-98ba-2fc9271bda51
-- title:
--   Congestion of a round $\kappa_t=\max_{t\le r\le t+d_t}q_r$
-- statement:
--   For a delay sequence $(d_t)$, the **congestion** of round $t$ is
--   $$
--   \kappa_t=\max_{t\le r\le t+d_t}q_r=\kappa_{t,t+d_t},
--   $$
--   the largest number of active rounds while round $t$ is active. Its sum over $t\in[T]$ lies between $T+d_{\mathrm{tot}}$ and $T+2d_{\mathrm{tot}}$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.4

import Mathlib
import Definitions.Def_DelayedGamesMAO_kappaRun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Congestion of a round** `κ_t := max_{t ≤ r ≤ t + d_t} q_r = κ_{t, t+d_t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.4.

The maximum number of active rounds while round `t` is active. -/
def kappa (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  kappaRun d t (t + d t)

end DelayedGamesMAO


