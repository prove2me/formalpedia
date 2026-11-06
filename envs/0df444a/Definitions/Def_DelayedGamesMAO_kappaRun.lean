-- Prove2me | Definitions.Def_DelayedGamesMAO_kappaRun
-- name    : DelayedGamesMAO_kappaRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:25.379338+00:00
-- url     : https://prove2.me/theorems/54329890-87c1-449a-a91a-3c2f5b0f7aaa
-- title:
--   Running congestion $\kappa_{s,t}=\max_{s\le r\le t}q_r$
-- statement:
--   For a delay sequence $(d_s)$ and rounds $s\le t$, the **running congestion** of round $s$ at time $t$ is
--   $$
--   \kappa_{s,t}=\max_{s\le r\le t}q_r ,
--   $$
--   the largest number of active rounds seen since round $s$; it is observable at round $t$. The paper uses it for $s\le t\le s+d_s$.
--
--   **Formalization Note** The function is total; its values for $t<s$ (where it is $0$) or $t>s+d_s$ are never used.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.4

import Mathlib
import Definitions.Def_DelayedGamesMAO_q

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Running congestion** `κ_{s,t} := max_{s ≤ r ≤ t} q_r`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.4.

The paper uses `κ_{s,t}` for `s ≤ t ≤ s + d_s` (while round `s` is active).

**Formalization Note.** The maximum over `{s, …, t} = Finset.Icc s t` is `Finset.sup` in `ℕ`;
the function is total, and its values for `t < s` (`0`) or `t > s + d_s` are never used. -/
def kappaRun (d : ℕ → ℕ) (s t : ℕ) : ℕ :=
  (Finset.Icc s t).sup (q d)

end DelayedGamesMAO


