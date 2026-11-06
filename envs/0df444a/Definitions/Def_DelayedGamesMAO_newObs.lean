-- Prove2me | Definitions.Def_DelayedGamesMAO_newObs
-- name    : DelayedGamesMAO_newObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:41.843578+00:00
-- url     : https://prove2.me/theorems/7564545a-db35-4046-9ce8-7cb4bf21c53d
-- title:
--   Newly observed rounds $N_t=\{s\in[t]: s+d_s=t\}$
-- statement:
--   For a delay sequence $(d_s)$ and a round $t$, the set of **newly observed rounds** is
--   $$
--   N_t=\{s\in[t]:\ s+d_s=t\},
--   $$
--   the rounds whose feedback is revealed at the end of round $t$. When every feedback arrives within the horizon, $N_1,\dots,N_T$ partition $[T]$.
--
--   **Formalization Note** Defined for every $t$; $N_0=\varnothing$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Newly observed rounds** `N_t := {s ∈ [t] : s + d_s = t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3.

The rounds whose feedback is revealed at the end of round `t`.

**Formalization Note.** `[t]` is `Finset.Icc 1 t`; defined for every `t` (`N_0 = ∅`). -/
def newObs (d : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter (fun s => s + d s = t)

end DelayedGamesMAO


