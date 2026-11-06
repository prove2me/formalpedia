-- Prove2me | Definitions.Def_DelayedGamesMAO_pending
-- name    : DelayedGamesMAO_pending
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:38.94836+00:00
-- url     : https://prove2.me/theorems/ef6c472b-7337-4358-bd0f-8a12243220e0
-- title:
--   Pending rounds $P_t=\{s\in[t-1]: s+d_s\ge t\}$
-- statement:
--   For a delay sequence $(d_s)$ and a round $t$, the set of **pending rounds** is
--   $$
--   P_t=\{s\in[t-1]:\ s+d_s\ge t\},
--   $$
--   the earlier rounds whose feedback is still missing at the start of round $t$. Together with $O_t$ it partitions $[t-1]$.
--
--   **Formalization Note** Defined for every $t$ by the same formula (the analysis reads $P_{T+1}$).
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Pending rounds** `P_t := {s ∈ [t − 1] : s + d_s ≥ t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3.

The earlier rounds whose feedback has not been revealed by the start of round `t`.

**Formalization Note.** `[t − 1]` is `Finset.Icc 1 (t - 1)`; the set is defined for every `t`
by the printed formula (the analysis reads `P_{T+1}`). -/
def pending (d : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (t - 1)).filter (fun s => t ≤ s + d s)

end DelayedGamesMAO


