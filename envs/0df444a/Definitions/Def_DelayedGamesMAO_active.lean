-- Prove2me | Definitions.Def_DelayedGamesMAO_active
-- name    : DelayedGamesMAO_active
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:27.688195+00:00
-- url     : https://prove2.me/theorems/5e16bb49-c8b6-45da-8d4f-e7b082ef88ae
-- title:
--   Active rounds $A_t=P_t\cup\{t\}$
-- statement:
--   For a delay sequence $(d_s)$ and a round $t$, the set of **active rounds** is
--   $$
--   A_t=P_t\cup\{t\},
--   $$
--   the rounds $s\le t$ whose feedback arrives in round $t$ or later.
--
--   **Formalization Note** Defined for every $t$ by the same formula; Definition 1 and the schedule (10) read $A_{T+1}$, which is $\{T+1\}$ when every feedback arrives by the end of round $T$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib
import Definitions.Def_DelayedGamesMAO_pending

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Active rounds** `A_t := P_t ∪ {t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3.

The rounds `s ≤ t` whose feedback arrives in round `t` or later.

**Formalization Note.** Defined for every `t` by the printed formula (Definition 1 and (10) read
`A_{T+1}`, which is `{T + 1}` when every round's feedback arrives by the end of round `T`). -/
def active (d : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  insert t (pending d t)

end DelayedGamesMAO


