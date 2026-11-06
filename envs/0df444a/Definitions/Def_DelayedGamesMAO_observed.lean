-- Prove2me | Definitions.Def_DelayedGamesMAO_observed
-- name    : DelayedGamesMAO_observed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:40.819195+00:00
-- url     : https://prove2.me/theorems/a4d87d86-9602-4ebb-8c21-963996ea07e4
-- title:
--   Observed rounds $O_t=\{s\in[t-1]: s+d_s<t\}$
-- statement:
--   Fix a delay sequence $(d_s)_{s\ge1}$ of natural numbers: the feedback (gradient) of round $s$ is revealed at the end of round $s+d_s$. For a round $t$, the set of **observed rounds** is
--   $$
--   O_t=\{s\in[t-1]:\ s+d_s<t\},
--   $$
--   the earlier rounds whose feedback was revealed before round $t$ starts. Here $[n]=\{1,\dots,n\}$ and $[0]=\varnothing$.
--
--   $O_t$ is the information available to a learner at the start of round $t$; MAO-OMD takes its hints from it.
--
--   **Formalization Note** Rounds are natural numbers and $O_t$ is a finite set of naturals, defined for every $t$ by the same formula (the algorithm also reads $O_{T+1}$); $O_0=O_1=\varnothing$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Observed rounds** `O_t := {s ∈ [t − 1] : s + d_s < t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3.

`d s` is the delay of round `s`: the feedback of round `s` is revealed at the end of round
`s + d s`. `O_t` collects the earlier rounds whose feedback was revealed before round `t`.

**Formalization Note.** Rounds are the natural numbers `1, 2, …`, and `[n] = {1, …, n}` is
`Finset.Icc 1 n` (empty for `n = 0`). The set is defined for every `t` by the printed formula
(Algorithm 1 also reads `O_{T+1}`); `O_0 = O_1 = ∅`. -/
def observed (d : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (t - 1)).filter (fun s => s + d s < t)

end DelayedGamesMAO


