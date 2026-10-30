-- Prove2me | Definitions.Def_CoffmanMitrani_mix
-- name    : CoffmanMitrani_mix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:50.627123+00:00
-- url     : https://prove2.me/theorems/c5e97472-9961-4491-80eb-b267759d5c1b
-- title:
--   The mixing strategy for $S_1,\dots,S_k$
-- statement:
--   Given strategies $S_1,\dots,S_k$ and a probability vector $(\alpha_1,\dots,\alpha_k)$, the mixing strategy decides at the beginning of each busy period, with probability $\alpha_j$ and independently across busy periods, that all sequencing decisions during that busy period are made according to $S_j$. Outside busy periods the server is idle.
--
--   Concretely, the type of the busy period opened by job $j_0$ is chosen from the first seed of $j_0$, and during that busy period the mixing strategy does what the chosen strategy does on the sample point with that seed removed.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, pp. 813–814

import Mathlib
import Definitions.Def_CoffmanMitrani_Schedule
import Definitions.Def_CoffmanMitrani_IsBPStart
import Definitions.Def_CoffmanMitrani_InBP
import Definitions.Def_CoffmanMitrani_seed
import Definitions.Def_CoffmanMitrani_shift
import Definitions.Def_CoffmanMitrani_mixType

namespace CoffmanMitrani

open Classical in
/-- **The mixing strategy.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, pp. 813–814: "Consider a new strategy which, at the beginning of each busy period, decides
with probability α that sequencing decisions during that busy period are to be made according to S1,
and with probability 1 − α these decisions are to be made according to S2. Such a strategy will be
called the mixing strategy for S1 and S2, with parameter α. … a sequence of Bernoulli trials
determines the sequence of busy period types. These strategies are generalized in the obvious way to
mixing strategies for S1, S2, ···, Sk with parameters α1, α2, ···, αk−1."

`mix α S ω t`: if `t` lies in the busy period opened by a job `j0`, the type of that busy period is
`mixType α (seed ω j0 0)` and the decision at `t` is that of strategy `S (type)` run on the
seed-shifted sample point `shift ω`; outside busy periods the server is idle.

**Formalization Note.** `k = K + 1` strategies with probability vector `α` (see `mixType`). Busy
periods are strategy-independent (`IsBPStart`, `InBP`), so a busy period of `ω` is also a busy period
of every strategy run on `shift ω` (which has the same arrival and service data). -/
noncomputable def mix {M K : ℕ} (α : Fin (K + 1) → ℝ) (S : Fin (K + 1) → Schedule M) :
    Schedule M :=
  fun ω t =>
    if h : ∃ j0 : Job M, IsBPStart ω j0 ∧ InBP ω j0 t then
      S (mixType α (seed ω h.choose 0)) (shift ω) t
    else none

end CoffmanMitrani


