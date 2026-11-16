-- Prove2me | Definitions.Def_DelayedGamesMAO_Supplement_boldRounds
-- name    : DelayedGamesMAO_Supplement_boldRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:51:08.950191+00:00
-- url     : https://prove2.me/theorems/c751d105-7029-49b6-8205-398f099b4a02
-- title:
--   Earlier rounds of the same instance, $[s\in[t-1]: i_s=i_t]$
-- statement:
--   For delays $(d_s)$ and a round $t$, this is the list of earlier rounds $s\in[t-1]$ with the same instance index as $t$, $i_s=i_t$, in increasing order of $s$.
--
--   Because the instance $B_{i_t}$ is idle at round $t$, it has already received the feedback of each of these rounds, in this order. The list is therefore the local history of that instance when it chooses the action of round $t$.
--
--   **Formalization Note** The list is $[1,\dots,t-1]$ filtered by $i_s=i_t$; it is empty for $t\le 1$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), App. B.1, Algorithm 2, p.33

import Mathlib
import Definitions.Def_DelayedGamesMAO_Supplement_boldIndex

set_option autoImplicit false

namespace DelayedGamesMAO.Supplement

/-- **Earlier rounds handled by the instance of round `t`** in the refined BOLD reduction:
the list `[s ∈ [t − 1] : i_s = i_t]` in increasing order of `s`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), App. B.1, Algorithm 2, p.33.

The instance `B_{i_t}` is idle at round `t`, so the feedback of each of these rounds has already
been fed to it, in this order (each instance receives the feedback of a round before it is used
again); the list is that instance's local history at round `t`.

**Formalization Note.** `List.range' 1 (t - 1) = [1, …, t − 1]` (empty for `t ≤ 1`). -/
def boldRounds (d : ℕ → ℕ) (t : ℕ) : List ℕ :=
  (List.range' 1 (t - 1)).filter (fun s => boldIndex d s = boldIndex d t)

end DelayedGamesMAO.Supplement


