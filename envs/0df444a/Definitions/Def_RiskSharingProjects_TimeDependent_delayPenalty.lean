-- Prove2me | Definitions.Def_RiskSharingProjects_TimeDependent_delayPenalty
-- name    : RiskSharingProjects_TimeDependent_delayPenalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:15:35.179535+00:00
-- url     : https://prove2.me/theorems/adc1f01e-6ab0-4fe9-9f65-f3356c46de0b
-- title:
--   A firm's share of the time-dependent delay penalty
-- statement:
--   Under time-dependent cost the first period of project delay costs firm $i$ the amount $p^1_i$ and the second period costs it $p^2_i$ (§4.1: "When both firms delay, the delay penalty is $p^1_i+p^2_i$ for firm $i$"). For first- and second-period shares $\pi_1,\pi_2$ the penalty after $n$ periods of delay is
--
--   $$
--   \mathrm{pen}(\pi_1,\pi_2;n)=\begin{cases}0,&n=0,\\ \pi_1,&n=1,\\ \pi_1+\pi_2,&n\ge 2.\end{cases}
--   $$
--
--   **Formalization Note** In the two-firm game the delay is at most $2$, so the value for $n>2$ is never used.
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), §4.1, p. 12

import Mathlib

namespace RiskSharingProjects.TimeDependent

/-- **A firm's share of the time-dependent delay penalty after `n` periods of project delay.**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), §4.1 "Time-dependent Cost (Assumption 1(b))", p. 12: "Let p^1 (or p^2) be the penalty for the
1st (the 2nd, respectively) period of the project delay; and let p^1_i and p^2_i be the penalty
shared by firm i … When both firms delay, the delay penalty is p^1_i + p^2_i for firm i."

`delayPenalty pFirst pSecond n` is `0` for `n = 0`, `pFirst` (= p^1_i) for `n = 1` and
`pFirst + pSecond` (= p^1_i + p^2_i) for `n ≥ 2`.

**Formalization Note.** In the two-firm game at most two periods of delay occur, so the branch
`n ≥ 2` is used only at `n = 2`; its value for `n > 2` is never evaluated. -/
noncomputable def delayPenalty (pFirst pSecond : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => pFirst
  | _ => pFirst + pSecond

end RiskSharingProjects.TimeDependent


