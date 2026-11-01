-- Prove2me | Definitions.Def_LocalDOvS_SUS_histAt
-- name    : LocalDOvS_SUS_histAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:58.746044+00:00
-- url     : https://prove2.me/theorems/736cef22-8870-47c7-8baa-cf2a4531ae93
-- title:
--   History of a run on a tape
-- statement:
--   The **history** of a run of algorithm $A$ on tape $\omega$ after $t$ steps. It starts empty. If $A$ asks to simulate $x$, the next unread entry $\omega(x,c)$ of $x$ is appended, where $c$ is the number of earlier simulations of $x$; once $A$ stops, the history no longer changes.
--
--   This construction makes the $(j+1)$-th simulation of $x$ equal to $\omega(x,j)$ whatever the order of queries, so a run on a random tape is the run of $A$ against independent replications.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §2.2, p.10

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SeqAlg
import Definitions.Def_LocalDOvS_SUS_ptVals

namespace LocalDOvS.SUS

/-- The history of a run of algorithm `A` on tape `ω` after `t` steps (Zhang–Zheng–Lavaei,
arXiv:2012.02427v2, §2.2, p.10). If `A` asks to simulate `x`, the next unread tape entry of `x`,
`ω (x, c)` with `c` the number of earlier simulations of `x`, is appended; once `A` stops, the
history no longer changes.

**Formalization Note.** Reading the tape this way makes the `j`-th simulation of `x` equal to
`ω (x, j)` whatever the order of the queries, which is the paper's "independent copy" model. -/
def histAt (A : SeqAlg) (ω : ℕ × ℕ → ℝ) : ℕ → List (ℕ × ℝ)
  | 0 => []
  | t + 1 =>
    match A (histAt A ω t) with
    | .sample x => histAt A ω t ++ [(x, ω (x, (ptVals (histAt A ω t) x).length))]
    | .stop _ => histAt A ω t

end LocalDOvS.SUS


