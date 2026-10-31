-- Prove2me | Definitions.Def_Underdogs_Params_mass
-- name    : Underdogs_Params_mass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:46.713336+00:00
-- url     : https://prove2.me/theorems/0662eaba-68d0-4540-82ca-d0c67fcd11f6
-- title:
--   Joint probability of quality and two outcomes
-- statement:
--   The probability of an elementary outcome $(q,o_1,o_2)$: the agent has quality $q\in\{H,L\}$, first-period outcome $o_1$ and second-period outcome $o_2$, each a success $S$ or a failure $F$. Each quality has prior probability $1/2$ ("It is equally likely that an agent is of high or low quality"), so
--   $$
--   \Pr(q,o_1,o_2)=\tfrac12\cdot\Pr(o_1\mid q)\cdot\Pr(o_2\mid q,o_1),
--   $$
--   where the first-period success probability is $p_q$ and the second-period one is $p_{q,S}$ after a success and $p_{q,F}$ after a failure; failure has the complementary probability.
--
--   **Formalization Note** Outcomes are booleans, `true` for success, and the coordinates are in time order: $(F,S)$ is `(false, true)`.
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6); Appendix A, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Quality
import Definitions.Def_Underdogs_Params

namespace Underdogs

/-- The probability of an elementary outcome `(q, o₁, o₂)` of the two-period model: the agent has
quality `q` (prior 1/2 each), first-period outcome `o₁` and second-period outcome `o₂`
(`true` = success S, `false` = failure F), writing `ω = (q, o₁, o₂)`. It is
`1/2 · P(o₁ | q) · P(o₂ | q, o₁)`, where the first-period success probability is `p_q` and the
second-period one is `p_{q,S}` after a success and `p_{q,F}` after a failure.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, p.5 (PDF p.6): "It is equally likely that an agent is of high or low quality"; the
Bayes computations of Appendix A, p.35 (PDF p.36) use this law.

**Formalization Note** The order of the outcome coordinates is the order in time: `(F, S)` is
`(false, true)`, failure first. -/
noncomputable def Params.mass (P : Params) (ω : Quality × Bool × Bool) : ℝ :=
  let p₁ : ℝ := if ω.1 = Quality.H then P.ph else P.pl
  let p₂ : ℝ :=
    if ω.2.1 then (if ω.1 = Quality.H then P.phS else P.plS)
    else (if ω.1 = Quality.H then P.phF else P.plF)
  (1 / 2) * (if ω.2.1 then p₁ else 1 - p₁) * (if ω.2.2 then p₂ else 1 - p₂)

end Underdogs


