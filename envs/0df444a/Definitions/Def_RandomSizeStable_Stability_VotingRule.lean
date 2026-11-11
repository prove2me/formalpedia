-- Prove2me | Definitions.Def_RandomSizeStable_Stability_VotingRule
-- name    : RandomSizeStable_Stability_VotingRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:29.037226+00:00
-- url     : https://prove2.me/theorems/6dc68f30-6afe-4ce1-8c55-cf8c5dce43b4
-- title:
--   Ranking-only randomized voting rules on every finite size
-- statement:
--   A randomized voting rule is one family $R$ of maps on every pair of positive sizes $n,m$. Given a strict-ranking profile $E$ on $n$ voters and $m$ candidates, it returns an actual lottery:
--   $$R_{n,m}:\{\text{strict-ranking profiles on }[n],[m]\}\longrightarrow\Delta([m]).$$
--   The family receives only rankings, never hidden distances. Each returned mass function is nonnegative and sums to one. A single family is selected before quantifying over any consistent metric.
--
--   **Formalization Note** The labels are represented by $\operatorname{Fin}(n)$ and $\operatorname{Fin}(m)$. Relabeling covers every finite nonempty instance, including a single voter or a single candidate. Proof arguments recording positive sizes carry no extra information.
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 8, Definition 1 and Section 2.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_DrawLaw
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Definition 1, p.8: a single family of ranking-only lottery maps on every
nonempty finite electorate and candidate set. Fin n and Fin m represent all finite
instances by relabeling. No hidden distances are supplied to a rule. -/
def VotingRule :=
  ∀ (n m : ℕ), 0 < n → 0 < m → Election (Fin n) (Fin m) →
    {P : Fin m → ℝ // P ∈ stdSimplex ℝ (Fin m)}

end RandomSizeStable.Stability


