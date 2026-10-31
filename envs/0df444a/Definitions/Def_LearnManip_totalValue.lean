-- Prove2me | Definitions.Def_LearnManip_totalValue
-- name    : LearnManip_totalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:42.157991+00:00
-- url     : https://prove2.me/theorems/dc02281d-803a-434b-976a-b8eb4177ab6c
-- title:
--   Total discounted profit of a policy
-- statement:
--   The total discounted profit of a policy is the limit superior of the partial sums $J_T(M)$, as an extended real number.
--
--   **Formalization Note.** The paper does not say in what sense the infinite sum in (8) is defined. The limit superior is the most generous reading for the firm, so an upper bound for it is the strongest one. For the optimal policy the partial sums converge.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (8), p.11

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_horizonValue

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The total discounted profit of a policy, the inner sum of (8), p.11, of Keppo, Kim, Zhang (SSRN
3465030, 2021-09-04).

**Formalization Note.** The paper does not say in what sense the infinite sum is defined. It is the
`limsup` of the partial sums in `EReal`: the most generous reading for the firm, so an upper bound
on the supremum of these values is the strongest one. -/
noncomputable def totalValue (P : Params) {s₀ : ℝ≥0} (M : Policy s₀) (μ₀ : ℝ) (c₁ : ℝ≥0) : EReal :=
  Filter.limsup (horizonValue P M μ₀ c₁) Filter.atTop

end LearnManip


