-- Prove2me | Definitions.Def_LearnManip_V
-- name    : LearnManip_V
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:38.308592+00:00
-- url     : https://prove2.me/theorems/3972efa7-6772-427a-b2d4-ae616472bb90
-- title:
--   The value function $V$ of (8)
-- statement:
--   The value function
--   $$V(\mu_0,s_0,c_1)=\sup_{M}\ \sum_{t=1}^\infty\alpha^{t-1}E\bigl[g_t(\pi^M_{t-1},\delta_t)\bigr],$$
--   the supremum over all admissible policies of the total discounted profit, for the prior $N(\mu_0,s_0)$ and initial cost rate $c_1$.
--
--   **Formalization Note.** The supremum is taken in the extended reals, so an unbounded family gives $+\infty$ and not a junk value. The family is nonempty.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (8), p.11

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_IsAdmissible
import Definitions.Def_LearnManip_totalValue

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The value function (8), p.11, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04): the supremum of
the total discounted profit over all admissible policies, for the prior `N(μ₀, s₀)` and initial cost
rate `c₁`. The supremum is in `EReal`, so neither an unbounded nor an empty family gives a junk
value. -/
noncomputable def V (P : Params) (μ₀ : ℝ) (s₀ c₁ : ℝ≥0) : EReal :=
  ⨆ M : {M : Policy s₀ // IsAdmissible M μ₀}, totalValue P M.1 μ₀ c₁

end LearnManip


