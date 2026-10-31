-- Prove2me | Definitions.Def_LearnManip_IsOptimalPolicy
-- name    : LearnManip_IsOptimalPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:37.706988+00:00
-- url     : https://prove2.me/theorems/3cf1e1e5-265b-4d86-a5f3-146e526a208e
-- title:
--   The Markov policy $(q^*,\Lambda^*)$
-- statement:
--   A policy is the Markov policy of Theorems 1 and 2 for initial cost rate $c_1$ when, at each history with last mean $\mu$ and current variance $s$, period $n+1$ uses the quantity $q^*(s,c_1\eta^n)$ and the distorted law with density $\Lambda^*(\mu,s,c_1\eta^n)$.
--
--   **Formalization Note.** This is a predicate because being a policy at all is part of the goal. The recursion through the variance path determines the policy uniquely. The cost rate moves with the true $\eta$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), §4, p.15, Theorems 1–2, pp.15, 17

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_History
import Definitions.Def_LearnManip_varPath
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_qStar
import Definitions.Def_LearnManip_Gstar

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- `M` is the Markov policy `(q*(s_{t−1}, c_t), Λ*(μ_{t−1}, s_{t−1}, c_t))` of §4, p.15, and
Theorems 1–2 of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), for the initial cost rate `c₁`: in
period `n + 1` the cost rate is `c₁ ηⁿ`, with the true `η`. The recursion through `varPath` determines
`M` uniquely.

**Formalization Note.** This is a predicate, not a definition of a `Policy` term, because that it is a
`Policy` at all is part of the theorem. -/
def IsOptimalPolicy (P : Params) {s₀ : ℝ≥0} (c₁ : ℝ≥0) (M : Policy s₀) : Prop :=
  ∀ (n : ℕ) (h : History n),
    M.q n h = qStar P (varPath M.q s₀ n h) (c₁ * P.η ^ n) ∧
      M.K n h = Gstar P (History.last h) (varPath M.q s₀ n h) (c₁ * P.η ^ n)

end LearnManip


