-- Prove2me | Definitions.Def_FairShareAlmostAll_Slack_Supplement_EntitlementCap
-- name    : FairShareAlmostAll_Slack_Supplement_EntitlementCap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:09.022095+00:00
-- url     : https://prove2.me/theorems/5bc3b208-cec0-486b-8a12-7036e4dee08f
-- title:
--   The optimal entitlement cap $c^\star(\varepsilon)$ for APS allocations
-- statement:
--   For a slack $\varepsilon$, a number $c$ is an admissible cap when every additive instance (with $n\ge2$ agents, finitely many goods, nonnegative additive valuations $v_i$ and entitlements $b_i$) satisfying
--
--   $$\sum_{i\in N}b_i<1-\varepsilon,\qquad 0<b_i\le c\quad(i\in N)$$
--
--   admits an integral allocation $(A_i)_{i\in N}$ with $v_i(A_i)\ge \mathrm{APS}_i(b_i)$ for every agent. The optimal cap is
--
--   $$c^\star(\varepsilon)=\sup\{c\in[0,1]: c \text{ is an admissible cap}\}.$$
--
--   The set always contains $0$, since no entitlement is $\le0$, and it is bounded by $1$, so the supremum is a genuine real number.
--
--   **Formalization Note** Instances are the live mission's `Instance` (real entitlements $0<b_i\le1$, nonnegative singleton values), the APS is its `target` at the original entitlement, and allocations are complete maps $\sigma$ from goods to agents; a partial allocation can always be completed without decreasing any value, so this changes no admissible cap.
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 5 (PDF p. 6), Theorem 4 (definition of c⋆(ε)); model §1.1, printed p. 2 (PDF p. 3); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack

/-- Theorem 4, PDF p. 6: the cap `c` has the universal property for slack `ε`: every additive
instance with `n ≥ 2` agents, `∑ b_i < 1 - ε` and `0 < b_i ≤ c` (positivity is part of
`Instance`) admits an allocation giving every agent her APS at her original entitlement. -/
def CapAdmissible (ε c : ℝ) : Prop :=
  ∀ (n m : ℕ) (X : Instance n m), 2 ≤ n → totalEntitlement X < 1 - ε →
    (∀ i, X.entitlement i ≤ c) →
    ∃ σ : Fin m → Fin n, ∀ i,
      target X i ≤ AnyPriceShare.Bidding.addVal (X.value i)
        (AnyPriceShare.Bidding.allocBundle σ i)

/-- Theorem 4, PDF p. 6: `c⋆(ε)`, the supremum of the admissible caps `c ∈ [0, 1]`. The set
always contains `0` (no entitlement is `≤ 0`) and is bounded above by `1`. -/
noncomputable def cStar (ε : ℝ) : ℝ :=
  sSup {c : ℝ | 0 ≤ c ∧ c ≤ 1 ∧ CapAdmissible ε c}

end FairShareAlmostAll.Slack.Supplement


