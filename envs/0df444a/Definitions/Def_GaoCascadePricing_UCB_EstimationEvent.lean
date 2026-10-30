-- Prove2me | Definitions.Def_GaoCascadePricing_UCB_EstimationEvent
-- name    : GaoCascadePricing_UCB_EstimationEvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:15:55.060188+00:00
-- url     : https://prove2.me/theorems/d8d3a739-f0bb-4788-9fc9-8958655eaddb
-- title:
--   Simultaneous bad estimation event at calendar time
-- statement:
--   At deterministic calendar time $t=n+1$, the bad event is the union of all absolute estimation errors at least $\sqrt{2\ln(t)/m}$, where $m$ is the corresponding examination, click, nonclick or click-without-purchase count. Both product-price parameter families range over every $j,k$; the two continuation families range only over nonterminal products. All four comparison radii are uncapped and the comparison is non-strict, as on p. 17.
--
--   An unavailable zero-count comparison contributes no event. This specifies the expression outside its printed domain without conditioning on the completion of initialization. On every fully initialized history this is exactly the source event $A_t$. The true parameter is fixed over time.
--
--   **Formalization Note.** The event is a predicate on finite histories, with its probability computed by the finite trajectory law. At $t=1$ every count is zero and the bad event is empty.
-- source:
--   Gao, Jasin, Najafi and Zhang (2022), Joint Learning and Optimization for Multi-Product Pricing (and Ranking) Under a General Cascade Click Model, DOI https://doi.org/10.1287/mnsc.2021.4246; published basis, supplied manuscript-paginated PDF; §4.2, p. 17

import Definitions.Def_GaoCascadePricing_UCB_Algorithm

namespace GaoCascadePricing.UCB

/-- Undefined zero-count comparisons contribute no error event. All available comparisons
use the printed non-strict inequality and uncapped radius, even during initialization. -/
def BadEvent {J K n : ℕ} (θ : Cascade J K) (h : History J K n) : Prop :=
  (∃ j k, (0 < ne h j k ∧
    radius (n + 1) (ne h j k) ≤ |(estimate h).beta j k - θ.beta j k|) ∨
    (0 < nc h j k ∧
    radius (n + 1) (nc h j k) ≤ |(estimate h).alpha j k - θ.alpha j k|)) ∨
  (∃ j : Fin J, j.val + 1 < J ∧
    ((0 < ng h j ∧ radius (n + 1) (ng h j) ≤ |(estimate h).gamma j - θ.gamma j|) ∨
     (0 < nz h j ∧ radius (n + 1) (nz h j) ≤ |(estimate h).zeta j - θ.zeta j|)))

end GaoCascadePricing.UCB


