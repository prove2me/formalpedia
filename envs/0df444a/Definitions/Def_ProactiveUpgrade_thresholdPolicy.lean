-- Prove2me | Definitions.Def_ProactiveUpgrade_thresholdPolicy
-- name    : ProactiveUpgrade_thresholdPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:27.316512+00:00
-- url     : https://prove2.me/theorems/b4c40a0e-2c91-4d06-ae81-83bf5ba7a795
-- title:
--   The two-threshold upgrade policy of Theorem 3
-- statement:
--   The **two-threshold policy** offers a free upgrade to a customer who requests product $i\in\{1,\dots,m-1\}$ in period $t$ with inventory $x$
--
--   1. if $x_i>0$: exactly when $x_{i+1}\ge\gamma_{i,t}(x_{-(i+1)})$;
--   2. if $x_i=0$: exactly when $x_{i+1}\ge\eta_{i,t}(x_{-(i+1)})$;
--
--   and never offers an upgrade to a customer who requests product $m$. Theorem 3 asserts that this policy is optimal.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Theorem 3, p.25

import Mathlib
import Definitions.Def_ProactiveUpgrade_Policy
import Definitions.Def_ProactiveUpgrade_gammaThr
import Definitions.Def_ProactiveUpgrade_etaThr

namespace ProactiveUpgrade

/-- **The two-threshold policy of Theorem 3** (Chen et al., SSRN 3777846, p.25): for a customer
requesting product `i < m` in period `t`, offer a free upgrade iff `x_{i+1} ≥ γ_{i,t}(x_{−(i+1)})`
when `xᵢ > 0`, and iff `x_{i+1} ≥ η_{i,t}(x_{−(i+1)})` when `xᵢ = 0`. No offer to a customer
requesting the last product. -/
def thresholdPolicy {m : ℕ} (M : Model m) (T : ℕ) : Policy m :=
  fun t x i => ∃ h : i.val + 1 < m,
    (0 < x i ∧ gammaThr M T t x i h ≤ ((x (succIdx i h) : ℕ) : ℕ∞)) ∨
      (x i = 0 ∧ etaThr M T t x i h ≤ ((x (succIdx i h) : ℕ) : ℕ∞))

end ProactiveUpgrade


