-- Prove2me | Definitions.Def_CompDesignBFM_IsTruthful
-- name    : CompDesignBFM_IsTruthful
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:07.183557+00:00
-- url     : https://prove2.me/theorems/d541eee5-78a6-4dec-b6ea-d3944dbfee3a
-- title:
--   Dominant-strategy truthfulness
-- statement:
--   A mechanism is **truthful** if, for every agent $i$, every true cost $t\ge0$, every misreport $z\ge0$ and every nonnegative profile $b_{-i}$ of the other bids,
--
--   $$u_i(z,b_{-i})\le u_i(t,b_{-i}).$$
--
--   Costs and misreports range over all of $[0,\infty)$, including values above the budget.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_util

namespace CompDesignBFM

/-- Dominant-strategy truthfulness (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3): for every agent `i`, every true cost
`t ≥ 0`, every misreport `z ≥ 0` and every nonnegative profile of the other bids, bidding `t` is at
least as good as bidding `z`.
**Formalization Note.** `b i` plays no role: both sides replace it through `Function.update`, so only
`b₋ᵢ` is kept. Costs and misreports range over all of `[0, ∞)`, including values above the budget. -/
def IsTruthful {n : ℕ} (m : Mechanism n) : Prop :=
  ∀ (i : Fin n) (t z : ℝ) (b : Fin n → ℝ), 0 ≤ t → 0 ≤ z → (∀ j, 0 ≤ b j) →
    util m i t (Function.update b i z) ≤ util m i t (Function.update b i t)

end CompDesignBFM


