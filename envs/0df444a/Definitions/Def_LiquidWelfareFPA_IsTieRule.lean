-- Prove2me | Definitions.Def_LiquidWelfareFPA_IsTieRule
-- name    : LiquidWelfareFPA_IsTieRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:13.60173+00:00
-- url     : https://prove2.me/theorems/65641d94-38d7-41f2-b828-d2f6cddba31e
-- title:
--   Tie-breaking rule for "bid $b$ wins against $d_{it}$"
-- statement:
--   A **tie rule** is a predicate $\mathrm{win}_{it}(b)$, saying whether a bid $b$ of player $i$ in round $t$ would win against the highest competing bid $d_{it}$, such that
--
--   1. every bid $b>d_{it}$ wins, and
--   2. every bid $b<d_{it}$ loses.
--
--   At $b=d_{it}$ the rule is arbitrary and may depend on $i$ and $t$. The paper's benchmark is defined for any such rule ("Our results hold for any tie-breaking rule").
--
--   **Formalization Note** The rule is a free predicate, so every statement using it holds for every tie rule. It is unrelated to how the actual outcome broke its own ties.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3.1, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_dcomp

namespace LiquidWelfareFPA

/-- **A tie-breaking rule for "bid b wins against d_it".**
Fikioris & Tardos, arXiv:2210.07502v4, §3.1, p.6: the benchmark uses "1[bid b̂_iτ wins against
d_iτ]", and "Our results hold for any tie-breaking rule, which is why we do not explicitly state
one above."

`win i t b` says that a bid `b` of player `i` in round `t` would win against the highest
competing bid `d_it`. It is a tie rule when every bid above `d_it` wins and every bid below
`d_it` loses; at `b = d_it` it is arbitrary (and may depend on `i` and `t`).

**Formalization Note** The rule is a free predicate, so the theorems hold for every tie rule. It is
independent of how the actual allocation `o.w` broke its own ties. -/
def IsTieRule {n T : ℕ} (o : Outcome n T) (win : Fin n → Fin T → ℝ → Prop) : Prop :=
  ∀ i t b, (dcomp o i t < b → win i t b) ∧ (b < dcomp o i t → ¬ win i t b)

end LiquidWelfareFPA


