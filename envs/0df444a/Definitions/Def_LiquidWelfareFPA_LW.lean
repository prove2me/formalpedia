-- Prove2me | Definitions.Def_LiquidWelfareFPA_LW
-- name    : LiquidWelfareFPA_LW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:15.242571+00:00
-- url     : https://prove2.me/theorems/ff78a354-cadc-465b-8d7f-4fb89ac0865c
-- title:
--   Liquid welfare $\mathrm{LW}=\sum_i\min\{B_i,V_i\}$
-- statement:
--   Given budgets $B_1,\dots,B_n$ and an outcome with allocated values $V_1,\dots,V_n$, the contribution of player $i$ to the **liquid welfare** is $\mathrm{LW}_i=\min\{B_i,V_i\}$, and the liquid welfare of the outcome is
--
--   $$\mathrm{LW}=\sum_{i=1}^n\min\{B_i,V_i\}.$$
--
--   Liquid welfare is the welfare measure for budget-constrained buyers: a buyer's value counts only up to the amount she can pay.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_Outcome

namespace LiquidWelfareFPA

/-- **Liquid welfare `LW = ∑_i min{B_i, V_i}`.**
Fikioris & Tardos, arXiv:2210.07502v4, §3, p.6: "the contribution of player i to the liquid
welfare is LW_i = min{B_i, V_i} and the resulting liquid welfare is LW = ∑_{i∈[n]} LW_i".

`B i` is player `i`'s budget and `o.val i` her allocated value in the outcome `o`. -/
def LW {n T : ℕ} (B : Fin n → ℝ) (o : Outcome n T) : ℝ :=
  ∑ i, min (B i) (o.val i)

end LiquidWelfareFPA


