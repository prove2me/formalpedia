-- Prove2me | Definitions.Def_LiquidWelfareFPA_Uhat
-- name    : LiquidWelfareFPA_Uhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:37.196534+00:00
-- url     : https://prove2.me/theorems/571c2230-b7e0-4d25-b970-ca881c57a8f7
-- title:
--   Utility $\hat U_i(\lambda)$ of a fixed shading multiplier
-- statement:
--   The utility of player $i$ had she bid with the fixed shading multiplier $\lambda$ in every round, against the competing bids that actually occurred, is
--
--   $$\hat U_i(\lambda)=\sum_{t=1}^T\big(v_{it}-\hat b_{it}(\lambda)\big)\,\mathbb 1\big[\text{bid }\hat b_{it}(\lambda)\text{ wins against }d_{it}\big],$$
--
--   with the budget-capped bids $\hat b_{it}(\lambda)$ and a given tie rule.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3.1, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_bhat

namespace LiquidWelfareFPA

open Classical in
/-- **Utility `Û_i(λ)` of the fixed shading multiplier `λ`.**
Fikioris & Tardos, arXiv:2210.07502v4, §3.1, p.6:
`Û_i(λ) = ∑_{t=1}^T (v_it − b̂_it(λ)) 1[bid b̂_it wins against d_it]`.

The sum is over rounds `t`, with the budget-capped bids `bhat` and the tie rule `win`. -/
noncomputable def Uhat {n T : ℕ} (B : Fin n → ℝ) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (i : Fin n) (lam : ℝ) : ℝ :=
  ∑ t, if win i t (bhat B o win i lam t) then o.v i t - bhat B o win i lam t else 0

end LiquidWelfareFPA


