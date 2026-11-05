-- Prove2me | Definitions.Def_LiquidWelfareFPA_bhat
-- name    : LiquidWelfareFPA_bhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:30.5353+00:00
-- url     : https://prove2.me/theorems/8c42c149-2d98-42dd-a037-cd91b54ca14a
-- title:
--   Budget-capped shaded bid $\hat b_{it}(\lambda)$
-- statement:
--   Fix a player $i$, a shading multiplier $\lambda$ and a tie rule. The bid player $i$ would have placed in round $t$ had she bid $\lambda$ times her value every round, up to her remaining budget, is defined recursively by
--
--   $$\hat b_{it}(\lambda)=\min\Big\{\lambda v_{it},\ B_i-\sum_{\tau=1}^{t-1}\hat b_{i\tau}(\lambda)\,\mathbb 1\big[\text{bid }\hat b_{i\tau}\text{ wins against }d_{i\tau}\big]\Big\}.$$
--
--   That is, every round her bid is the minimum of $\lambda v_{it}$ and her remaining budget; she pays it only in the rounds it wins. Wins are judged against the competing bids $d_{i\tau}$ the other players actually used.
--
--   **Formalization Note** The remaining budget $R_k$ is defined by recursion on the 0-based round index: $R_0=B_i$ and $R_{k+1}=R_k-\hat b_{ik}\,\mathbb 1[\text{win}]$.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3.1, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_Outcome

namespace LiquidWelfareFPA

variable {n T : ℕ}

open Classical in
/-- Remaining budget of player `i` after the first `k` rounds when she bids with multiplier `λ`:
`R_0 = B_i` and, in round `k` (0-based), she bids `b = min{λ v_ik, R_k}` and
`R_{k+1} = R_k − b · 1[b wins]`. Rounds `k ≥ T` change nothing. -/
noncomputable def remBudget (B : Fin n → ℝ) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (i : Fin n) (lam : ℝ) : ℕ → ℝ
  | 0 => B i
  | k + 1 =>
    if h : k < T then
      if win i ⟨k, h⟩ (min (lam * o.v i ⟨k, h⟩) (remBudget B o win i lam k)) then
        remBudget B o win i lam k - min (lam * o.v i ⟨k, h⟩) (remBudget B o win i lam k)
      else remBudget B o win i lam k
    else remBudget B o win i lam k

/-- **The budget-capped shaded bid `b̂_it(λ)`.**
Fikioris & Tardos, arXiv:2210.07502v4, §3.1, p.6:
`b̂_it(λ) = min{ λ v_it , B_i − ∑_{τ=1}^{t−1} b̂_iτ(λ) 1[bid b̂_iτ wins against d_iτ] }`,
"i.e., every round t player i's bid is the minimum of λv_it and her remaining budget".

`bhat B o win i λ t = min (λ · v_it) (remBudget … t)`, where `remBudget` is the recursion above;
wins are decided by the tie rule `win` against the *original* competing bids (p.6, "We
emphasize that d_it … is calculated using the bids that the other players used originally").

**Formalization Note** Rounds are `Fin T`; the recursion runs over the 0-based round index in `ℕ`. -/
noncomputable def bhat (B : Fin n → ℝ) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (i : Fin n) (lam : ℝ) (t : Fin T) : ℝ :=
  min (lam * o.v i t) (remBudget B o win i lam t.val)

end LiquidWelfareFPA


