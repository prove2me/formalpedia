-- Prove2me | Definitions.Def_LiquidWelfareFPA_bench
-- name    : LiquidWelfareFPA_bench
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:25.244859+00:00
-- url     : https://prove2.me/theorems/c8ca56ca-9cf9-4b28-bfcc-9e0314778e0d
-- title:
--   Best fixed shading multiplier $\sup_{\lambda\in[0,1]}\hat U_i(\lambda)$
-- statement:
--   The benchmark against which player $i$'s utility is compared is the utility of the best fixed shading multiplier in hindsight:
--
--   $$\sup_{\lambda\in[0,1]}\hat U_i(\lambda).$$
--
--   **Formalization Note** For nonnegative budgets every term of $\hat U_i(\lambda)$ lies in $[0,1]$, so $0\le\hat U_i(\lambda)\le T$ and the supremum is a genuine supremum of a bounded nonempty family.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3.1, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_Uhat

namespace LiquidWelfareFPA

/-- **The benchmark `sup_{λ∈[0,1]} Û_i(λ)`: the best fixed shading multiplier.**
Fikioris & Tardos, arXiv:2210.07502v4, §3.1, p.6: "the benchmark with which we compare a player
i's utility is the best-fixed shading multiplier, i.e., sup_{λ∈[0,1]} Û_i(λ)".

**Formalization Note** `iSup` over the subtype `[0,1]`. For budgets `B_i ≥ 0` the family is
bounded (`0 ≤ Û_i(λ) ≤ T`, since every term is `v_it − b̂_it ∈ [0,1]` or `0`), so the `iSup` is
the true supremum and is not a junk value. -/
noncomputable def bench {n T : ℕ} (B : Fin n → ℝ) (o : Outcome n T)
    (win : Fin n → Fin T → ℝ → Prop) (i : Fin n) : ℝ :=
  ⨆ lam : Set.Icc (0 : ℝ) 1, Uhat B o win i lam

end LiquidWelfareFPA


