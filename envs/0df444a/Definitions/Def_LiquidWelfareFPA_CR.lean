-- Prove2me | Definitions.Def_LiquidWelfareFPA_CR
-- name    : LiquidWelfareFPA_CR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:20.435096+00:00
-- url     : https://prove2.me/theorems/2553a2fa-0d4e-42ef-8ab6-ebe0b4d2578d
-- title:
--   Competitive ratio at most $\gamma$ with regret at most $\mathrm{Reg}$
-- statement:
--   Player $i$ has **budgeted quasi-linear utility** $U_i=V_i-P_i$ if $P_i\le B_i$, and $U_i=-\infty$ otherwise. She has **competitive ratio at most $\gamma$ and regret at most $\mathrm{Reg}$** if
--
--   $$U_i\ \ge\ \frac{\sup_{\lambda\in[0,1]}\hat U_i(\lambda)-\mathrm{Reg}}{\gamma}.$$
--
--   Because $U_i=-\infty$ fails every such inequality, this holds exactly when $P_i\le B_i$ and $V_i-P_i\ge(\sup_\lambda\hat U_i(\lambda)-\mathrm{Reg})/\gamma$.
--
--   This is the behavioural assumption of the paper: it replaces equilibrium play by a guarantee that learning algorithms for budgeted bidders can achieve.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3, p.6 and §3.1, p.6

import Mathlib
import Definitions.Def_LiquidWelfareFPA_bench

namespace LiquidWelfareFPA

/-- **"Player i has competitive ratio at most γ and regret at most Reg."**
Fikioris & Tardos, arXiv:2210.07502v4, §3, p.6: budgeted quasi-linear utility
`U_i = V_i − P_i` if `P_i ≤ B_i`, `−∞` otherwise; §3.1, p.6: player `i` has competitive ratio at
most `γ` and regret at most `Reg` if `U_i ≥ (sup_{λ∈[0,1]} Û_i(λ) − Reg)/γ`.

`CR B o win γ Reg i` holds when `P_i ≤ B_i` and `(sup_λ Û_i(λ) − Reg)/γ ≤ V_i − P_i`.

**Formalization Note** `U_i = −∞` when `P_i > B_i`, and `−∞` is never `≥` a real number, so the
inequality `U_i ≥ …` is exactly the conjunction above; no extended reals are used. -/
def CR {n T : ℕ} (B : Fin n → ℝ) (o : Outcome n T) (win : Fin n → Fin T → ℝ → Prop)
    (γ Reg : ℝ) (i : Fin n) : Prop :=
  o.pay i ≤ B i ∧ (bench B o win i - Reg) / γ ≤ o.val i - o.pay i

end LiquidWelfareFPA


