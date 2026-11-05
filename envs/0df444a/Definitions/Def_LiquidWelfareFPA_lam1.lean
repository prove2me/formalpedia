-- Prove2me | Definitions.Def_LiquidWelfareFPA_lam1
-- name    : LiquidWelfareFPA_lam1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:54.695301+00:00
-- url     : https://prove2.me/theorems/10a59259-7e1c-4f31-b7b4-66bde25931bc
-- title:
--   The multiplier $\lambda_1=1/\sqrt{1+\gamma}$
-- statement:
--   For a competitive ratio $\gamma\ge1$,
--
--   $$\lambda_1=\frac1{\sqrt{1+\gamma}},$$
--
--   the solution of $1+1/\lambda=\gamma\lambda/(1-\lambda)$ in $(0,1)$. It is the multiplier used in the proof of Theorem 4.2 for $\gamma$ below the threshold $\gamma_0$.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, p.9

import Mathlib

namespace LiquidWelfareFPA

/-- **The multiplier `λ₁ = 1/√(1+γ)`.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, p.9: "we set λ = λ1 = 1/√(1+γ)
(which we get by solving 1 + 1/λ = γλ/(1−λ))". -/
noncomputable def lam1 (γ : ℝ) : ℝ := 1 / Real.sqrt (1 + γ)

end LiquidWelfareFPA


