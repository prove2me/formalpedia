-- Prove2me | Definitions.Def_LiquidWelfareFPA_lam2
-- name    : LiquidWelfareFPA_lam2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:29.778025+00:00
-- url     : https://prove2.me/theorems/0eaf3465-5100-4ad4-bcaf-9615af8f0475
-- title:
--   The multiplier $\lambda_2=\gamma W(-e^{-2/\gamma}/\gamma)+1$
-- statement:
--   For a competitive ratio $\gamma\ge1$,
--
--   $$\lambda_2=\gamma\,W\!\left(-\frac{e^{-2/\gamma}}{\gamma}\right)+1,$$
--
--   where $W$ is the principal branch of the Lambert $W$ function. It solves $1+1/\lambda=\gamma/(c(\lambda)\lambda)$ and is the multiplier used in the proof of Theorem 4.2 for $\gamma\ge\gamma_0$.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, p.10

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lambertW

namespace LiquidWelfareFPA

/-- **The multiplier `λ₂ = γ W(−e^{−2/γ}/γ) + 1`.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, p.10: "we solve the equation
1 + 1/λ = γ/(c(λ)λ), set λ2 = γW(−e^{−2/γ}/γ) + 1, where W(·) is the Lambert W function".

`W` is the principal branch `lambertW`. For `γ ≥ 1` the argument `−e^{−2/γ}/γ` lies in
`(−1/e, 0)`. -/
noncomputable def lam2 (γ : ℝ) : ℝ :=
  γ * lambertW (-Real.exp (-2 / γ) / γ) + 1

end LiquidWelfareFPA


