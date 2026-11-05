-- Prove2me | Definitions.Def_LiquidWelfareFPA_hfun
-- name    : LiquidWelfareFPA_hfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:53.526453+00:00
-- url     : https://prove2.me/theorems/20f44c7b-5270-4344-ac25-b127632165a8
-- title:
--   The function $h(\gamma)=1+\sqrt{\gamma+1}+\gamma\sqrt{\gamma+1}\ln(1-1/\sqrt{\gamma+1})$
-- statement:
--   For $\gamma\ge1$ let
--
--   $$h(\gamma)=1+\sqrt{\gamma+1}+\gamma\sqrt{\gamma+1}\,\ln\!\Big(1-\frac1{\sqrt{\gamma+1}}\Big).$$
--
--   Its root $\gamma_0$ is where the two candidate multipliers of the proof of Theorem 4.2 exchange roles: $h(\gamma)=0$ is the equation $1+1/\lambda_1=\gamma/(c(\lambda_1)\lambda_1)$.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, pp.21–22

import Mathlib

namespace LiquidWelfareFPA

/-- **The function `h(γ) = 1 + √(γ+1) + γ√(γ+1) ln(1 − 1/√(γ+1))` whose root is `γ₀`.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, pp.21–22: "let γ0 be the solution to
1 + 1/λ1 = γ/(c(λ1)λ1) ⟺ 1 + √(γ+1) = −γ√(γ+1) ln(1 − 1/√(γ+1))", and "1 + √(γ+1) +
γ√(γ+1) ln(1 − 1/√(γ+1)) is strictly decreasing for γ ≥ 1".

**Formalization Note** `ln` is `Real.log`. For `γ ≥ 1` the argument of the logarithm lies in
`(0,1)`. -/
noncomputable def hfun (γ : ℝ) : ℝ :=
  1 + Real.sqrt (γ + 1) + γ * Real.sqrt (γ + 1) * Real.log (1 - 1 / Real.sqrt (γ + 1))

end LiquidWelfareFPA


