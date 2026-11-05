-- Prove2me | Definitions.Def_LiquidWelfareFPA_gamma0
-- name    : LiquidWelfareFPA_gamma0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:32.691006+00:00
-- url     : https://prove2.me/theorems/2c22260c-905d-4de5-9886-845e0bfff662
-- title:
--   The threshold $\gamma_0\approx1.73$
-- statement:
--   The threshold $\gamma_0$ is the root of $h$ on $[1,\infty)$:
--
--   $$\gamma_0=\inf\{\gamma\ge1:\ h(\gamma)\le0\}.$$
--
--   Because $h$ is continuous and strictly decreasing on $[1,\infty)$ with $h(1)>0$ and $h(\gamma)\to-\infty$, this is the unique solution of $1+1/\lambda_1=\gamma/(c(\lambda_1)\lambda_1)$ with $\gamma\ge1$; numerically $\gamma_0=1.72511\ldots$
--
--   **Formalization Note** $\gamma_0$ is defined exactly rather than by the rounded value $1.73$ of the text. The milestone on the $\lambda_1$ branch states that $h(\gamma_0)=0$, $\gamma_0\ge1$ and that the root is unique, so a wrong definition would make that milestone false.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, pp.21–22

import Mathlib
import Definitions.Def_LiquidWelfareFPA_hfun

namespace LiquidWelfareFPA

/-- **The threshold `γ₀ ≈ 1.73`.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, pp.21–22: "let γ0 be the solution to
1 + 1/λ1 = γ/(c(λ1)λ1)", "Numerically we can solve the above equation to see that γ0 ≈ 1.73."

`gamma0 = inf {γ ≥ 1 : h(γ) ≤ 0}`, with `h = hfun`. Since `h` is continuous and strictly
decreasing on `[1, ∞)` with `h(1) > 0` and `h → −∞`, this is the unique root of `h` on `[1, ∞)`
(numerically `γ₀ = 1.72511…`).

**Formalization Note** `γ₀` is defined exactly, not as the rounded `1.73` of the text (at
`γ = 1.73 > γ₀` the inequality the text attributes to `γ ≤ 1.73` fails). `sInf` of an empty set
would be `0`; the set is nonempty, and the milestone on the `λ₁` branch states `h(γ₀) = 0`,
`1 ≤ γ₀` and uniqueness, so a wrong value would make that statement false, not trivial. -/
noncomputable def gamma0 : ℝ := sInf {γ : ℝ | 1 ≤ γ ∧ hfun γ ≤ 0}

end LiquidWelfareFPA


