-- Prove2me | Definitions.Def_ComplementarySourcing_candidateProfit1
-- name    : ComplementarySourcing_candidateProfit1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:14.807127+00:00
-- url     : https://prove2.me/theorems/57c3b4b6-b5a9-4f34-bf09-802517cfbadd
-- title:
--   The candidate profit $\pi_1$
-- statement:
--   $$\pi_1=\Big(r-\frac{\epsilon_1-x_1}{\mu(1+\alpha x_1)^2}\Big)\mu\epsilon_0-\tfrac12x_1^2,\qquad\epsilon_1=\epsilon_0+\sigma.$$
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13, Proposition 2

import Mathlib
import Definitions.Def_ComplementarySourcing_wholesaleCandidate

namespace ComplementarySourcing

/-- `π₁ = (r − (ϵ₁ − x₁) / (µ(1 + αx₁)²)) µ ϵ₀ − ½ x₁²`, with `ϵ₁ = ϵ₀ + σ`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Proposition 2, p.13 (PDF 13). -/
noncomputable def candidateProfit1 (μ α r ε₀ σ x₁ : ℝ) : ℝ :=
  (r - wholesaleCandidate μ α (ε₀ + σ) x₁) * μ * ε₀ - 1 / 2 * x₁ ^ 2

end ComplementarySourcing


