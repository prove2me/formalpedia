-- Prove2me | Definitions.Def_ComplementarySourcing_candidateProfit2
-- name    : ComplementarySourcing_candidateProfit2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:38.740999+00:00
-- url     : https://prove2.me/theorems/d427f654-a8a0-45fe-9791-31ab0f450e8a
-- title:
--   The candidate profit $\pi_2$
-- statement:
--   $$\pi_2=\Big(r-\frac{\epsilon_2-x_2}{\mu(1+\alpha x_2)^2}\Big)\mu\epsilon_2-\tfrac12x_2^2,\qquad\epsilon_2=\epsilon_0-\sigma.$$
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13, Proposition 2

import Mathlib
import Definitions.Def_ComplementarySourcing_wholesaleCandidate

namespace ComplementarySourcing

/-- `π₂ = (r − (ϵ₂ − x₂) / (µ(1 + αx₂)²)) µ ϵ₂ − ½ x₂²`, with `ϵ₂ = ϵ₀ − σ`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Proposition 2, p.13 (PDF 13). -/
noncomputable def candidateProfit2 (μ α r ε₀ σ x₂ : ℝ) : ℝ :=
  (r - wholesaleCandidate μ α (ε₀ - σ) x₂) * μ * (ε₀ - σ) - 1 / 2 * x₂ ^ 2

end ComplementarySourcing


