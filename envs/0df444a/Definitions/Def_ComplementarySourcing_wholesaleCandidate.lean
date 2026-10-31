-- Prove2me | Definitions.Def_ComplementarySourcing_wholesaleCandidate
-- name    : ComplementarySourcing_wholesaleCandidate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:31.85911+00:00
-- url     : https://prove2.me/theorems/1355bd8a-8308-478a-97c0-af9d22eb5221
-- title:
--   The candidate wholesale price
-- statement:
--   For a market-risk level $\epsilon$ and an effort $x$,
--
--   $$w(\epsilon,x)=\frac{\epsilon-x}{\mu(1+\alpha x)^2}.$$
--
--   This is the price at which the second mover's response just brings the user experience up to $\epsilon$.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13, Proposition 2

import Mathlib

namespace ComplementarySourcing

/-- The candidate wholesale price `(ϵ − x) / (µ (1 + αx)²)`, which appears at `(ϵ_k, x_k)` in
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Proposition 2, p.13 (PDF 13), and Proposition 3, p.14 (PDF 14). -/
noncomputable def wholesaleCandidate (μ α ε x : ℝ) : ℝ :=
  (ε - x) / (μ * (1 + α * x) ^ 2)

end ComplementarySourcing


