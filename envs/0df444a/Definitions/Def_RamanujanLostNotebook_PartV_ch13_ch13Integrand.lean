-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch13_ch13Integrand
-- name    : RamanujanLostNotebook_PartV_ch13_ch13Integrand
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T18:28:31.881248+00:00
-- url     : https://prove2.me/theorems/167aab7a-9abf-49fd-b4ea-d846e385fc5e
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 13: ch13Integrand
-- statement:
--   The integrand of Ramanujan's Mordell-type integral on page 202 of the Lost Notebook
--   (Entry 13.1.1, p. 292; Theorem 13.1.1, (13.1.6), p. 293):
--   `e^{-π n x^2 / 3} cos(π t x) / (e^{2π x / 3} + 1 + e^{-2π x / 3})`,
--   as a complex-valued function of the real variable `x`, with complex parameters `n`, `t`.
--   The arguments are ordered `ch13Integrand n t x`.
--
--   Domain: every `n`, `t`, `x` (the denominator is `1 + 2 cosh(2π x / 3) ≥ 3` for real `x`).
--   It is integrable over `(0, ∞)` when `0 < n.re`; integrability is asserted in the statements,
--   not here.
--   Reference: `n = 1`, `t = 3/10`, `x = 1/2`: `0.16325791437932799…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 13.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- The integrand of Ramanujan's Mordell-type integral on page 202 of the Lost Notebook
(Entry 13.1.1, p. 292; Theorem 13.1.1, (13.1.6), p. 293):
`e^{-π n x^2 / 3} cos(π t x) / (e^{2π x / 3} + 1 + e^{-2π x / 3})`,
as a complex-valued function of the real variable `x`, with complex parameters `n`, `t`.
The arguments are ordered `ch13Integrand n t x`.

Domain: every `n`, `t`, `x` (the denominator is `1 + 2 cosh(2π x / 3) ≥ 3` for real `x`).
It is integrable over `(0, ∞)` when `0 < n.re`; integrability is asserted in the statements,
not here.
Reference: `n = 1`, `t = 3/10`, `x = 1/2`: `0.16325791437932799…`. -/
noncomputable def ch13Integrand (n t : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * n * (x : ℂ) ^ 2 / 3)) * Complex.cos ((Real.pi : ℂ) * t * (x : ℂ)) /
    (Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) / 3) + 1 + Complex.exp (-(2 * (Real.pi : ℂ) * (x : ℂ) / 3)))

end RamanujanLostNotebook.PartV


