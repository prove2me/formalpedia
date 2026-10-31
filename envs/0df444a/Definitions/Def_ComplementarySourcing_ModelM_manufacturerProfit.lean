-- Prove2me | Definitions.Def_ComplementarySourcing_ModelM_manufacturerProfit
-- name    : ComplementarySourcing_ModelM_manufacturerProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:32.110999+00:00
-- url     : https://prove2.me/theorems/fe1c6172-22e9-4f6a-83e1-a305fabc4528
-- title:
--   Manufacturer's expected profit in Model (M)
-- statement:
--   With $f(\epsilon)$ the supplier's effort at realized market risk $\epsilon$,
--
--   $$\pi_m(x_m,w)=(r-w)\sum_{i=1}^2p_i\,d(x_m,f(\epsilon_i),\epsilon_i)-\tfrac12x_m^2,\qquad p_1=p_2=\tfrac12.$$
--
--   The first mover pays its effort cost once, outside the expectation.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13

import Mathlib
import Definitions.Def_ComplementarySourcing_demand

namespace ComplementarySourcing

/-- The first mover's expected profit in Model (M),
`π_m(x_m, w) = (r − w) Σ_{i=1,2} p_i d(x_m, f(ϵ_i), ϵ_i) − ½ x_m²` with `ϵ₁ = ϵ₀ + σ`, `ϵ₂ = ϵ₀ − σ`,
`p₁ = p₂ = ½`, where `f` gives the supplier's effort at each realized `ϵ`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.13 (PDF 13).

**Formalization Note.** The first mover's cost is paid once, outside the two-point sum, which is
the page's explicit sum. -/
noncomputable def ModelM.manufacturerProfit (μ α r ε₀ σ xm w : ℝ) (f : ℝ → ℝ) : ℝ :=
  (r - w) * (1 / 2 * demand μ α xm (f (ε₀ + σ)) (ε₀ + σ) +
    1 / 2 * demand μ α xm (f (ε₀ - σ)) (ε₀ - σ)) - 1 / 2 * xm ^ 2

end ComplementarySourcing


