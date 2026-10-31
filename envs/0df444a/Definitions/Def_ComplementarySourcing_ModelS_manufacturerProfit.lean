-- Prove2me | Definitions.Def_ComplementarySourcing_ModelS_manufacturerProfit
-- name    : ComplementarySourcing_ModelS_manufacturerProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:24.69376+00:00
-- url     : https://prove2.me/theorems/899f0671-f924-41a6-af3b-6f4fe91b8893
-- title:
--   Manufacturer's expected profit in Model (S)
-- statement:
--   With $f(\epsilon)$ the manufacturer's effort at realized $\epsilon$,
--
--   $$\sum_{i=1}^2p_i\big((r-w)\,d(f(\epsilon_i),x_s,\epsilon_i)-\tfrac12f(\epsilon_i)^2\big),\qquad p_1=p_2=\tfrac12.$$
--
--   The second mover pays its effort cost in each realization.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.14

import Mathlib
import Definitions.Def_ComplementarySourcing_manufacturerStageProfit

namespace ComplementarySourcing

/-- The second mover's expected profit in Model (S),
`Σ_{i=1,2} p_i ((r − w) d_i − ½ f(ϵ_i)²)`, with `p₁ = p₂ = ½`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.14 (PDF 14).

**Formalization Note.** The second mover's unit margin is `r − w`, and its cost sits inside the
expectation. -/
noncomputable def ModelS.manufacturerProfit (μ α r ε₀ σ xs w : ℝ) (f : ℝ → ℝ) : ℝ :=
  1 / 2 * manufacturerStageProfit μ α r xs w (ε₀ + σ) (f (ε₀ + σ)) +
    1 / 2 * manufacturerStageProfit μ α r xs w (ε₀ - σ) (f (ε₀ - σ))

end ComplementarySourcing


