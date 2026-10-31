-- Prove2me | Definitions.Def_ComplementarySourcing_ModelM_supplierProfit
-- name    : ComplementarySourcing_ModelM_supplierProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:32.480466+00:00
-- url     : https://prove2.me/theorems/b26d6cbe-25d7-4c3d-9cd5-8f0bece00ea6
-- title:
--   Supplier's expected profit in Model (M)
-- statement:
--   With $f(\epsilon)$ the supplier's effort at realized $\epsilon$,
--
--   $$\pi_s=\sum_{i=1}^2p_i\big(w\,d(x_m,f(\epsilon_i),\epsilon_i)-\tfrac12f(\epsilon_i)^2\big),\qquad p_1=p_2=\tfrac12.$$
--
--   The second mover pays its effort cost in each realization, so the cost sits inside the expectation.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), pp.8, 12–14

import Mathlib
import Definitions.Def_ComplementarySourcing_supplierStageProfit

namespace ComplementarySourcing

/-- The second mover's expected profit in Model (M), `π_s = Σ_{i=1,2} p_i (w d_i − ½ f(ϵ_i)²)`:
the expectation over `ϵ` of the objective of (2) at the response `f`, with `p₁ = p₂ = ½`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), pp.8, 12–14 (PDF 8, 12–14).

**Formalization Note.** The second mover pays its cost in each realization, so the cost sits
inside the expectation. -/
noncomputable def ModelM.supplierProfit (μ α ε₀ σ xm w : ℝ) (f : ℝ → ℝ) : ℝ :=
  1 / 2 * supplierStageProfit μ α xm w (ε₀ + σ) (f (ε₀ + σ)) +
    1 / 2 * supplierStageProfit μ α xm w (ε₀ - σ) (f (ε₀ - σ))

end ComplementarySourcing


