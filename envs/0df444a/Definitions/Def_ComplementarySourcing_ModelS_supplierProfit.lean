-- Prove2me | Definitions.Def_ComplementarySourcing_ModelS_supplierProfit
-- name    : ComplementarySourcing_ModelS_supplierProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:40.714363+00:00
-- url     : https://prove2.me/theorems/4f2ca433-4364-443b-bca4-02be209d2f1c
-- title:
--   Supplier's expected profit in Model (S)
-- statement:
--   With $f(\epsilon)$ the manufacturer's effort at realized $\epsilon$,
--
--   $$w\sum_{i=1}^2p_i\,d(f(\epsilon_i),x_s,\epsilon_i)-\tfrac12x_s^2,\qquad p_1=p_2=\tfrac12.$$
--
--   The supplier as first mover pays its effort cost once, outside the expectation.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.14

import Mathlib
import Definitions.Def_ComplementarySourcing_demand

namespace ComplementarySourcing

/-- The first mover's expected profit in Model (S),
`w Σ_{i=1,2} p_i d(f(ϵ_i), x_s, ϵ_i) − ½ x_s²`, with `ϵ₁ = ϵ₀ + σ`, `ϵ₂ = ϵ₀ − σ`, `p₁ = p₂ = ½`, where
`f` gives the manufacturer's effort at each realized `ϵ`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.14 (PDF 14).

**Formalization Note.** Defined on its own, not by relabeling Model (M): the page's `w' = r − w`
identity is Corollary 3. -/
noncomputable def ModelS.supplierProfit (μ α ε₀ σ xs w : ℝ) (f : ℝ → ℝ) : ℝ :=
  w * (1 / 2 * demand μ α (f (ε₀ + σ)) xs (ε₀ + σ) +
    1 / 2 * demand μ α (f (ε₀ - σ)) xs (ε₀ - σ)) - 1 / 2 * xs ^ 2

end ComplementarySourcing


