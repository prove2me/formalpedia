-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_expectedSupplierProfit
-- name    : ComplementarySourcing_Supplement_expectedSupplierProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:43:32.47801+00:00
-- url     : https://prove2.me/theorems/a40ddfb2-f437-4050-829f-47f913b4ccab
-- title:
--   The second-moving supplier's expected profit
-- statement:
--   When the supplier moves second and observes the realized market taste $\epsilon=\epsilon_i$ (probability $p_i$) before investing, and responds with effort $f(\epsilon_i)$ to the manufacturer's effort $x_m$ at wholesale price $w$, its expected profit is
--
--   $$\pi_s=\sum_i p_i\Big(w\,d\big(x_m,f(\epsilon_i),\epsilon_i\big)-\tfrac12f(\epsilon_i)^2\Big).$$
--
--   It is the supplier's profit $\pi_s^M$ in the fixed-wholesale-price comparisons of Theorems 3 and A3.
--
--   **Formalization Note** The second mover pays its effort cost in each realization, so the cost sits inside the expectation.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), eq. (2), p.8; §A5, p.A22

import Mathlib
import Definitions.Def_ComplementarySourcing_supplierStageProfit

namespace ComplementarySourcing

/-- The second-moving supplier's expected profit when it observes the realized risk,
`π_s = Σ_i p_i (w d(x_m, f(ϵ_i), ϵ_i) − ½ f(ϵ_i)²)`, for the manufacturer's effort `x_m`, wholesale
price `w` and the supplier's response `f` to each realization `ϵ_i`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), eq. (2), p.8 (PDF 8), with the expectation over
`ϵ = ϵ_i` w.p. `p_i` of §A1 and §A5, pp.A1, A22 (PDF 29, 50).

**Formalization Note.** The second mover pays its cost in each realization, so the cost sits
inside the expectation. -/
noncomputable def Supplement.expectedSupplierProfit {m : ℕ} (μ α xm w : ℝ) (ε p : Fin m → ℝ)
    (f : Fin m → ℝ) : ℝ :=
  ∑ i, p i * supplierStageProfit μ α xm w (ε i) (f i)

end ComplementarySourcing


