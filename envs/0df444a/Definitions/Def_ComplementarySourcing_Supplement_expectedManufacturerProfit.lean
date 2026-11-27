-- Prove2me | Definitions.Def_ComplementarySourcing_Supplement_expectedManufacturerProfit
-- name    : ComplementarySourcing_Supplement_expectedManufacturerProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:43:58.486929+00:00
-- url     : https://prove2.me/theorems/28589329-ca3e-53db-9558-42d6a1c5e265
-- title:
--   The second-moving manufacturer's expected profit
-- statement:
--   When the manufacturer moves second and observes the realized market taste $\epsilon=\epsilon_i$ (probability $p_i$), and responds with effort $f(\epsilon_i)$ to the supplier's effort $x_s$ at wholesale price $w$, its expected profit is
--
--   $$\pi_m=\sum_i p_i\Big((r-w)\,d\big(f(\epsilon_i),x_s,\epsilon_i\big)-\tfrac12f(\epsilon_i)^2\Big).$$
--
--   It is $\pi_m^{S}$ in Theorems 3, A1 and A3.
--
--   **Formalization Note** The second mover's cost sits inside the expectation.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A1.2, p.A5; §A5, p.A23

import Mathlib
import Definitions.Def_ComplementarySourcing_manufacturerStageProfit

namespace ComplementarySourcing

/-- The second-moving manufacturer's expected profit when it observes the realized risk,
`π_m = Σ_i p_i ((r − w) d(f(ϵ_i), x_s, ϵ_i) − ½ f(ϵ_i)²)`, for the supplier's effort `x_s`,
wholesale price `w` and the manufacturer's response `f` to each realization `ϵ_i`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A1.2, p.A5 (PDF 33), and §A5, p.A23 (PDF 51).

**Formalization Note.** The second mover's cost sits inside the expectation. -/
noncomputable def Supplement.expectedManufacturerProfit {m : ℕ} (μ α r xs w : ℝ)
    (ε p : Fin m → ℝ) (f : Fin m → ℝ) : ℝ :=
  ∑ i, p i * manufacturerStageProfit μ α r xs w (ε i) (f i)

end ComplementarySourcing


