-- Prove2me | Definitions.Def_ComplementarySourcing_weightedRisk
-- name    : ComplementarySourcing_weightedRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:33.656008+00:00
-- url     : https://prove2.me/theorems/ddabf437-04d2-4f9f-95b2-d232d84b1629
-- title:
--   The quantities $A_i$ at $n=2$
-- statement:
--   The paper's $A_i=\big(\sum_{j\le i}p_j\big)\epsilon_i+\sum_{j>i}p_j\epsilon_j$ at $n=2$, $p_1=p_2=\tfrac12$:
--
--   $$A_1=\tfrac12\epsilon_1+\tfrac12\epsilon_2,\qquad A_2=\big(\tfrac12+\tfrac12\big)\epsilon_2.$$
--
--   **Formalization Note** Indexed by `Fin 2`.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.A1

import Mathlib
import Definitions.Def_ComplementarySourcing_riskLevel

namespace ComplementarySourcing

/-- The paper's `A_i = (Σ_{j ≤ i} p_j) ϵ_i + Σ_{j > i} p_j ϵ_j` at `n = 2`, `p₁ = p₂ = ½`, so
`A₁ = ½ϵ₁ + ½ϵ₂` and `A₂ = (½ + ½)ϵ₂`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.A1 (PDF 29).

**Formalization Note.** Indexed by `Fin 2`, like `riskLevel`. -/
noncomputable def weightedRisk (ε₀ σ : ℝ) : Fin 2 → ℝ :=
  ![1 / 2 * riskLevel ε₀ σ 0 + 1 / 2 * riskLevel ε₀ σ 1, (1 / 2 + 1 / 2) * riskLevel ε₀ σ 1]

end ComplementarySourcing


