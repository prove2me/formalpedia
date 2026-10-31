-- Prove2me | Definitions.Def_ComplementarySourcing_riskLevel
-- name    : ComplementarySourcing_riskLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:36.216979+00:00
-- url     : https://prove2.me/theorems/879e1ae0-755b-4060-8fed-655cd8387ce3
-- title:
--   The two market-risk realizations
-- statement:
--   The vector $(\epsilon_1,\epsilon_2)=(\epsilon_0+\sigma,\epsilon_0-\sigma)$.
--
--   **Formalization Note** Indexed by `Fin 2`.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.12

import Mathlib

namespace ComplementarySourcing

/-- The two realizations of the market risk, `ϵ₁ = ϵ₀ + σ` and `ϵ₂ = ϵ₀ − σ`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.12 (PDF 12).

**Formalization Note.** Indexed by `Fin 2`: the paper's index `i` is `i − 1` here. -/
def riskLevel (ε₀ σ : ℝ) : Fin 2 → ℝ :=
  ![ε₀ + σ, ε₀ - σ]

end ComplementarySourcing


