-- Prove2me | Definitions.Def_MDPFinance_ConsumptionInvestment_PowerAuxiliary
-- name    : MDPFinance_ConsumptionInvestment_PowerAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:51.073031+00:00
-- url     : https://prove2.me/theorems/8fbb97e7-6104-4a32-add8-9ec1a4fef0f1
-- title:
--   The power-utility one-period sub-problem, Eq. (4.7)
-- statement:
--   $A_n := \{\alpha \in \mathbb{R}^d : 1+\alpha\cdot R_{n+1} \ge 0 \text{ a.s.}\}$;
--   $v_n := \sup_{\alpha \in A_n} \mathbb{E}[(1+\alpha\cdot R_{n+1})^\gamma]$ — reused, unmodified,
--   from the pure-investment problem (chunk `04a`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 83, PDF 97, Eq. (4.7)

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `A_n := {α ∈ ℝ^d | 1+α·R_{n+1} ≥ 0 ℙ-a.s.}` (Bäuerle–Rieder, p. 83/97, PDF 97/111, reused
across the pure-investment (chunk `04a`) and consumption-investment problems). -/
def ConsumptionInvestmentMarket.Afrac (M : ConsumptionInvestmentMarket Ω d) (n : ℕ) :
    Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 ≤ 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period power-utility sub-problem, Eq. (4.7) (Bäuerle–Rieder, p. 83, PDF 97):
`v_n := sup_{α ∈ A_n} 𝔼[(1+α·R_{n+1})^γ]`. -/
noncomputable def ConsumptionInvestmentMarket.vPower (M : ConsumptionInvestmentMarket Ω d)
    (γ : ℝ) (n : ℕ) : ℝ :=
  ⨆ α ∈ M.Afrac n, ∫ ω, (1 + ∑ k, α k * M.R (n + 1) ω k) ^ γ ∂M.measIP

end MDPFinance.ConsumptionInvestment


