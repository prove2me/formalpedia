-- Prove2me | Definitions.Def_MDPFinance_ConsumptionInvestment_LogAuxiliary
-- name    : MDPFinance_ConsumptionInvestment_LogAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:42.877823+00:00
-- url     : https://prove2.me/theorems/8bc89b2b-dac3-4d52-8282-0436565e42f9
-- title:
--   The logarithmic-utility one-period sub-problem, Eq. (4.11)
-- statement:
--   $A_n := \{\alpha \in \mathbb{R}^d : 1+\alpha\cdot R_{n+1} > 0 \text{ a.s.}\}$ (strict);
--   $v_n := \sup_{\alpha \in A_n} \mathbb{E}[\log(1+\alpha\cdot R_{n+1})]$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 89, PDF 103, Eq. (4.11)

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `A_n := {α ∈ ℝ^d | 1+α·R_{n+1} > 0 ℙ-a.s.}` (Bäuerle–Rieder, p. 89, PDF 103), the strict
version used for logarithmic utility. -/
def ConsumptionInvestmentMarket.AfracLog (M : ConsumptionInvestmentMarket Ω d) (n : ℕ) :
    Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period logarithmic-utility sub-problem, Eq. (4.11) (Bäuerle–Rieder, p. 89,
PDF 103): `v_n := sup_{α ∈ A_n} 𝔼[log(1+α·R_{n+1})]`. -/
noncomputable def ConsumptionInvestmentMarket.vLog (M : ConsumptionInvestmentMarket Ω d)
    (n : ℕ) : ℝ :=
  ⨆ α ∈ M.AfracLog n, ∫ ω, Real.log (1 + ∑ k, α k * M.R (n + 1) ω k) ∂M.measIP

end MDPFinance.ConsumptionInvestment


