-- Prove2me | Definitions.Def_MDPFinance_ConsumptionInvestment_RegimePowerAuxiliary
-- name    : MDPFinance_ConsumptionInvestment_RegimePowerAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:01:12.842991+00:00
-- url     : https://prove2.me/theorems/4d129f1b-e2fa-46b5-bf71-2c151e86fbe0
-- title:
--   The regime-dependent power-utility one-period sub-problem, Eq. (4.20)
-- statement:
--   $A(j) := \{\alpha \in \mathbb{R}^d : 1+\alpha\cdot R(j) \ge 0 \ Q_j\text{-a.e.}\}$;
--   $v(j) := \sup_{\alpha \in A(j)} \mathbb{E}[(1+\alpha\cdot R(j))^\gamma]$, $R(j) \sim Q_j$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 104, PDF 118, Eq. (4.20)

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

variable {EY : Type*} [Fintype EY] [MeasurableSpace EY] {d : ℕ}

/-- `A(j) := {α ∈ ℝ^d | 1+α·R(j) ≥ 0 Q_j-a.e.}`, the admissible fractions in regime `j`
(Bäuerle–Rieder, p. 104, PDF 118). -/
def RegimeSwitchingMarket.Afrac (M : RegimeSwitchingMarket EY d) (j : EY) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ z ∂(M.Q j), 0 ≤ 1 + ∑ k, α k * z k}

/-- The generic one-period power-utility sub-problem, Eq. (4.20) (Bäuerle–Rieder, p. 104, PDF
118): `v(j) := sup_{α ∈ A(j)} 𝔼[(1+α·R(j))^γ]`. -/
noncomputable def RegimeSwitchingMarket.vPower (M : RegimeSwitchingMarket EY d) (γ : ℝ)
    (j : EY) : ℝ :=
  ⨆ α ∈ M.Afrac j, ∫ z, (1 + ∑ k, α k * z k) ^ γ ∂(M.Q j)

end MDPFinance.ConsumptionInvestment


