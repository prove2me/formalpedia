-- Prove2me | Definitions.Def_MDPFinance_TerminalWealth_LogAuxiliary
-- name    : MDPFinance_TerminalWealth_LogAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:55:17.902614+00:00
-- url     : https://prove2.me/theorems/14333d06-45ee-4b38-aefa-3ac0a55b27d4
-- title:
--   The logarithmic-utility one-period sub-problem, Eq. (4.11)
-- statement:
--   $A_n := \{\alpha \in \mathbb{R}^d : 1+\alpha\cdot R_{n+1} > 0 \text{ a.s.}\}$ (a strict
--   inequality, unlike the power-utility `Afrac`); the logarithmic one-period sub-problem is
--   $v_n := \sup_{\alpha \in A_n} \mathbb{E}[\log(1+\alpha\cdot R_{n+1})]$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 89, PDF 103, Eq. (4.11)

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The set of admissible fractions for the logarithmic-utility one-period problem,
`A_n := {α ∈ ℝ^d | 1 + α·R_{n+1} > 0  ℙ-a.s.}` (Bäuerle–Rieder, p. 89, PDF 103) — note the
strict inequality, unlike the power-utility `Afrac`. -/
def TerminalWealthMarket.AfracLog (M : TerminalWealthMarket Ω d) (n : ℕ) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period logarithmic-utility sub-problem, Eq. (4.11) (Bäuerle–Rieder, p. 89,
PDF 103): `v_n := sup_{α ∈ A_n} 𝔼[log(1+α·R_{n+1})]`. -/
noncomputable def TerminalWealthMarket.vLog (M : TerminalWealthMarket Ω d) (n : ℕ) : ℝ :=
  ⨆ α ∈ M.AfracLog n, ∫ ω, Real.log (1 + ∑ k, α k * M.R (n + 1) ω k) ∂M.measIP

end MDPFinance.TerminalWealth


