-- Prove2me | Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary
-- name    : MDPFinance_TerminalWealth_PowerAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:55:05.461816+00:00
-- url     : https://prove2.me/theorems/f5727c81-f625-4816-a294-aac8f9db168c
-- title:
--   The power-utility one-period sub-problem, Eq. (4.7)
-- statement:
--   $A_n := \{\alpha \in \mathbb{R}^d : 1+\alpha\cdot R_{n+1} \geq 0 \text{ a.s.}\}$; the power-utility
--   one-period sub-problem is $v_n := \sup_{\alpha \in A_n} \mathbb{E}[(1+\alpha\cdot R_{n+1})^\gamma]$.
--
--   **Formalization Note.** Reused, unmodified, by the HARA-utility theorem (both share the same
--   one-period sub-problem after a wealth-shift transformation, per the book's own proof of Theorem
--   4.2.11).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 83, PDF 97, Eq. (4.7)

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The set of admissible fractions `A_n := {α ∈ ℝ^d | 1 + α·R_{n+1} ≥ 0  ℙ-a.s.}`
(Bäuerle–Rieder, p. 83, PDF 97), used in the power-, HARA- and log-utility one-period
sub-problems. -/
def TerminalWealthMarket.Afrac (M : TerminalWealthMarket Ω d) (n : ℕ) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 ≤ 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period power-utility sub-problem, Eq. (4.7) (Bäuerle–Rieder, p. 83, PDF 97):
`v_n := sup_{α ∈ A_n} 𝔼[(1+α·R_{n+1})^γ]`. -/
noncomputable def TerminalWealthMarket.vPower (M : TerminalWealthMarket Ω d) (γ : ℝ) (n : ℕ) :
    ℝ :=
  ⨆ α ∈ M.Afrac n, ∫ ω, (1 + ∑ k, α k * M.R (n + 1) ω k) ^ γ ∂M.measIP

end MDPFinance.TerminalWealth


