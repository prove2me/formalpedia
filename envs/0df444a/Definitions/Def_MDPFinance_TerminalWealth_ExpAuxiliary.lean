-- Prove2me | Definitions.Def_MDPFinance_TerminalWealth_ExpAuxiliary
-- name    : MDPFinance_TerminalWealth_ExpAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:55:08.73913+00:00
-- url     : https://prove2.me/theorems/ffc8e5e0-7689-4ecd-b6e0-8a4bb2c6be9d
-- title:
--   The exponential-utility one-period sub-problem, Eq. (4.13)
-- statement:
--   $v_n := \inf_{a \in \mathbb{R}^d} \mathbb{E}[\exp(-\gamma(S^0_N/S^0_n)\,a\cdot R_{n+1})]$, the
--   exponential-utility one-period sub-problem.
--
--   **Formalization Note (moderation).** The expectations in (4.13) are Lebesgue integrals in
--   $[0,\infty]$: no exponential moments of $R_{n+1}$ are assumed (the book needs only no
--   arbitrage here), and a Bochner integral of a non-integrable $\exp(\cdot)$ would be $0$ and
--   turn the infimum into $0$. The infimum lies in $(0,1]$ since $a = 0$ gives $1$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 91, PDF 105, Eq. (4.13)

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The generic one-period exponential-utility sub-problem, Eq. (4.13) (Bäuerle–Rieder, p. 91,
PDF 105): `v_n := inf_{a ∈ ℝ^d} 𝔼[exp(-γ(S⁰_N/S⁰_n) a·R_{n+1})]`. The expectations are Lebesgue
integrals in `[0, ∞]` (no exponential moments are assumed: the book needs only no-arbitrage
here); the infimum lies in `(0, 1]` since `a = 0` gives `1`, and is returned as a real. -/
noncomputable def TerminalWealthMarket.vExp (M : TerminalWealthMarket Ω d) (γ : ℝ) (n : ℕ) :
    ℝ :=
  (⨅ a : Fin d → ℝ,
    ∫⁻ ω, ENNReal.ofReal
      (Real.exp (-γ * (M.S0 M.N / M.S0 n) * ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP).toReal

end MDPFinance.TerminalWealth


