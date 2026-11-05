-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_powerValue
-- name    : BauerleRiederMDP_RegimeSwitching_powerValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:17.086433+00:00
-- url     : https://prove2.me/theorems/75b53245-8708-4a04-bbe1-ebcb03b5936a
-- title:
--   Generic one-period power-utility value $\sup_{\alpha\in A}\mathbb E(1+\alpha\cdot R)^\gamma$
-- statement:
--   For a relative risk $R$ and $0<\gamma<1$, the **generic one-period power-utility problem** has value
--
--   $$
--   \sup_{\alpha\in A}\ \mathbb E\big(1+\alpha\cdot R\big)^\gamma,
--   $$
--
--   with $A$ the admissible fractions. With $R=R_{n+1}$ this is $v_n$ of (4.7); with $R=R(j)$ it is $v(j)$ of (4.20) and (4.21). An $\alpha$ attaining the supremum is an optimal solution $\alpha^*$.
--
--   **Formalization Note** The integrand is nonnegative almost surely for $\alpha\in A$, so the expectation and the supremum are taken in $[0,\infty]$; under Assumption (FM) the value is finite and at least $1$ (take $\alpha=0$).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (4.7), p.83 (PDF p.97); (4.20), p.103 (PDF p.117); (4.21), p.104 (PDF p.118)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_admFrac
open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- The value of the **generic one-period power-utility problem** for a relative risk `R` of law
`μ` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), (4.7), p.83, PDF p.97; (4.20), p.103, PDF p.117; (4.21), p.104, PDF p.118):
`sup_{α ∈ A} 𝔼 (1 + α · R)^γ`, with `A = admFrac μ`.

**Formalization Note.** The integrand is nonnegative on the support of `μ` for `α ∈ A`, so the
expectation is a lintegral in `[0, ∞]` and the supremum is taken in `[0, ∞]`: no junk value.
Under Assumption (FM) the value is finite (and `≥ 1`, from `α = 0`); the recursions `dCI`,
`dReg` use its real value. -/
noncomputable def powerValue {d : ℕ} (μ : Measure (Fin d → ℝ)) (γ : ℝ) : ℝ≥0∞ :=
  ⨆ α ∈ admFrac μ, ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, α k * z k) ^ γ) ∂μ

end BauerleRiederMDP.RegimeSwitching


