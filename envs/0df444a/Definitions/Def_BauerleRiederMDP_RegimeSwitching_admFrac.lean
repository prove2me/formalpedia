-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_admFrac
-- name    : BauerleRiederMDP_RegimeSwitching_admFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:21.355061+00:00
-- url     : https://prove2.me/theorems/b1e5c4fc-76b8-4b64-9162-358865647b16
-- title:
--   Admissible fractions $A=\{\alpha\in\mathbb R^d: 1+\alpha\cdot R\ge0\ \text{a.s.}\}$
-- statement:
--   For a relative risk $R\in\mathbb R^d$ with law $\mu$, the **admissible fractions** are
--
--   $$
--   A=\{\alpha\in\mathbb R^d : 1+\alpha\cdot R\ge0\ \ \mathbb P\text{-a.s.}\},
--   $$
--
--   the fractions of wealth invested in the risky assets that keep the wealth nonnegative. With $R=R_{n+1}$ this is $A_n$ of (4.7); with $R=R(j)$ it is $A(j)$ of (4.20).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.83 (PDF p.97); p.103 (PDF p.117)

import Mathlib
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The **admissible fractions** for a relative risk `R ∈ ℝ^d` of law `μ`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.83, PDF p.97, and p.103, PDF p.117):
`A = {α ∈ ℝ^d | 1 + α · R ≥ 0 ℙ-a.s.}`; with `μ` the law of `R_{n+1}` this is `A_n` of (4.7),
with `μ = Q_j` the law of `R(j)` it is `A(j)` of (4.20). -/
def admFrac {d : ℕ} (μ : Measure (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ z ∂μ, 0 ≤ 1 + ∑ k, α k * z k}

end BauerleRiederMDP.RegimeSwitching


