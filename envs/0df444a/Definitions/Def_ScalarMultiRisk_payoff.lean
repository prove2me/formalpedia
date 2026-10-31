-- Prove2me | Definitions.Def_ScalarMultiRisk_payoff
-- name    : ScalarMultiRisk_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:20.426134+00:00
-- url     : https://prove2.me/theorems/3f9354a3-daea-478c-a88c-b151afcaa9dc
-- title:
--   The inner product $S^{\mathsf T}X$ of a price and a portfolio
-- statement:
--   For random vectors $S,X$ in $\mathbb R^d$, $S^{\mathsf T}X$ is the random variable $\omega\mapsto S(\omega)^{\mathsf T}X(\omega)$, the value of the portfolio $X$ (in physical units) at prices $S$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, §3.2, p.11

import Mathlib

open MeasureTheory Matrix

namespace ScalarMultiRisk

/-- **The inner product of a price and a portfolio.** `S^T X`, the random variable
`ω ↦ S(ω)ᵀ X(ω)`, used throughout arXiv:1807.10694v5, §3.2 and §4. -/
def payoff {Ω : Type*} {d : ℕ} (S X : Ω → Fin d → ℝ) : Ω → ℝ :=
  fun ω => S ω ⬝ᵥ X ω

end ScalarMultiRisk


