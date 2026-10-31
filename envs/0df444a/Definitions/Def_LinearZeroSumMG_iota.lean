-- Prove2me | Definitions.Def_LinearZeroSumMG_iota
-- name    : LinearZeroSumMG_iota
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:15.204048+00:00
-- url     : https://prove2.me/theorems/ea68f9ac-a0b1-4b29-8cb2-f378d4b4ee23
-- title:
--   The logarithmic factor $\iota=\log(2dT/p)$, $T=KH$
-- statement:
--   With $T=KH$ the total number of steps and $p\in(0,1)$ the failure probability,
--   $$
--   \iota=\log\frac{2dT}{p}.
--   $$
--   It appears in the bonus parameter $\beta=c\,dH\sqrt\iota$ and in the rate $\sqrt{d^3H^3T\iota^2}$ of Theorem 1.
--
--   **Formalization Note** $\log$ is the natural logarithm. For $d,K,H\ge1$ and $p\in(0,1)$, $\iota>\log2>0$.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Theorem 1, p.12

import Mathlib

namespace LinearZeroSumMG

/-- **The logarithmic factor `ι = log(2dT/p)` with `T = KH`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Theorem 1, p.12: "Set `β = cdH√ι`
with `ι := log(2dT/p)` in Algorithm 1", and §3.3, p.12: "Recall that `T = KH` is the total number of
timesteps."

**Formalization Note** `log` is `Real.log`. In the theorems `d, K, H ≥ 1` and `p ∈ (0, 1)`, so
`2dT/p > 2` and `ι > log 2 > 0`. -/
noncomputable def iota (d K H : ℕ) (p : ℝ) : ℝ :=
  Real.log (2 * d * ((K : ℝ) * H) / p)

end LinearZeroSumMG


