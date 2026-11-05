-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_dCI
-- name    : BauerleRiederMDP_RegimeSwitching_dCI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:08.261461+00:00
-- url     : https://prove2.me/theorems/91f178ce-7c90-400d-a2f1-3494088230f7
-- title:
--   Coefficients $d_n$ of Theorem 4.3.6: $d_n^\delta=\gamma^{-\delta}+((1+i_{n+1})^\gamma v_n)^\delta d_{n+1}^\delta$
-- statement:
--   For $0<\gamma<1$ and $\delta=(1-\gamma)^{-1}$, the coefficients $d_0,\dots,d_N$ are defined backwards by
--
--   $$
--   d_N=\frac1\gamma,\qquad d_n^\delta=\gamma^{-\delta}+\big((1+i_{n+1})^\gamma v_n\big)^\delta d_{n+1}^\delta\quad(n<N),
--   $$
--
--   where $v_n$ is the value of problem (4.7) for $R_{n+1}$; $d_n$ is the positive root, $d_n=\big(\gamma^{-\delta}+((1+i_{n+1})^\gamma v_n)^\delta d_{n+1}^\delta\big)^{1-\gamma}$. They give the value functions $V_n(x)=d_nx^\gamma$ of the power-utility consumption-investment problem.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.3.6 a), p.97 (PDF p.111)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_powerValue
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The coefficients `d_n` of the power-utility consumption-investment problem
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 4.3.6 a), p.97, PDF p.111): `d_N = 1/γ` and, for `n < N`,
`d_n^δ = γ^{-δ} + ((1 + i_{n+1})^γ v_n)^δ d_{n+1}^δ` with `δ = (1 − γ)^{-1}`, where `v_n` is
the value (4.7) for the law `μ (n+1)` of `R_{n+1}`. Solved for the positive root:
`d_n = (γ^{-δ} + ((1 + i_{n+1})^γ v_n)^δ d_{n+1}^δ)^{1/δ}`, `1/δ = 1 − γ`.

**Formalization Note.** Computed backwards: the auxiliary sequence `e m = d_{N-m}` starts at
`e 0 = 1/γ`, so `dCI … N n = e (N - n)` for `n ≤ N`. `v_n` enters through
`(powerValue (μ (n+1)) γ).toReal`, its real value (finite under Assumption (FM)). -/
noncomputable def dCI {d : ℕ} (i : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (Fin d → ℝ)) (γ : ℝ)
    (N n : ℕ) : ℝ :=
  let δ := (1 - γ)⁻¹
  let e : ℕ → ℝ := fun m => Nat.rec (1 / γ) (fun k ek =>
    (γ ^ (-δ) + ((1 + i (N - k)) ^ γ * (powerValue (μ (N - k) : Measure (Fin d → ℝ)) γ).toReal) ^ δ *
      ek ^ δ) ^ (1 - γ)) m
  e (N - n)

end BauerleRiederMDP.RegimeSwitching


