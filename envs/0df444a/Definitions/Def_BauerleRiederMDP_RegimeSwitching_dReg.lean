-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_dReg
-- name    : BauerleRiederMDP_RegimeSwitching_dReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:06.792369+00:00
-- url     : https://prove2.me/theorems/50d4d0b5-9c02-4808-8daa-963018771690
-- title:
--   Coefficients $d_n(j)$ of Theorem 4.4.2
-- statement:
--   For $0<\gamma<1$, $\delta=(1-\gamma)^{-1}$, interest rate $i$ and discount factor $\beta$, the coefficients $d_n(j)$, $j\in E_Y$, are
--
--   $$
--   d_0(j)=\gamma^{-1},\qquad d_{n+1}^\delta(j)=\gamma^{-\delta}+\big(\beta(1+i)^\gamma v(j)\big)^\delta\Big(\sum_{k\in E_Y}p_{jk}d_n(k)\Big)^\delta,
--   $$
--
--   where $v(j)$ is the value of problem (4.20) for $R(j)$; $d_{n+1}(j)$ is the positive root. They give the value functions $J_n(x,j)=d_n(j)x^\gamma$ under power utility.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.4.2 a), pp.103–104 (PDF pp.117–118)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_powerValue
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_RegimeMarket
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The coefficients `d_n(j)` of the regime-switching power-utility problem
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 4.4.2 a), pp.103–104, PDF pp.117–118): `d_0(j) = γ^{-1}` and
`d_{n+1}^δ(j) = γ^{-δ} + (β(1 + i)^γ v(j))^δ (∑_{k ∈ E_Y} p_{jk} d_n(k))^δ`,
`δ = (1 − γ)^{-1}`, where `v(j)` is the value (4.20) for the law `Q_j`. Solved for the positive
root: `d_{n+1}(j) = (γ^{-δ} + …)^{1 − γ}`.

**Formalization Note.** `v(j)` enters as `(powerValue (Q_j) γ).toReal`, its real value (finite
under Assumption (FM)). -/
noncomputable def dReg {EY : Type*} [Fintype EY] {d : ℕ} (M : RegimeMarket EY d) (i β γ : ℝ) :
    ℕ → EY → ℝ
  | 0 => fun _ => 1 / γ
  | n + 1 => fun j =>
      (γ ^ (-(1 - γ)⁻¹) + (β * (1 + i) ^ γ *
          (powerValue (M.Q j : Measure (Fin d → ℝ)) γ).toReal) ^ (1 - γ)⁻¹ *
        (∑ k, M.p j k * dReg M i β γ n k) ^ (1 - γ)⁻¹) ^ (1 - γ)

end BauerleRiederMDP.RegimeSwitching


