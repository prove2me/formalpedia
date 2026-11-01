-- Prove2me | Definitions.Def_FocusSetRB_piBar
-- name    : FocusSetRB_piBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:15.172148+00:00
-- url     : https://prove2.me/theorems/03115e30-bab8-428d-a997-d852f8a55a47
-- title:
--   The optimal single-armed policy $\bar\pi^*$, its chain $P_{\bar\pi^*}$, $\mu^*$ and $\Xi$
-- statement:
--   Let $y^*$ be an optimal solution of (LP). The **optimal single-armed policy** $\bar\pi^*$ is
--
--   $$
--   \bar\pi^*(a\mid s)=\begin{cases} y^*(s,a)/\big(y^*(s,0)+y^*(s,1)\big), & \text{if } y^*(s,0)+y^*(s,1)>0,\\ 1/2, & \text{if } y^*(s,0)+y^*(s,1)=0,\end{cases}
--   $$
--
--   for $s\in\mathbb S$, $a\in\{0,1\}$. It induces the single-armed transition matrix $P_{\bar\pi^*}(s,s')=\sum_a\bar\pi^*(a\mid s)P(s,a,s')$. The vector
--
--   $$
--   \mu^*(s)=y^*(s,0)+y^*(s,1)
--   $$
--
--   is a stationary distribution of $P_{\bar\pi^*}$, and under Assumption 1 the unique one. $\Xi$ denotes the $|\mathbb S|\times|\mathbb S|$ matrix every row of which is $\mu^*$.
--
--   **Formalization Note** The paper introduces $\mu^*$ as the stationary distribution of $P_{\bar\pi^*}$ and observes that $\mu^*(s)=y^*(s,0)+y^*(s,1)$; the formula is taken as the definition. The $1/2$ branch is used whenever the denominator is not positive, which for a feasible (nonnegative) $y^*$ is exactly the case $y^*(s,0)+y^*(s,1)=0$.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, §3.4, eq. (3), p.6; μ*: p.7; Ξ: Definition 2, p.17

import Mathlib
import Definitions.Def_FocusSetRB_SingleArmMDP

namespace FocusSetRB

open Matrix

variable {S : Type*} [Fintype S]

/-- The **optimal single-armed policy** `π̄*` built from an (LP) solution `y*`
(arXiv:2402.05689v4, §3.4, eq. (3), p.6):
`π̄*(a | s) = y*(s, a) / (y*(s, 0) + y*(s, 1))` if `y*(s, 0) + y*(s, 1) > 0`, and `1/2` if
`y*(s, 0) + y*(s, 1) = 0`.

**Formalization Note.** Actions are `Bool` (`true` = `1`). The `1/2` branch is taken whenever the
denominator is not positive; for a feasible `y*` (nonnegative) that is exactly the source's case
`y*(s, 0) + y*(s, 1) = 0`. -/
noncomputable def piBar (y : S → Bool → ℝ) (s : S) (a : Bool) : ℝ :=
  if 0 < y s false + y s true then y s a / (y s false + y s true) else 1 / 2

/-- `μ*(s) = y*(s, 0) + y*(s, 1)` (arXiv:2402.05689v4, §3.4, p.7), the stationary distribution of
the chain induced by `π̄*`.

**Formalization Note.** The source introduces `μ*` as the unique stationary distribution of
`P_π̄*` under Assumption 1 and notes that `μ*(s) = y*(s, 0) + y*(s, 1)`; that formula is taken
as the definition. -/
def muStar (y : S → Bool → ℝ) (s : S) : ℝ := y s false + y s true

/-- `P_π̄*`, the transition matrix of the single-armed chain under `π̄*`
(arXiv:2402.05689v4, §3.4, p.6): `P_π̄*(s, s') = ∑_a π̄*(a | s) P(s, a, s')`. -/
noncomputable def Ppi (M : SingleArmMDP S) (y : S → Bool → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' => ∑ a, piBar y s a * M.P s a s'

/-- `Ξ`, the `|𝕊| × |𝕊|` matrix with every row equal to `μ*` (arXiv:2402.05689v4, Definition 2,
p.17). -/
def Xi (y : S → Bool → ℝ) : Matrix S S ℝ :=
  Matrix.of fun _ s' => muStar y s'

end FocusSetRB


