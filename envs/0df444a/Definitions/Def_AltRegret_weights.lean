-- Prove2me | Definitions.Def_AltRegret_weights
-- name    : AltRegret_weights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:03:26.958768+00:00
-- url     : https://prove2.me/theorems/924a8bdd-a0f9-4faa-9182-36a336b12854
-- title:
--   The exponential weights $p_t$ of Algorithm 1
-- statement:
--   In round $t\ge1$, Algorithm 1 sets the distribution $p_t\in\Delta_d$ by
--   $$
--   p_{t,i}=\frac{\exp\!\big[-\eta L_{t-1,i}-\beta(c_{t-1,i}-\theta_t)^2\big]}{\sum_{j=1}^{d}\exp\!\big[-\eta L_{t-1,j}-\beta(c_{t-1,j}-\theta_t)^2\big]},\qquad i\in[d],
--   $$
--   i.e. $p_{t,i}\propto\exp[-\eta L_{t-1,i}-\beta(c_{t-1,i}-\theta_t)^2]$, with $\theta_t$ the centering scalar of line 3.
--
--   These are Hedge weights on the effective cumulative loss, tilted toward the experts whose last loss $c_{t-1,i}$ is close to $\theta_t$.
--
--   **Formalization Note** The proportionality is written out as a normalization; the denominator is positive whenever $d\ge1$.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.1, p.6, Algorithm 1, line 4

import Mathlib
import Definitions.Def_AltRegret_theta

namespace AltRegret

/-- **The exponential weights `p_t` of Algorithm 1.** Tao–Zheng, arXiv:2608.24731, §2.1, p.6,
Algorithm 1, line 4: "Set `p_t` such that `p_{t,i} ∝ exp[−ηL_{t−1,i} − β(c_{t−1,i} − θ_t)²]`".

`weights η β c t i = exp(−ηL_{t−1,i} − β(c_{t−1,i} − θ_t)²) / ∑_j exp(−ηL_{t−1,j} − β(c_{t−1,j} − θ_t)²)`.

**Formalization Note.** The normalization "∝" is written out; the denominator is positive for
`d ≥ 1`. Read at rounds `t ≥ 1`, with `θ_t = theta η β c t`. -/
noncomputable def weights {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i =>
    Real.exp (-η * effCumLoss c (t - 1) i - β * (lossAt c (t - 1) i - theta η β c t) ^ 2) /
      ∑ j, Real.exp (-η * effCumLoss c (t - 1) j - β * (lossAt c (t - 1) j - theta η β c t) ^ 2)

end AltRegret


