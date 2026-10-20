-- Prove2me | Definitions.Def_ClosedLoopBass_Immediate_Bass
-- name    : ClosedLoopBass_Immediate_Bass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:54.122173+00:00
-- url     : https://prove2.me/theorems/f829ae30-61bd-48ae-877d-00aa919dbe45
-- title:
--   §3, p. 4 — the discrete-time Bass diffusion process: cumulative demand D̃ₜ and period demand d̃ₜ
-- statement:
--   The discrete-time **Bass diffusion process** with market size $m$, coefficient of innovation $p$ and coefficient of imitation $q$ describes how a population of $m$ consumers adopts a new product when all demand is met immediately in each period. The demand in period $t\ge1$ is
--
--   $$
--   \widetilde d_t=\Bigl(p+\frac{q\,\widetilde D_t}{m}\Bigr)\bigl(m-\widetilde D_t\bigr),
--   $$
--
--   where $\widetilde D_t$ is the total sales volume up to period $t$:
--
--   $$
--   \widetilde D_1=0,\qquad \widetilde D_t=\sum_{i=1}^{t-1}\widetilde d_i\quad(t>1).
--   $$
--
--   The factor $p+q\widetilde D_t/m$ is the probability that an individual consumer who has not yet adopted purchases in period $t$. Innovators adopt at rate $p$ regardless of others, and imitators adopt in proportion to the fraction $\widetilde D_t/m$ of previous adopters.
--
--   This module defines $\widetilde D_t$ and $\widetilde d_t$ as functions of $(p,q,m)$ and the period $t$. It is the benchmark trajectory against which every sales plan of the closed-loop model is compared.
--
--   **Formalization Note** The cumulative demand is computed by a recursion on the offset $k=t-1$: `bassCumc p q m k` $=\widetilde D_{k+1}$, with $\widetilde D_{k+2}=\widetilde D_{k+1}+\widetilde d_{k+1}$. `bassCum p q m t` $=\widetilde D_t$ and `bassDemand p q m t` $=\widetilde d_t$ for $t\ge1$. Period $0$ is not a period of the model, and its value (equal to that of period $1$) is never used.
-- source:
--   Nadar, Kaya and Güler, New-Product Diffusion in Closed-Loop Supply Chains, MSOM (Articles in Advance, 2020), doi:10.1287/msom.2019.0864, p. 4, §3 (display for d̃t and the definition of D̃t)

import Mathlib

namespace ClosedLoopBass.Immediate

/-- Cumulative demand of the discrete-time Bass diffusion process, indexed by the offset
`k = t - 1`: `bassCumc p q m k` is `D̃_{k+1}`, the total sales volume up to period `k + 1`
when all demand is met in every period (Nadar–Kaya–Güler, §3, p. 4).
`D̃_1 = 0` and `D̃_{t+1} = D̃_t + d̃_t` with `d̃_t = (p + q D̃_t / m)(m − D̃_t)`. -/
noncomputable def bassCumc (p q m : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => bassCumc p q m k + (p + q * bassCumc p q m k / m) * (m - bassCumc p q m k)

/-- `D̃_t = ∑_{i=1}^{t-1} d̃_i`, the cumulative Bass demand up to (and excluding) period `t ≥ 1`.
`D̃_1 = 0`. -/
noncomputable def bassCum (p q m : ℝ) (t : ℕ) : ℝ := bassCumc p q m (t - 1)

/-- `d̃_t = (p + q D̃_t / m)(m − D̃_t)`, the Bass demand in period `t ≥ 1` (§3, p. 4). -/
noncomputable def bassDemand (p q m : ℝ) (t : ℕ) : ℝ :=
  (p + q * bassCum p q m t / m) * (m - bassCum p q m t)

end ClosedLoopBass.Immediate


