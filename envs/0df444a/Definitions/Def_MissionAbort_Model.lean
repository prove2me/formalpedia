-- Prove2me | Definitions.Def_MissionAbort_Model
-- name    : MissionAbort_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:51.866606+00:00
-- url     : https://prove2.me/theorems/3a42c4f2-3381-476c-989f-87e2087e6bac
-- title:
--   Mission data $(N,\delta,\zeta,C_m,C_s,w,D)$
-- statement:
--   The scalar data of the mission over a signal alphabet $[K]=\{1,\dots,K\}$:
--
--   1. the number $N\ge 1$ of sampling epochs, the sampling interval $\delta>0$, so that the mission time is $H=N\delta$;
--   2. the rate $\zeta>0$ of the direct failure time $T_{13}$;
--   3. the mission failure cost $C_m\ge 0$ and the system failure cost $C_s\ge 0$;
--   4. the rescue times $w_n\ge 0$ with $w_0=0$;
--   5. the state-observation matrix $D=(d_{ik})_{2\times K}$, whose rows are probability vectors, since $d_{ik}=\mathbb P(Y_n=k\mid X_n=i)$.
--
--   **Formalization Note** The entry $d_{ik}$ is `D (i-1) (k-1)`. Only $w_0,\dots,w_N$ are consulted. Assumptions 1 to 3 of the paper are not part of this data. The rows being probability vectors force $K\ge 1$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3, pp.8–10

import Mathlib

namespace MissionAbort

/-- The scalar data of the mission (Sun, Hu & Ye, arXiv:2505.03225v1, §3, pp.8–11): the number `N`
of sampling epochs (`H = Nδ` is the mission time, p.10), the inter-sampling interval `δ`, the rate
`ζ` of the direct failure time `T₁₃` (p.9), the mission and system failure costs `Cm`, `Cs` (p.10),
the rescue times `wₙ` with `w₀ = 0` (p.10) and the state-observation matrix `D = (d_ik)` (p.10).

**Formalization Note.** `D i k` is the page's `d_{i+1,k+1}`: row `0` is the healthy state and row `1`
the defective state, and `k : Fin K` is the signal value `k + 1 ∈ [K]`. The rows are probability
vectors because `d_ik = P(Yₙ = k | Xₙ = i)` (p.10); they force `1 ≤ K`. Only `w 0, …, w N` are
consulted. The costs are nonnegative, which the page leaves to the word "cost". -/
structure Model (K : ℕ) where
  /-- The number of sampling epochs, `H = Nδ`. -/
  N : ℕ
  /-- The inter-sampling interval. -/
  δ : ℝ
  /-- The rate of the exponential direct failure time `T₁₃`. -/
  ζ : ℝ
  /-- The mission failure cost. -/
  Cm : ℝ
  /-- The system failure cost. -/
  Cs : ℝ
  /-- The rescue times `w₀, …, w_N`. -/
  w : ℕ → ℝ
  /-- The state-observation matrix. -/
  D : Fin 2 → Fin K → ℝ
  N_pos : 1 ≤ N
  δ_pos : 0 < δ
  ζ_pos : 0 < ζ
  Cm_nonneg : 0 ≤ Cm
  Cs_nonneg : 0 ≤ Cs
  w_nonneg : ∀ n, 0 ≤ w n
  w_zero : w 0 = 0
  D_nonneg : ∀ i k, 0 ≤ D i k
  D_sum : ∀ i, ∑ k, D i k = 1

end MissionAbort


