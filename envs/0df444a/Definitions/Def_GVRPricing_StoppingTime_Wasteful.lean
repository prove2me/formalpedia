-- Prove2me | Definitions.Def_GVRPricing_StoppingTime_Wasteful
-- name    : GVRPricing_StoppingTime_Wasteful
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:47:03.168512+00:00
-- url     : https://prove2.me/theorems/982c964a-48c6-4c6f-8fe9-7af498c193c3
-- title:
--   Appendix — expected revenue $J^W(n,t)$ of the wasteful heuristic (two independent Poisson sales counts)
-- statement:
--   With $k$, $m=\lceil\lambda_k t_k\rceil$ and $t_m=m/\lambda_k$ as for the ST heuristic, the **wasteful heuristic** reserves $m$ units to be sold at $p_k$ during $[0,t_m]$ and $n-m$ units to be sold at $p_{k+1}$ during $(t_m,t]$. With $N_\mu$ a Poisson random variable of mean $\mu$, its expected revenue is
--
--   $$J^W(n,t)=p_k\,\mathbb E\min\{N_{\lambda_k t_m},m\}+p_{k+1}\,\mathbb E\min\{N_{\lambda_{k+1}(t-t_m)},n-m\},$$
--
--   where $\mathbb E\min\{N_\mu,c\}=\sum_{i\ge 0}\min\{i,c\}\,e^{-\mu}\mu^i/i!$.
--
--   The wasteful heuristic is the lower-bound device in the proof of Theorem 5.
--
--   **Formalization Note** $J^W$ is defined by the paper's own formula on p. 1018 (written there at the shrunk horizon) rather than through a sales process. The Poisson mean is clamped at $0$; in the regime of every theorem, $t\ge t'\ge t_m$, so no clamping occurs.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 5, display "J^W(n, t) = p_k E min{…}"

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic

namespace GVRPricing.StoppingTime

variable {K : ℕ}

/-- `E min{N_μ, c}` for a Poisson random variable `N_μ` with mean `μ ≥ 0`, as the series
`∑_i min(i, c) e^{−μ} μ^i / i!` (`μ` is clamped at `0`).  The series converges absolutely for every
`c`, since `|min(i, c)| ≤ i + |c|` and the Poisson law has finite mean, so `tsum` is its sum. -/
noncomputable def expMinPoisson (μ c : ℝ) : ℝ :=
  ∑' i : ℕ, min (i : ℝ) c * (Real.exp (-max μ 0) * max μ 0 ^ i / (i.factorial : ℝ))

/-- `J^W(n, t)`, the expected revenue of the wasteful heuristic (Appendix, p. 1018): `m` units are
offered at `p_k` during `[0, t_m]` and `n − m` units at `p_{k+1}` during `(t_m, t]`, with independent
Poisson demand, so
`J^W(n, t) = p_k E min{N_{λ_k t_m}, m} + p_{k+1} E min{N_{λ_{k+1}(t − t_m)}, n − m}`. -/
noncomputable def jW (M : Menu K) (k n : ℕ) (t : ℝ) : ℝ :=
  M.pN k * expMinPoisson (M.lamN k * tm M k n t) (stM M k n t)
    + M.pN (k + 1) * expMinPoisson (M.lamN (k + 1) * (t - tm M k n t)) ((n : ℝ) - stM M k n t)

end GVRPricing.StoppingTime


