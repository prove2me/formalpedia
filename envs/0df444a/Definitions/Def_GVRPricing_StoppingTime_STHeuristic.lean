-- Prove2me | Definitions.Def_GVRPricing_StoppingTime_STHeuristic
-- name    : GVRPricing_StoppingTime_STHeuristic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:26:20.616979+00:00
-- url     : https://prove2.me/theorems/50fe902b-30e3-411f-b13e-b4adda43f3df
-- title:
--   §4.1 — the stopping-time heuristic: price $p_k$ until $\tau=\min(T_m,t_m)$, then $p_{k+1}$; its expected revenue $J^{ST}(n,t)$
-- statement:
--   Fix an index $k$ with $1\le k\le K-1$ (the paper's $k^*$), a stock $n\in\mathbb N$ and a horizon $t$. Put
--
--   $$t_k=\frac{n-\lambda_{k+1}t}{\lambda_k-\lambda_{k+1}},\qquad m=\lceil\lambda_k t_k\rceil,\qquad t_m=\frac{m}{\lambda_k},\qquad t'=t_m+\frac{n-m}{\lambda_{k+1}}.$$
--
--   **Sales process.** Let $E_1,\dots,E_n$ be independent standard exponential random variables and $S_j=E_1+\dots+E_j$. Demand is Poisson with intensity $\lambda_k$ while the price is $p_k$ and $\lambda_{k+1}$ while it is $p_{k+1}$; the $j$-th sale occurs when the cumulative intensity reaches $S_j$. Since there are only $n$ clocks, at most $n$ items are sold.
--
--   **ST heuristic.** Start at price $p_k$ and switch to $p_{k+1}$ at the random time
--
--   $$\tau=\min(T_m,t_m),$$
--
--   where $T_m=S_m/\lambda_k$ is the time of the $m$-th demand when the price is fixed at $p_k$. The cumulative intensity is therefore $\lambda_k s$ for $s\le\tau$ and $\lambda_k\tau+\lambda_{k+1}(s-\tau)$ for $s>\tau$. A sale with $S_j\le\lambda_k\tau$ happens at time $S_j/\lambda_k$ at price $p_k$; any other sale happens at time $\tau+(S_j-\lambda_k\tau)/\lambda_{k+1}$ at price $p_{k+1}$.
--
--   **Expected revenue.** $J^{ST}(n,t)$ is the expectation of the sum of the prices charged at the sales in $[0,t]$, i.e. of $\int_0^t p_s\,dN_s$ in (4).
--
--   These are the objects of Theorem 5 and its proof.
--
--   **Formalization Note** The ST policy is Markovian in (items sold, elapsed time): it charges $p_k$ while fewer than $m$ items are sold and the elapsed time is below $t_m$, and $p_{k+1}$ afterwards. The exponential-clock (time-change) construction is the exact law of the controlled Poisson sales process for such a policy. Time is elapsed time from $0$. The index $k$ is a parameter; the hypotheses $\lambda_{k+1}t<n\le\lambda_k t$ of every theorem make it the paper's $k^*$. The expectation is a lower Lebesgue integral of a nonnegative revenue bounded by $n\max_k p_k$, hence finite. Mission 1 of this series defines the same process for general policies; drafts cannot import drafts, so it is built here for the ST policy.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), pp. 1010–1011 (PDF 12–13), §4.1, ST Heuristic; sales process §2.2, p. 1004 (PDF 6), (2) and (4); t′ from p. 1018 (PDF 20)

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_Menu

namespace GVRPricing.StoppingTime

open MeasureTheory ProbabilityTheory

variable {K : ℕ}

/-- `expMeasure 1` is a probability measure (hence σ-finite), needed for the product law. -/
instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- Law of `n` i.i.d. standard exponential clocks `E_1, …, E_n` (0-based `Fin n`). -/
noncomputable def clockLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => expMeasure 1)

/-- Proposition 4's time at the lower price, `t_k = (n − λ_{k+1} t)/(λ_k − λ_{k+1})` (0-based `k`). -/
noncomputable def tK (M : Menu K) (k : ℕ) (n t : ℝ) : ℝ :=
  (n - M.lamN (k + 1) * t) / (M.lamN k - M.lamN (k + 1))

/-- `m = ⌈λ_k t_k⌉` (§4.1, p. 1010). -/
noncomputable def stM (M : Menu K) (k n : ℕ) (t : ℝ) : ℕ :=
  ⌈M.lamN k * tK M k n t⌉₊

/-- `t_m = m / λ_k`, the deterministic time to sell `m` items at `p_k`. -/
noncomputable def tm (M : Menu K) (k n : ℕ) (t : ℝ) : ℝ :=
  (stM M k n t : ℝ) / M.lamN k

/-- Cumulative clock `S_j = E_1 + ⋯ + E_j` (sum over the first `j` clocks). -/
def cumClock {n : ℕ} (E : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), E i

/-- The switching time `τ = min(T_m, t_m)`, where `T_m = S_m / λ_k` is the time of the `m`-th demand
while the price is `p_k`. -/
noncomputable def switchTime (M : Menu K) (k n : ℕ) (t : ℝ) (E : Fin n → ℝ) : ℝ :=
  min (cumClock E (stM M k n t) / M.lamN k) (tm M k n t)

/-- Sales process of the ST heuristic by the exponential-clock (time-change) construction:
the intensity is `λ_k` on `[0, τ)` and `λ_{k+1}` afterwards, so the cumulative intensity is
`Λ(s) = λ_k s` for `s ≤ τ` and `λ_k τ + λ_{k+1}(s − τ)` after, and the `j`-th sale happens at
`Λ⁻¹(S_j)`.  Only `n` clocks exist, so at most `n` items are sold (constraint (2)).
This is the time (elapsed time from 0) of the sale using clock `i` (the `(i+1)`-st sale). -/
noncomputable def saleTime (M : Menu K) (k n : ℕ) (t : ℝ) (E : Fin n → ℝ) (i : Fin n) : ℝ :=
  let S := cumClock E (i.val + 1)
  let τ := switchTime M k n t E
  if S ≤ M.lamN k * τ then S / M.lamN k
  else τ + (S - M.lamN k * τ) / M.lamN (k + 1)

/-- The price charged at the `(i+1)`-st sale: `p_k` if it occurs by the switch, `p_{k+1}` after. -/
noncomputable def salePrice (M : Menu K) (k n : ℕ) (t : ℝ) (E : Fin n → ℝ) (i : Fin n) : ℝ :=
  if cumClock E (i.val + 1) ≤ M.lamN k * switchTime M k n t E then M.pN k else M.pN (k + 1)

/-- Realized revenue `∫_0^t p_s dN_s` of the ST heuristic: the price at each sale in `[0, t]`. -/
noncomputable def stRevenue (M : Menu K) (k n : ℕ) (t : ℝ) (E : Fin n → ℝ) : ℝ :=
  ∑ i, if saleTime M k n t E i ≤ t then salePrice M k n t E i else 0

/-- `J^ST(n, t)`: expected revenue of the ST heuristic with (0-based) switching index `k`
(the paper's `k*`), started with `n` items and horizon `t`.  The revenue is nonnegative and at most
`n · max p`, so the lower integral is finite and `toReal` loses nothing. -/
noncomputable def jST (M : Menu K) (k n : ℕ) (t : ℝ) : ℝ :=
  (∫⁻ E, ENNReal.ofReal (stRevenue M k n t E) ∂ clockLaw n).toReal

/-- `t_{n−m} = (n − m)/λ_{k+1}` and the shrunk horizon `t' = t_m + t_{n−m}` (p. 1018). -/
noncomputable def shrunkHorizon (M : Menu K) (k n : ℕ) (t : ℝ) : ℝ :=
  tm M k n t + ((n : ℝ) - stM M k n t) / M.lamN (k + 1)

end GVRPricing.StoppingTime


