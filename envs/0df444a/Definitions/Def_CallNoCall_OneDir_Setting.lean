-- Prove2me | Definitions.Def_CallNoCall_OneDir_Setting
-- name    : CallNoCall_OneDir_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:12.819043+00:00
-- url     : https://prove2.me/theorems/f68b0170-d53f-4d96-b6b4-ca96ad50af41
-- title:
--   §5.1–§5.2 — the service rates (1) of the one-direction call approximation and (3) of the no-call approximation, and W^(1c), W^(nc)
-- statement:
--   A circular road of perimeter $R > 0$ carries $k \ge 1$ taxis travelling clockwise at speed $v > 0$. Passengers arrive as a Poisson process of rate $\lambda \ge 0$ at uniformly distributed locations and ride an exponentially distributed distance with mean $d > 0$, so a ride lasts $d/v$ on average. Feng, Kong and Wang approximate each matching mechanism by a state-dependent $M/M/k$ queue with arrival rate $\lambda$; the service rate in state $n$ (the number of passengers in the system) is the number of busy taxis divided by the mean ride time plus an approximate en-route time.
--
--   1. The **one-direction call system** (the platform matches each passenger to the nearest available taxi) has the rates (1), p. 16:
--   $$\mu^{(1c)}_n = \begin{cases} \dfrac{n}{\frac dv + \frac{R}{v(k-n+1)}}, & n < k,\\[2mm] \dfrac{k}{\frac dv + \frac{R}{2v}}, & n = k,\\[2mm] \dfrac{k}{\frac dv + \frac{R}{v(n-k+1)}}, & n > k. \end{cases}$$
--   2. The **no-call system** (a passenger is picked up by the first free taxi passing by) has the rates (3), p. 19:
--   $$\mu^{(nc)}_n = \begin{cases} \dfrac{n}{\frac dv + \int_0^{R/v} \left(\frac{R-vt}{R}\right)^{k-n+1} \exp\!\left(-\frac{(n-1)v^2t^2}{2Rd}\right) dt}, & n \le k,\\[2mm] \dfrac{k}{\frac dv + \int_0^{R/v} \left(\frac{R-vt}{R}\right)^{n-k} \exp\!\left(-\frac{\lambda v t^2}{2R}\right) dt}, & n > k. \end{cases}$$
--   3. $\mathcal W^{(1c)}(\lambda,d,v,k,R)$ and $\mathcal W^{(nc)}(\lambda,d,v,k,R)$ are the average waiting times $\mathcal W$ of the state-dependent $M/M/k$ queues with arrival rate $\lambda$ and the rates (1), respectively (3), given by the closed formula of Appendix A (definition `CallNoCall.OneDir.StateDepQueue`).
--
--   These are the two approximations compared by Theorem 4. They are approximations of the simulated ride-hailing systems, not the exact systems; every theorem of the mission is about them.
--
--   **Formalization Note** $\lambda$ is written `lam`. The paper's constant $\mu = v/d$ is written `v / d` and never named $\mu$, which is reserved for the rate sequence. In (1) the factors $k-n+1$ and $n-k+1$ are real numbers; in (3) the exponents $k-n+1$ (for $n \le k$) and $n-k$ (for $n > k$) are natural numbers, used only inside their branches, where the subtraction does not truncate. The integrals are interval integrals over $[0, R/v]$, exactly as printed; the no-call rate is not defined through the call rate. The rates are used for $n \ge 1$ only. The no-call rate for $n > k$ depends on $\lambda$, and $\mathcal W^{(nc)}$ uses the same $\lambda$ in the rate and in the queue.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), pp. 7–8 (§3, model), p. 16 (1), p. 19 (3)

import Mathlib
import Definitions.Def_CallNoCall_OneDir_StateDepQueue

namespace CallNoCall.OneDir

/-- The state-dependent service rate (1), p. 16, of the approximated one-direction call system
with `k` taxis, mean ride distance `d`, speed `v` and perimeter `R`:
`μₙ = n / (d/v + R/(v(k-n+1)))` if `n < k`, `k / (d/v + R/(2v))` if `n = k`, and
`k / (d/v + R/(v(n-k+1)))` if `n > k`. Used for `n ≥ 1`. -/
noncomputable def mu1c (d v R : ℝ) (k n : ℕ) : ℝ :=
  if n < k then (n : ℝ) / (d / v + R / (v * ((k : ℝ) - n + 1)))
  else if n = k then (k : ℝ) / (d / v + R / (2 * v))
  else (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1)))

/-- The state-dependent service rate (3), p. 19, of the approximated no-call system:
for `n ≤ k`, `n / (d/v + ∫₀^{R/v} ((R - vt)/R)^{k-n+1} exp(-(n-1)v²t²/(2Rd)) dt)`, and for `n > k`,
`k / (d/v + ∫₀^{R/v} ((R - vt)/R)^{n-k} exp(-λvt²/(2R)) dt)`. Used for `n ≥ 1`. -/
noncomputable def muNC (lam d v R : ℝ) (k n : ℕ) : ℝ :=
  if n ≤ k then
    (n : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (k - n + 1) * Real.exp (-(((n : ℝ) - 1) * v ^ 2 * t ^ 2) / (2 * R * d)))
  else
    (k : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (n - k) * Real.exp (-(lam * v * t ^ 2) / (2 * R)))

/-- `W^{(1c)}(λ, d, v, k, R)`: the average waiting time of the approximated one-direction call
system, the state-dependent `M/M/k` queue with arrival rate `λ` and service rates (1). -/
noncomputable def W1c (lam d v R : ℝ) (k : ℕ) : ℝ :=
  avgWait (mu1c d v R k) lam d v

/-- `W^{(nc)}(λ, d, v, k, R)`: the average waiting time of the approximated no-call system, the
state-dependent `M/M/k` queue with arrival rate `λ` and service rates (3). -/
noncomputable def Wnc (lam d v R : ℝ) (k : ℕ) : ℝ :=
  avgWait (muNC lam d v R k) lam d v

end CallNoCall.OneDir


