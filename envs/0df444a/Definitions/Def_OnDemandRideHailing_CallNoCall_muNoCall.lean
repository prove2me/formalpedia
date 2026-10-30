-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_muNoCall
-- name    : OnDemandRideHailing_CallNoCall_muNoCall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:57:59.853251+00:00
-- url     : https://prove2.me/theorems/b4a0ec11-87ad-4061-8f4f-239f8d72b9dd
-- title:
--   Service rates (3) of the approximated no-call (street-hailing) system
-- statement:
--   A circular road of perimeter $R>0$ carries $k\ge1$ taxis moving at constant speed $v>0$; passengers arrive as a Poisson process of rate $\lambda\ge0$ at uniformly distributed locations and request rides whose length is exponential with mean $d>0$ (§3, pp. 7–8). In the **no-call mechanism** there is no matching: a passenger is picked up by the first available taxi passing by.
--
--   The paper approximates this system by an M/M/k queue with arrival rate $\lambda$ and, in state $n$, service rate
--
--   $$
--   \mu^{(nc)}_n=\begin{cases}
--   \dfrac{n}{\frac dv+\int_0^{R/v}\left(\frac{R-vt}{R}\right)^{k-n+1}\exp\!\left(-\frac{(n-1)v^2t^2}{2Rd}\right)dt}, & n\le k,\\[4mm]
--   \dfrac{k}{\frac dv+\int_0^{R/v}\left(\frac{R-vt}{R}\right)^{n-k}\exp\!\left(-\frac{\lambda vt^2}{2R}\right)dt}, & n>k.
--   \end{cases}
--   $$
--
--   The integrals are approximate expected en route times (pp. 18–19). For $n>k$ the exponential factor is the probability that a taxi meets no newly arriving passenger, so the rate depends on the same $\lambda$ as the queue's arrival rate. This is display (3); the approximation is the same for the one- and two-direction no-call systems.
--
--   **Formalization Note** The integrals are interval integrals over $[0,R/v]$. The exponents $k-n+1$ (for $n\le k$) and $n-k$ (for $n>k$) are natural numbers without truncation on their branches; $n-1$ is computed in $\mathbb R$. The value at $n=0$ is unused.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, §5.2, display (3), p. 19; model §3, pp. 7–8

import Mathlib

namespace OnDemandRideHailing.CallNoCall

/-- **Service rates (3) of the approximated no-call (street-hailing) system.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, §5.2, display (3), p. 19:
`µ(nc)_n = n/(d/v + ∫_0^{R/v} ((R−vt)/R)^{k−n+1} exp(−(n−1)v²t²/(2Rd)) dt)` for `n ≤ k`, and
`µ(nc)_n = k/(d/v + ∫_0^{R/v} ((R−vt)/R)^{n−k} exp(−λvt²/(2R)) dt)` for `n > k`.

The model is that of §3 (pp. 7–8): circular road of perimeter `R`, `k` taxis of speed `v`,
Poisson arrivals at rate `λ` at uniform locations, ride distances exponential with mean `d`. In
the no-call mechanism a passenger is picked up by the first available taxi passing by (p. 8).
The integrals are the approximate expected en route times of pp. 18–19. For `n > k` the
exponential factor is the probability that the taxi meets no newly arriving passenger, so it
depends on the arrival rate `λ` (`lam`), the same `λ` as the queue's arrival rate. The paper
notes (p. 18) that the approximation is the same for the one- and two-direction systems.

**Formalization Note.** Transcribed as printed. The integrals are interval integrals over
`[0, R/v]`; the exponents `k − n + 1` (on the branch `n ≤ k`) and `n − k` (on `n > k`) are natural
numbers without truncation, and `n − 1` in the exponential is cast to `ℝ` first. Index `n = 0`
is unused. -/
noncomputable def muNoCall (lam d v : ℝ) (k : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  if n ≤ k then
    (n : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (k - n + 1) * Real.exp (-(((n : ℝ) - 1) * v ^ 2 * t ^ 2 / (2 * R * d))))
  else
    (k : ℝ) / (d / v + ∫ t in (0 : ℝ)..R / v,
      ((R - v * t) / R) ^ (n - k) * Real.exp (-(lam * v * t ^ 2 / (2 * R))))

end OnDemandRideHailing.CallNoCall


