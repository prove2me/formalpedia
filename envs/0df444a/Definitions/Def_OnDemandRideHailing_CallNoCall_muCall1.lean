-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_muCall1
-- name    : OnDemandRideHailing_CallNoCall_muCall1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:57:40.826726+00:00
-- url     : https://prove2.me/theorems/cb24ab2b-f266-49cb-a93e-9bc5dbc1cc66
-- title:
--   Service rates (1) of the approximated one-direction call system
-- statement:
--   A circular road of perimeter $R>0$ carries $k\ge1$ taxis moving at constant speed $v>0$; passengers arrive as a Poisson process of rate $\lambda\ge0$ at uniformly distributed locations and request rides whose length is exponential with mean $d>0$ (§3, pp. 7–8). In the **call mechanism** a platform matches each arriving passenger to the nearest available taxi; in the one-direction system all taxis and rides go clockwise.
--
--   The paper approximates this system by an M/M/k queue with arrival rate $\lambda$ and, in state $n$ (passengers waiting or in service), service rate
--
--   $$
--   \mu^{(1c)}_n=\begin{cases}
--   \dfrac{n}{\frac dv+\frac{R}{v(k-n+1)}}, & n<k,\\[3mm]
--   \dfrac{k}{\frac dv+\frac{R}{2v}}, & n=k,\\[3mm]
--   \dfrac{k}{\frac dv+\frac{R}{v(n-k+1)}}, & n>k.
--   \end{cases}
--   $$
--
--   The numerator is the number of busy taxis; the denominator is the mean ride time $d/v$ plus the approximate expected en route time to the nearest idle taxi ($n<k$) or waiting passenger ($n>k$), and $R/(2v)$ when $n=k$. This is display (1).
--
--   **Formalization Note** The three cases are transcribed as printed, with $k-n+1$ and $n-k+1$ computed in $\mathbb R$. The value at $n=0$ is unused.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, §5.1, display (1), p. 16; model §3, pp. 7–8

import Mathlib

namespace OnDemandRideHailing.CallNoCall

/-- **Service rates (1) of the approximated one-direction call system.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, §5.1, display (1), p. 16:
`µ(1c)_n = n/(d/v + R/(v(k−n+1)))` if `n < k`; `k/(d/v + R/(2v))` if `n = k`;
`k/(d/v + R/(v(n−k+1)))` if `n > k`.

The model (§3, pp. 7–8): a circular road of perimeter `R > 0`, `k ≥ 1` taxis of constant speed
`v > 0`, Poisson passenger arrivals at rate `λ` at uniform locations, ride distances exponential
with mean `d > 0`. In the call mechanism a platform matches an arriving passenger to the nearest
available taxi (clockwise). In state `n` (passengers waiting or in service), the rate is the
number of busy servers `min(n, k)` over the mean pure ride time `d/v` plus the approximate
expected en route time: `R/(v(k−n+1))` for `n < k` (nearest of `k − n` idle taxis, p. 15),
`R/(v(n−k+1))` for `n > k` (nearest of `n − k` waiting passengers), and `R/(2v)` for `n = k`.

**Formalization Note.** Transcribed as printed, with the three cases of (1); `k − n + 1` and
`n − k + 1` are computed in `ℝ`. Index `n = 0` gives `0` and is unused by the queue formulas. -/
noncomputable def muCall1 (d v : ℝ) (k : ℕ) (R : ℝ) (n : ℕ) : ℝ :=
  if n < k then (n : ℝ) / (d / v + R / (v * ((k : ℝ) - n + 1)))
  else if n = k then (k : ℝ) / (d / v + R / (2 * v))
  else (k : ℝ) / (d / v + R / (v * ((n : ℝ) - k + 1)))

end OnDemandRideHailing.CallNoCall


