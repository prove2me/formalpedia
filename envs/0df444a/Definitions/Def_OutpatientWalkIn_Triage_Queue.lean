-- Prove2me | Definitions.Def_OutpatientWalkIn_Triage_Queue
-- name    : OutpatientWalkIn_Triage_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:39.655616+00:00
-- url     : https://prove2.me/theorems/e1f5a9b4-7c16-4592-82d5-07671fedee13
-- title:
--   Online App. C — the M/D/1/K−1+p appointment queue: Poisson weights, Brun–Garcia a_j, b_j, a′_K (26), q_0 (27) and π(δ, µ_S), the probability that an arrival does not join (Corollary C.1)
-- statement:
--   This file defines the closed-form blocking probability of the appointment queue in the observable setting of Liu, van Jaarsveld, Wang and Xiao.
--
--   **The queue.** Strategic patients arrive as a Poisson process of rate $\lambda$ and are served by one deterministic server with $\mu_S$ appointment slots per day. A patient who sees $k$ patients waiting and one in service computes the delay $(k+\tilde u)/\mu_S$ with $\tilde u$ uniform on $[0,1]$, and joins if it is at most the threshold $\delta$. With $x=\delta\mu_S$, $K=\lceil x\rceil$ and $p=x+1-K\in(0,1]$ (for $x>0$), an arrival joins when the system holds fewer than $K$ patients, joins with probability $p$ when it holds exactly $K$, and is blocked otherwise: an M/D/1/K−1+p queue.
--
--   **Coefficients.** Put $\rho=\lambda/\mu_S$ and let $\alpha_j=\rho^j e^{-\rho}/j!$ be the probability of $j$ arrivals during a slot. Define $a_0=1$, $a_1=e^\rho-1$ and, for $j\ge2$,
--   $$a_j=e^\rho\Big(a_{j-1}-\sum_{i=1}^{j-1}\alpha_i a_{j-i}-\alpha_{j-1}a_0\Big),$$
--   and $b_j=\sum_{i=0}^{j}a_i$. For $0<p<1$ and $K\ge1$,
--   $$a'_K=(e^{p\rho}-1)(1-p)^{-K+1}+(e^{p\rho}-pe^{p\rho}-1)\sum_{i=1}^{K-1}(b_i-b_{i-1})(1-p)^{-K+i}. \tag{26}$$
--   The departure-epoch probability of an empty system is $q_0=1/b_K$ when $p=1$ and $q_0=1/(b_{K-1}+a'_K)$ when $0<p<1$ (27).
--
--   **Blocking probability** (Corollary C.1). For $\mu_S>0$ and $\delta\ge0$,
--   $$\pi(\delta,\mu_S)=1-\frac{1}{q_0+\rho}.$$
--   With no appointment capacity, $\pi(\delta,0)=1$: every strategic patient is blocked.
--
--   The blocking probability is the only queueing quantity the comparison of the triage and strategic models uses: it is the fraction of strategic patients who do not schedule.
--
--   **Formalization Note** The recursion for $a_j$ is defined for every $j$ in the printed two-clause form ($a_0$, $a_1$, and the recursion for $j\ge2$); the paper uses it for $j\le K$. The negative powers of (26) are written as inverses of natural powers, $((1-p)^{K-1})^{-1}$ and $((1-p)^{K-i})^{-1}$ with $1\le i\le K-1$. The case split $p=1$ versus $p<1$ is explicit, so $(1-p)^{-n}$ is never evaluated at $p=1$. At $\delta=0$ the formula gives $K=0$, $p=1$, $q_0=1/b_0=1$ and $\pi=\rho/(1+\rho)$, the M/D/1/1 loss probability. The value $\pi=1$ is also returned for $\mu_S\le0$ (the paper's convention at $\mu_S=0$; negative rates never occur) and for a negative threshold $\delta<0$, which the paper never uses (a patient with a negative threshold never schedules).
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix pp. 5–7, §C, §C.1, §C.2, (24), (26), (27), Corollary C.1

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue

namespace OutpatientWalkIn.Triage

open Finset

/-- The blocking probability `π(δ, μ_S)` of the observable appointment queue with arrival rate
`lam`, service rate `μS` and delay threshold `δ` (Corollary C.1, Online Appendix p. 7): with
`x = δ μ_S`, `K = ⌈x⌉`, `p = x + 1 - K`, `ρ = λ/μ_S`,
`π(δ, μ_S) = 1 - 1/(q_0 + ρ)`.
Conventions: with no appointment capacity (`μS ≤ 0`) every arrival is blocked, `π = 1`; a negative
threshold (never used by the paper) also gives `π = 1`. At `δ = 0` the formula gives `K = 0`,
`p = 1`, `q_0 = 1/b_0 = 1`, so `π = ρ/(1+ρ)`. -/
noncomputable def blockProb (lam δ μS : ℝ) : ℝ :=
  if μS ≤ 0 ∨ δ < 0 then 1
  else
    1 - 1 / (OutpatientWalkIn.SmallCap.q0 ⌈δ * μS⌉₊ (δ * μS + 1 - (⌈δ * μS⌉₊ : ℝ)) (lam / μS) + lam / μS)

end OutpatientWalkIn.Triage


