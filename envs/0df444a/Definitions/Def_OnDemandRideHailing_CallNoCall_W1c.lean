-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_W1c
-- name    : OnDemandRideHailing_CallNoCall_W1c
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:58:37.822351+00:00
-- url     : https://prove2.me/theorems/a89711ed-181b-4ea8-901b-e45ef14e1873
-- title:
--   Average waiting time $\mathcal W^{(1c)}(\lambda,d,v,k,R)$ of the approximated one-direction call system
-- statement:
--   $\mathcal W^{(1c)}(\lambda,d,v,k,R)$ is the average waiting time of the state-dependent M/M/k queue with arrival rate $\lambda$ and the call service rates $\mu^{(1c)}_n$ of display (1), with the mean ride time $d/v$ subtracted:
--
--   $$
--   \mathcal W^{(1c)}(\lambda,d,v,k,R)=\mathcal W\big(\lambda,\tfrac dv,\mu^{(1c)}\big),
--   $$
--
--   which equals the waiting-time formula of p. 34 when the queue is stable and $+\infty$ otherwise. This is the paper's "average waiting time under the approximation scheme" for the one-direction call system (p. 16).
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, §5.1, p. 16; formula of the proof of Theorem 1, Part 1, p. 34

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
import Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula
import Definitions.Def_OnDemandRideHailing_CallNoCall_avgWait
import Definitions.Def_OnDemandRideHailing_CallNoCall_muCall1

namespace OnDemandRideHailing.CallNoCall

/-- **`W^(1c)(λ, d, v, k, R)`: the average waiting time of the approximated one-direction call
system.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, §5.1, p. 16 ("let `W^(1c)(λ, d, v, k, R)` be the average waiting time under the
approximation scheme given parameters `λ, d, v, k` and `R`"), with the formula of the proof of
Theorem 1, Part 1, p. 34.

It is the average waiting time `avgWait` of the state-dependent M/M/k queue with arrival rate
`λ` and service rates (1) (`muCall1`), with mean ride time `d/v` subtracted: the formula when the
queue is stable, `+∞` otherwise. -/
noncomputable def W1c (lam d v : ℝ) (k : ℕ) (R : ℝ) : EReal :=
  avgWait lam (d / v) (muCall1 d v k R)

end OnDemandRideHailing.CallNoCall


