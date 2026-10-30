-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_Wnc
-- name    : OnDemandRideHailing_CallNoCall_Wnc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:18.529254+00:00
-- url     : https://prove2.me/theorems/fedc024d-7409-488b-9939-e67b1784a481
-- title:
--   Average waiting time $\mathcal W^{(nc)}(\lambda,d,v,k,R)$ of the approximated no-call system
-- statement:
--   $\mathcal W^{(nc)}(\lambda,d,v,k,R)$ is the average waiting time of the state-dependent M/M/k queue with arrival rate $\lambda$ and the no-call service rates $\mu^{(nc)}_n$ of display (3) (which themselves depend on $\lambda$), with the mean ride time $d/v$ subtracted:
--
--   $$
--   \mathcal W^{(nc)}(\lambda,d,v,k,R)=\mathcal W\big(\lambda,\tfrac dv,\mu^{(nc)}\big),
--   $$
--
--   which equals the waiting-time formula of p. 34 when the queue is stable and $+\infty$ otherwise. This is the paper's "average waiting time under the approximated no-call mechanism" (p. 19).
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, §5.2, p. 19; formula of p. 34 as used on p. 38

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
import Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula
import Definitions.Def_OnDemandRideHailing_CallNoCall_avgWait
import Definitions.Def_OnDemandRideHailing_CallNoCall_muNoCall

namespace OnDemandRideHailing.CallNoCall

/-- **`W^(nc)(λ, d, v, k, R)`: the average waiting time of the approximated no-call system.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, §5.2, p. 19 ("let `W^(nc)(λ, d, v, k, R)` be the average waiting time under the
approximated no-call mechanism"), with the formula of p. 34 (used for `W^(nc)` on p. 38).

It is the average waiting time `avgWait` of the state-dependent M/M/k queue with arrival rate
`λ` and service rates (3) (`muNoCall`, which themselves depend on `λ`), with mean ride time `d/v`
subtracted: the formula when the queue is stable, `+∞` otherwise. The approximation is the same
for the one- and two-direction no-call systems (p. 18). -/
noncomputable def Wnc (lam d v : ℝ) (k : ℕ) (R : ℝ) : EReal :=
  avgWait lam (d / v) (muNoCall lam d v k R)

end OnDemandRideHailing.CallNoCall


