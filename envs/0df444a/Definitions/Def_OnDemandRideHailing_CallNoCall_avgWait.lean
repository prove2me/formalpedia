-- Prove2me | Definitions.Def_OnDemandRideHailing_CallNoCall_avgWait
-- name    : OnDemandRideHailing_CallNoCall_avgWait
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:57:23.145441+00:00
-- url     : https://prove2.me/theorems/fb756348-8cf6-4cf7-836b-8905da097224
-- title:
--   Average waiting time of a state-dependent M/M/k queue, $+\infty$ when unstable
-- statement:
--   The **average waiting time** of the state-dependent M/M/k queue with arrival rate $\lambda$, service rates $\mu_1,\mu_2,\dots$ and mean ride time $s$ is the extended real number
--
--   $$
--   \mathcal W(\lambda,s,\mu)=\begin{cases}
--   \dfrac{\sum_{i\ge1} i\lambda^{i-1}/(\mu_1\cdots\mu_i)}{1+\sum_{i\ge1}\lambda^{i}/(\mu_1\cdots\mu_i)}-s, & \text{if the queue is stable},\\[2mm]
--   +\infty, & \text{otherwise}.
--   \end{cases}
--   $$
--
--   This is the convention of the proof of Theorem 1, Part 1 (p. 34): $\mathcal W<\infty$ exactly when both series are finite, and $\mathcal W=\infty$ otherwise.
--
--   **Formalization Note** The value is an `EReal`; the subtraction of $s$ is carried out in $\mathbb R$ inside the stable branch.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, proof of Theorem 1, Part 1, p. 34

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
import Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula

namespace OnDemandRideHailing.CallNoCall

/-- **The average waiting time of a state-dependent M/M/k queue, `+∞` when unstable.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, proof of Theorem 1, Part 1, p. 34: the formula
`W = Σ_{i=1}^∞ iλ^{i−1}/(µ1⋯µi) / (1 + Σ_{i=1}^∞ λ^i/(µ1⋯µi)) − d/v`, with "`W < ∞`" equivalent to
both series being finite and "`W(λ, d, v, k, R) = ∞`" otherwise.

`avgWait lam s μ` is `waitFormula lam s μ` (an extended real) when `QueueStable lam μ`, and `⊤`
(`+∞`) otherwise.

**Formalization Note.** The value lives in `EReal` so that an unstable queue has waiting time
`+∞`, as on p. 34. The subtraction of `s` is done in `ℝ`, inside the stable branch; no `EReal`
arithmetic is involved. -/
noncomputable def avgWait (lam s : ℝ) (μ : ℕ → ℝ) : EReal :=
  open Classical in
  if QueueStable lam μ then ((waitFormula lam s μ : ℝ) : EReal) else ⊤

end OnDemandRideHailing.CallNoCall


