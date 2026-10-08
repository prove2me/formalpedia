-- Prove2me | Definitions.Def_TwoAgentSched_MaxMax_Reduction
-- name    : TwoAgentSched_MaxMax_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:46.281687+00:00
-- url     : https://prove2.me/theorems/7d4d440a-5c0e-48cf-b7bd-409d01f57659
-- title:
--   §4: the single-agent costs $f_i$ with values $\pm\infty$ for B-jobs, and the objective $f_{\max}$ of $1|prec|f_{\max}$
-- statement:
--   §4 reduces $1\|f^A_{\max} : f^B_{\max}\le Q$ to a single-agent problem in which every job, of either agent, has one cost function $f_i$ with values in the extended reals $[-\infty,+\infty]$:
--   $$
--   f_i(t)=\begin{cases} f^A_i(t) & \text{if } i\in J^A,\\ +\infty & \text{if } i\in J^B \text{ and } f^B_i(t)>Q,\\ -\infty & \text{if } i\in J^B \text{ and } f^B_i(t)\le Q.\end{cases}
--   $$
--   The objective of the single-agent problem is
--   $$f_{\max}(\sigma)=\max_{i\in J^A\cup J^B} f_i\big(C_i(\sigma)\big).$$
--   A B-job thus costs nothing when it meets agent B's bound and makes the schedule infinitely bad when it does not, while A-jobs keep their own costs.
--
--   **Formalization Note** Values are in Lean's `EReal`, with $\bot=-\infty$ and $\top=+\infty$; only the maximum and the order are used, never addition. The paper defines $f_i(t)$ for $t\ge0$; the Lean function is defined for every real $t$ and is only evaluated at completion times. The maximum over the job set is `Finset.sup`, whose value on an empty job set would be $-\infty$; the theorems that use it assume $n_A\ge1$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 232, §4, the display defining f_max and f_i(t)

import Mathlib
import Definitions.Def_TwoAgentSched_MaxMax_Model

namespace TwoAgentSched.MaxMax

/-- The single-agent cost functions of the reduction of §4 (p. 232), with values in the extended
reals `[-∞, +∞]`:
`f_i(t) = f^A_i(t)` for an A-job, `+∞` for a B-job with `f^B_i(t) > Q`, and `−∞` for a B-job
with `f^B_i(t) ≤ Q`. -/
noncomputable def reducedCost {nA nB : ℕ} (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ) :
    Job nA nB → ℝ → EReal
  | Sum.inl h, t => (fA h t : EReal)
  | Sum.inr k, t => if fB k t ≤ Q then ⊥ else ⊤

/-- The objective `f_max(σ) = max_{i ∈ J^A ∪ J^B} f_i(C_i(σ))` of the single-agent problem
`1|prec|f_max` of the reduction of §4 (p. 232), in the extended reals (the maximum over the
finite job set; `⊥ = −∞` would be the value on an empty job set). -/
noncomputable def reducedMax {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (l : List (Job nA nB)) : EReal :=
  Finset.univ.sup (fun j => reducedCost fA fB Q j (MooreLateJobs.Shared.completionTime p l j))

end TwoAgentSched.MaxMax


