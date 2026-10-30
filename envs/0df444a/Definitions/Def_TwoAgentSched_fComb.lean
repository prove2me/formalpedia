-- Prove2me | Definitions.Def_TwoAgentSched_fComb
-- name    : TwoAgentSched_fComb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:46:22.539609+00:00
-- url     : https://prove2.me/theorems/7161af02-aa28-4701-9e7e-4db83bd2e2ad
-- title:
--   Combined single-agent cost of the reduction to $1|prec|f_{\max}$
-- statement:
--   Given agent $A$'s cost functions $f^A_h$, agent $B$'s cost functions $f^B_k$ and the bound $Q$, the reduction of §4 assigns to every job $i \in J^A\cup J^B$ the cost function
--   $$
--   f_i(t) = \begin{cases} f^A_i(t) & \text{if } i \in J^A, \\ \infty & \text{if } i \in J^B \text{ and } f^B_i(t) > Q, \\ -\infty & \text{if } i \in J^B \text{ and } f^B_i(t) \le Q, \end{cases}
--   $$
--   and, for completion times $C$, the single-agent objective
--   $$
--   f_{\max}(C) = \max_{i\in J^A\cup J^B} f_i(C_i).
--   $$
--
--   A schedule with finite $f_{\max}$ meets agent $B$'s constraint, and then $f_{\max}=f^A_{\max}$; this is how the two-agent problem becomes the classical problem $1|prec|f_{\max}$.
--
--   **Formalization Note** `fComb` takes values in `EReal` and is defined for every real `t` (the paper defines it for `t ≥ 0`; completion times of feasible schedules are ≥ 0). `combMax` is the finite supremum over all jobs.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, p. 232 (definition of f_i(t) and f_max)

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible

namespace TwoAgentSched

open Classical in
/-- **The combined single-agent cost** of the reduction (§4, p. 232):
`f_i(t) = f^A_i(t)` for an A-job, `∞` for a B-job with `f^B_i(t) > Q`, and `−∞` for a B-job
with `f^B_i(t) ⩽ Q`. -/
noncomputable def fComb {nA nB : ℕ} (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ) :
    Job nA nB → ℝ → EReal
  | Sum.inl h, t => ((fA h t : ℝ) : EReal)
  | Sum.inr k, t => if Q < fB k t then ⊤ else ⊥

/-- `f_max = max_{i ∈ J^A ∪ J^B} f_i(C_i)` (§4, p. 232) for completion times `C`. -/
noncomputable def combMax {nA nB : ℕ} (fA : Fin nA → ℝ → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (C : Job nA nB → ℝ) : EReal :=
  Finset.univ.sup fun j => fComb fA fB Q j (C j)

end TwoAgentSched


