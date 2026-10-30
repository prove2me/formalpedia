-- Prove2me | Definitions.Def_TwoAgentSched_fAmax
-- name    : TwoAgentSched_fAmax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:45:32.792373+00:00
-- url     : https://prove2.me/theorems/bd1f1404-f1eb-4a82-9a52-3eee64b06913
-- title:
--   Agent A's objective $f^A_{\max}$ and agent B's constraint $f^B_{\max}\le Q$
-- statement:
--   Let $C$ assign a completion time $C_j$ to every job.
--
--   1. Agent $A$'s objective is the **maximum of regular functions**
--   $$
--   f^A_{\max}(C) = \max_{h=1,\dots,n_A} f^A_h\bigl(C^A_h\bigr),
--   $$
--   where each $f^A_h$ is a real function of the completion time of $J^A_h$.
--   2. Agent $B$'s constraint $f^B_{\max}(C)\le Q$ holds when every B-job satisfies
--   $$
--   f^B_k\bigl(C^B_k\bigr) \le Q, \qquad k = 1,\dots,n_B .
--   $$
--
--   Problem CP asks to minimize $f^A_{\max}$ over the feasible schedules satisfying $f^B_{\max}\le Q$.
--
--   **Formalization Note** `fAmax` takes values in the extended reals (`EReal`) as a finite supremum, so it is $-\infty$ when agent $A$ has no jobs; for $n_A\ge1$ it is the real maximum. `BOk` is written without a maximum, so for $n_B = 0$ it holds trivially.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §3, p. 231 (f_max = max_i f_i(C_i(σ))); problem CP, p. 232 (f^B(σ*) ⩽ Q, f^A(σ*) minimum)

import Mathlib
import Definitions.Def_TwoAgentSched_Feasible

namespace TwoAgentSched

/-- **Agent A's objective** `f^A_max = max_h f^A_h(C^A_h)` (§3, p. 231) for completion times
`C`, as an extended real; it is `⊥` when agent A has no jobs (`n_A = 0`). -/
noncomputable def fAmax {nA nB : ℕ} (fA : Fin nA → ℝ → ℝ) (C : Job nA nB → ℝ) : EReal :=
  Finset.univ.sup fun h => ((fA h (C (Sum.inl h)) : ℝ) : EReal)

/-- **Agent B's constraint** `f^B_max ≤ Q` (problem CP, p. 232) for completion times `C`:
every B-job satisfies `f^B_k(C^B_k) ≤ Q`. -/
def BOk {nA nB : ℕ} (fB : Fin nB → ℝ → ℝ) (Q : ℝ) (C : Job nA nB → ℝ) : Prop :=
  ∀ k, fB k (C (Sum.inr k)) ≤ Q

end TwoAgentSched


