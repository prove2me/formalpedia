-- Prove2me | Definitions.Def_IgnallSchrage_Invariance_Node
-- name    : IgnallSchrage_Invariance_Node
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:59.417914+00:00
-- url     : https://prove2.me/theorems/45cd337e-9548-4c55-b553-56d75a5767c2
-- title:
--   Unscheduled jobs $\bar J_r$, minima over $\bar J_r$, and the change of units $\tilde x_i = H(x'_i+G)$
-- statement:
--   Three small objects used throughout the mission.
--
--   1. For a node $J_r$ (a list of jobs in processing order), $\bar J_r$ is the set of jobs that do not occur in $J_r$ (p. 401: "the set of $n-r$ jobs that have not been assigned a position in sequence $J_r$").
--   2. For a nonempty set $s$ of jobs and a function $f$ on jobs, $\min_{i\in s} f(i)$ is the least value of $f$ on $s$.
--   3. The **change of location and scale** of the Appendix (p. 411). From processing times $x'_i$ of a problem $P'$ and constants $H,G$, the processing times of $\tilde P$ are
--   $$
--   \tilde x_i = H\,(x'_i + G),
--   $$
--   obtained by first adding $G$ and then multiplying by $H$.
--
--   **Formalization Note** The minimum is `Finset.inf'` on a nonempty set. On the empty set the definition returns the placeholder $0$, which no statement of the mission uses, since every node the bounds are evaluated at has $\bar J_r\neq\emptyset$.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 401 (J̄_r) and p. 411, Appendix, THEOREM (ã_i=H(a_i′+G))

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Invariance

/-- The change of location and scale of the Appendix (p. 411): from processing times `x'` of
problem `P'`, the processing times `x̃_i = H (x'_i + G)` of problem `P̃` (first add `G`, then
multiply by `H`). -/
def shiftScale {n : ℕ} (H G : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => H * (x i + G)

end IgnallSchrage.Invariance


