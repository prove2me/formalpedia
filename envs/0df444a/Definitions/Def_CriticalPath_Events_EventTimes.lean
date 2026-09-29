-- Prove2me | Definitions.Def_CriticalPath_Events_EventTimes
-- name    : CriticalPath_Events_EventTimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:25:25.95771+00:00
-- url     : https://prove2.me/theorems/c834ec26-2f40-45fa-a742-c269b3ecc857
-- title:
--   Earliest and latest event times (1), (2); maximum time available; critical jobs, floaters and critical paths
-- statement:
--   Let $P$ be a project network with events $0,\dots,n$ ($n\ge1$), and let $y_{ij} \in \mathbb R$ be the duration of job $(i,j)$ (only the values on jobs $(i,j)\in P$ are used).
--
--   **Earliest event times** (display (1)). The earliest time $t_i^{(0)}$ of event $i$ is defined recursively on the label:
--   $$
--   t_0^{(0)} = 0, \qquad t_j^{(0)} = \max\,[\,y_{ij} + t_i^{(0)} \mid i<j,\ (i,j)\in P\,], \quad 1 \le j \le n.
--   $$
--
--   **Latest event times** (display (2)). For a project completion time $\lambda\in\mathbb R$, the latest time $t_i^{(1)}$ of event $i$ is defined recursively downward on the label:
--   $$
--   t_n^{(1)} = \lambda, \qquad t_i^{(1)} = \min\,[\,t_j^{(1)} - y_{ij} \mid i<j,\ (i,j)\in P\,], \quad 0 \le i \le n-1.
--   $$
--   Both the maximum and the minimum range over nonempty sets, because every event but the origin has a predecessor and every event but the terminus has a successor.
--
--   **Maximum time available** for job $(i,j)$: $t_j^{(1)} - t_i^{(0)}$.
--
--   **Critical job.** Job $(i,j)$ is *critical* if its maximum time available equals its duration, $t_j^{(1)} - t_i^{(0)} = y_{ij}$. It is a **floater** if its maximum time available exceeds its duration, $t_j^{(1)} - t_i^{(0)} > y_{ij}$.
--
--   **Critical path.** A *critical path* is a contiguous path of critical jobs through the project diagram from origin to terminus: a list of events $v_0, v_1, \dots, v_k$ with $v_0 = 0$, $v_k = n$, and every consecutive pair $(v_{r-1}, v_r)$ a job of $P$ that is critical.
--
--   These are the quantities with which Kelley and Walker analyse a project in the deterministic case; the mission's theorems are stated in terms of them.
--
--   **Formalization Note** $t^{(0)}$ is `earliest N y` and $t^{(1)}$ is `latest N y λ`; both are defined by well-founded recursion on the label (upward, respectively downward), with `Finset.sup'` / `Finset.inf'` over the predecessor / successor set and its nonemptiness proof, so no fallback value exists. `latest` is defined for every real $\lambda$; the paper's assumption $\lambda \ge t_n^{(0)}$ is a hypothesis of the theorems. `IsCritical` and `IsFloater` are stated for any ordered pair of events; the theorems apply them to jobs $e \in P$. A critical path is a `List` whose `head?` is $0$, whose `getLast?` is $n$, and which satisfies `List.IsChain` for "is a job of $P$ and is critical"; since $0 \ne n$ such a list has at least two events.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, pp. 162-163, §2 Calendar Limits on Activities, The Deterministic Case, displays (1) and (2), table of job quantities (Maximum time available), definitions of critical job, floater and critical-path

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork

namespace CriticalPath.Events

variable {n : ℕ}

/-- Earliest event times, Kelley–Walker (1959) display (1), p. 163:
`t_0^(0) = 0`, `t_j^(0) = max [y_ij + t_i^(0) | i < j, (i,j) ∈ P]` for `1 ≤ j ≤ n`.
The maximum is over a nonempty set by `ProjectNetwork.pred_nonempty`; no fallback value is used. -/
noncomputable def earliest (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) : ℝ :=
  if h : j = 0 then 0
  else (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty h))
    (fun i => y i.1 j + earliest N y i.1)
termination_by j.val
decreasing_by exact N.lt_of_mem_pred i.2

/-- Latest event times relative to a project completion time `λ`, Kelley–Walker (1959)
display (2), p. 163: `t_n^(1) = λ`, `t_i^(1) = min [t_j^(1) − y_ij | i < j, (i,j) ∈ P]`
for `0 ≤ i ≤ n − 1`. The minimum is over a nonempty set by `ProjectNetwork.succ_nonempty`. -/
noncomputable def latest (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (i : Fin (n + 1)) : ℝ :=
  if h : i = Fin.last n then lam
  else (N.succ i).attach.inf' (Finset.attach_nonempty_iff.2 (N.succ_nonempty h))
    (fun j => latest N y lam j.1 - y i j.1)
termination_by n - i.val
decreasing_by
  have h1 := N.lt_of_mem_succ j.2
  have h2 := j.1.is_le
  rw [Fin.lt_def] at h1
  omega

/-- Maximum time available for job `(i, j)`: `t_j^(1) − t_i^(0)` (p. 163). -/
noncomputable def maxTimeAvailable (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (e : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  latest N y lam e.2 - earliest N y e.1

/-- A job is critical if its maximum time available equals its duration (p. 163). -/
def IsCritical (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (e : Fin (n + 1) × Fin (n + 1)) : Prop :=
  maxTimeAvailable N y lam e = y e.1 e.2

/-- A job is a floater if its maximum time available exceeds its duration (p. 163). -/
def IsFloater (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (e : Fin (n + 1) × Fin (n + 1)) : Prop :=
  y e.1 e.2 < maxTimeAvailable N y lam e

/-- A critical path (p. 163): a contiguous path of critical jobs through the project diagram
from origin to terminus, given as its list of events `v_0 = 0, v_1, …, v_k = n`, every
consecutive pair `(v_{r-1}, v_r)` being a job of `P` that is critical. -/
def IsCriticalPath (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (lam : ℝ)
    (p : List (Fin (n + 1))) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some (Fin.last n) ∧
    p.IsChain (fun i j => (i, j) ∈ N.P ∧ IsCritical N y lam (i, j))

end CriticalPath.Events


