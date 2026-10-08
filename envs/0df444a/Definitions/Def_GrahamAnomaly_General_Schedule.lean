-- Prove2me | Definitions.Def_GrahamAnomaly_General_Schedule
-- name    : GrahamAnomaly_General_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:28:39.451605+00:00
-- url     : https://prove2.me/theorems/2242f712-ed57-4487-85a1-2698cb0ba509
-- title:
--   §2, p. 416 — feasible nonpreemptive schedules and their finishing time
-- statement:
--   For a finite task set $T_1,\ldots,T_r$ with durations $\mu(T_j)$, a precedence relation $\prec$, and $n$ identical processors, a **feasible schedule** assigns task $j$ a processor $P_j$ and a nonnegative start time $S_j$. It runs continuously on the half-open interval $[S_j,S_j+\mu(T_j))$. Distinct tasks assigned to the same processor have disjoint running intervals, and $T_i\prec T_j$ requires $S_i+\mu(T_i)\le S_j$. The **finishing time** is
--
--   $$\omega=\max_j\bigl(S_j+\mu(T_j)\bigr).$$
--
--   This reusable schedule object records feasibility independently of how tasks are selected. Graham's priority-list rule is defined in the following item.
--
--   **Formalization Note** Tasks and processors are 0-based finite types. A task set with no elements has finishing time $0$; the ratio theorem assumes $r>0$. Positive processing times and a strict precedence order are hypotheses of the theorems rather than fields of this general schedule object.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 416, §2 Description of the system; https://doi.org/10.1137/0117039

import Mathlib

namespace GrahamAnomaly.General

/-- A feasible nonpreemptive execution of the tasks `Fin r` on `n` identical processors.
Task `j` occupies `[S j, S j + μ j)` on processor `P j`. -/
structure Schedule {r : ℕ} (n : ℕ) (μ : Fin r → ℝ)
    (prec : Fin r → Fin r → Prop) where
  S : Fin r → ℝ
  P : Fin r → Fin n
  nonneg : ∀ j, 0 ≤ S j
  noOverlap : ∀ i j, P i = P j → i ≠ j →
    S i + μ i ≤ S j ∨ S j + μ j ≤ S i
  precedence : ∀ i j, prec i j → S i + μ i ≤ S j

namespace Schedule

/-- The least time at which every task has completed, or zero for no tasks. -/
noncomputable def finish {r n : ℕ} {μ : Fin r → ℝ}
    {prec : Fin r → Fin r → Prop} (G : Schedule n μ prec) : ℝ :=
  if h : (Finset.univ : Finset (Fin r)).Nonempty then
    Finset.univ.sup' h (fun j => G.S j + μ j)
  else 0

end Schedule

end GrahamAnomaly.General


