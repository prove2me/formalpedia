-- Prove2me | Definitions.Def_IgnallSchrage_Makespan_LowerBound
-- name    : IgnallSchrage_Makespan_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:15:26.046195+00:00
-- url     : https://prove2.me/theorems/5c490cce-b6f1-4164-b4a3-997d8218c044
-- title:
--   The three-machine lower bound $LB(J_r)$ (p. 401)
-- statement:
--   For a node $J_r$ (a partial sequence of $r$ jobs) with unscheduled set $\bar J_r \neq \emptyset$, Ignall and Schrage's lower bound is
--
--   $$
--   LB(J_r)=\max\Big[\,\mathrm{TIMEA}(J_r)+\sum_{i\in\bar J_r}a_i+\min_{i\in\bar J_r}(b_i+c_i),\ \ \mathrm{TIMEB}(J_r)+\sum_{i\in\bar J_r}b_i+\min_{i\in\bar J_r}c_i,\ \ \mathrm{TIMEC}(J_r)+\sum_{i\in\bar J_r}c_i\,\Big],
--   $$
--
--   where $a_i,b_i,c_i$ are the processing times of job $i$ on machines $A,B,C$ and $\mathrm{TIMEA},\mathrm{TIMEB},\mathrm{TIMEC}$ are the node attributes.
--
--   Each of the three terms follows one machine: it adds to the time that machine becomes free the work still to be done on it, and the work that must still follow on the later machines for at least one job. The bound is the ranking key of the branch-and-bound procedure for the makespan.
--
--   **Formalization Note** The minima are `Finset.inf'` over $\bar J_r$ when $\bar J_r$ is nonempty. On the empty set the auxiliary minimum returns the placeholder $0$; no statement of the mission uses that value, because the bound is evaluated only at nodes with at most $n-1$ jobs (the procedure stops at depth $n-1$, and every theorem about the bound assumes $r<n$). In the scan the bars over $\bar J_r$ in the six subscripts are not visible; the text below the display defines $\bar J_r$ and the subscripts range over it.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 401, "A Lower Bound for the Makespan of All Nodes Emanating from a Given Node", LB(J_r)

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Makespan

/-- The minimum of `f` over a finite set of jobs `s`, `min_{i ∈ s} f i`, when `s` is nonempty
(`Finset.inf'`). The value `0` on the empty set is a placeholder: every statement of the
mission evaluates it only on a nonempty `s`. -/
def minOver {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℝ) : ℝ :=
  if h : s.Nonempty then s.inf' h f else 0

/-- The lower bound of Ignall and Schrage (p. 401) of a node `J = J_r` with `J̄_r` its set of
unscheduled jobs:
`LB(J_r) = max [ TIMEA(J_r) + Σ_{J̄_r} a_i + min_{J̄_r} (b_i + c_i),
                 TIMEB(J_r) + Σ_{J̄_r} b_i + min_{J̄_r} c_i,
                 TIMEC(J_r) + Σ_{J̄_r} c_i ]`.
It is meant for nodes with `J̄_r` nonempty (`r ≤ n - 1`), where the minima are genuine
minima; the procedure never evaluates it at a node with `J̄_r = ∅`. -/
def lowerBound {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n)) : ℝ :=
  let t := times a b c J
  let U := unscheduled J
  max (t.1 + (∑ i ∈ U, a i) + minOver U (fun i => b i + c i))
    (max (t.2.1 + (∑ i ∈ U, b i) + minOver U c)
      (t.2.2 + ∑ i ∈ U, c i))

end IgnallSchrage.Makespan


