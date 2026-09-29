-- Prove2me | Definitions.Def_CriticalPath_CostCurve_earliest
-- name    : CriticalPath_CostCurve_earliest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:29:24.223377+00:00
-- url     : https://prove2.me/theorems/98ef5fbd-a1b2-4533-95e8-e3abc46b4610
-- title:
--   Earliest event times $t_j^{(0)}$, recursion (1)
-- statement:
--   Let a project network with events $0,\dots,n$ and jobs $P$ be given, and let $y = (y_{ij})$ be job durations. The **earliest event times** $t_j^{(0)} = t_j^{(0)}(y)$ are defined by the recursion (1) of Kelley and Walker:
--
--   $$
--   t_0^{(0)} = 0, \qquad t_j^{(0)} = \max\,[\,y_{ij} + t_i^{(0)} \mid i < j,\ (i,j) \in P\,], \quad 1 \le j \le n.
--   $$
--
--   The recursion is well founded because every predecessor $i$ of $j$ has a smaller label. The number $t_n^{(0)}(y)$ is the **earliest project completion time** for the durations $y$.
--
--   **Formalization Note** The recursion is on the label `j.val`, with the maximum taken as `Finset.sup'` over the predecessor set $\{i : i < j,\ (i,j) \in P\}$. An event with no predecessor is given the value $0$: this is exactly $t_0^{(0)} = 0$ for the origin, and for $j \ge 1$ the case never occurs, because the origin precedes every event, so the last job of a path from $0$ to $j$ is a predecessor of $j$. Only the values $y_{ij}$ with $(i,j) \in P$ are read.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 163, Part I §2 The Deterministic Case, display (1)

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork

namespace CriticalPath.CostCurve

variable {n : ℕ}

/-- The predecessors of event `j`: the events `i` with `i < j` and `(i, j) ∈ P`. -/
def preds (N : ProjectNetwork n) (j : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i < j ∧ (i, j) ∈ N.P)

/-- Earliest event times, recursion (1) of Kelley–Walker (1959), p. 163, for durations `y`:
`t₀⁽⁰⁾ = 0` and `tⱼ⁽⁰⁾ = max [yᵢⱼ + tᵢ⁽⁰⁾ | i < j, (i, j) ∈ P]` for `1 ≤ j ≤ n`.
An event with no predecessor gets `0`; this covers the origin (`t₀⁽⁰⁾ = 0`), and for `j ≥ 1` it is
unreachable, because origin precedes every event (`ProjectNetwork.origin_precedes`). -/
noncomputable def earliest (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ
  | j =>
    if h : (preds N j).Nonempty then
      (preds N j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        (fun i => y i.1 j + earliest N y i.1)
    else 0
termination_by j => j.val
decreasing_by
  exact (Finset.mem_filter.mp i.2).2.1

end CriticalPath.CostCurve


