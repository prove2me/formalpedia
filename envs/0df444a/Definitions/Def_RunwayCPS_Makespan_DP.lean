-- Prove2me | Definitions.Def_RunwayCPS_Makespan_DP
-- name    : RunwayCPS_Makespan_DP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:25.883717+00:00
-- url     : https://prove2.me/theorems/84789fa4-0dab-4c49-bfca-8c9b264753db
-- title:
--   §4.1, Table 2, Eq. (1): the dynamic program $T^*$, partial schedules, and the makespan
-- statement:
--   This file defines the dynamic programming recursion of §4.1 on the pruned CPS network $G$, the independent "earliest landing time" quantity it is meant to compute, and the makespan.
--
--   For a node $i$ of $G$ write $e(i)$, $l(i)$ for the earliest and latest time of its final aircraft, $\delta_i(j)$ for the minimum separation between the final aircraft of $i$ (leading) and of $j$ (trailing), and $P(j)$ for the set of nodes of the previous stage with an arc into $j$.
--
--   **The recursion.** By recursion on the stage $p$: at stage $1$, $T^*(j)=e(j)$; at stage $p+1$,
--
--   $$T^*(j)=\max\Big\{e(j),\ \min_{i\in P(j):\,T^*(i)\le l(i)}\big(T^*(i)+\delta_i(j)\big)\Big\},$$
--
--   with values in $\mathbb R\cup\{+\infty\}$ and the minimum over an empty family equal to $+\infty$.
--
--   **Partial schedules.** For a stage-$p$ node $j$ of $G$, a **partial schedule ending at $j$** is a path $v_1,\dots,v_p=j$ in $G$ (nodes of stages $1,\dots,p$, consecutive nodes joined by arcs) with times $t_1,\dots,t_p$ such that
--
--   1. $e(v_q)\le t_q\le l(v_q)$ for $q<p$;
--   2. $e(j)\le t_p$ (the latest time of $j$ itself is not imposed);
--   3. $\delta_{v_q}(v_r)\le t_r-t_q$ for all $1\le q<r\le p$.
--
--   The set $\mathrm{arr}(p,j)$ collects the times $t_p$ of all partial schedules ending at $j$. Its least element, when it exists, is the earliest possible landing time of the final aircraft of $j$: the quantity Table 2 calls $T^*(j)$, "arrival time of the final aircraft of node $i$ in an optimal solution".
--
--   **Makespan.** The makespan of a schedule is the landing time of the aircraft in the last position.
--
--   The recursion and the set $\mathrm{arr}(p,j)$ are defined independently, so that Lemma 3 is a genuine statement relating them.
--
--   **Formalization Note** Values of the recursion lie in `WithTop ℝ`, with $\top=+\infty$: then $\top+x=\top$, $\max\{x,\top\}=\top$, and the filter $T^*(i)\le l(i)$ excludes $\top$. The recursion is set to $\top$ at the non-stage $p=0$. Stages are 1-based; the last position is the 0-based position $n-1$.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1654–1655, §4, Table 2, Lemma 3 Eq. (1), §4.1 boundary condition, Figure 2

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_Network

namespace RunwayCPS.Makespan

variable {n : ℕ}

open Classical in
/-- The dynamic programming recursion (1) of Lemma 3 on the pruned network `G`, with the
boundary condition of §4.1, by recursion on the (1-based) stage `p`:
* stage 1: `T*(j) = e(j)`;
* stage `p + 1`: `T*(j) = max { e(j), min_{i ∈ P(j) : T*(i) ≤ l(i)} (T*(i) + δ_i(j)) }`, where
  `P(j)` is the set of stage-`p` nodes of `G` with an arc into `j`, `e(j)`, `l(j)` are the window
  of the final aircraft of `j`, and `δ_i(j)` is the separation between the final aircraft of `i`
  (leading) and of `j` (trailing).
Values live in `WithTop ℝ`; `⊤` is `+∞`, and the minimum over an empty family is `⊤`. Stage 0
is not a stage of the network and is set to `⊤`. -/
noncomputable def T [NeZero n] (I : Instance n) : ℕ → List (Fin n) → WithTop ℝ
  | 0, _ => ⊤
  | 1, j => ((I.e (final j) : ℝ) : WithTop ℝ)
  | p + 2, j =>
      max ((I.e (final j) : ℝ) : WithTop ℝ)
        (((GNodes I (p + 1)).filter
            (fun i => IsArc I.k (p + 1) i j ∧ T I (p + 1) i ≤ ((I.l (final i) : ℝ) : WithTop ℝ))).inf
          (fun i => T I (p + 1) i + ((I.δ (final i) (final j) : ℝ) : WithTop ℝ)))

/-- The earliest-arrival meaning of `T*(j)` (Table 2), defined independently of the
recursion: the set of landing times `t p` of the final aircraft of the stage-`p` node `j` over
all **partial schedules ending at `j`**, i.e. paths `v 1, …, v p = j` in `G` (consecutive
arcs) with times `t 1, …, t p` such that the aircraft at stages `q < p` land inside their
windows, the final aircraft of `j` lands no earlier than its earliest time (its latest time is
not imposed), and every pair of stages `q < r ≤ p` respects the minimum separation. -/
def arrivals [NeZero n] (I : Instance n) (p : ℕ) (j : List (Fin n)) : Set ℝ :=
  {τ | ∃ (v : ℕ → List (Fin n)) (t : ℕ → ℝ),
    (∀ q, 1 ≤ q → q ≤ p → IsGNode I q (v q)) ∧
    (∀ q, 1 ≤ q → q < p → IsArc I.k q (v q) (v (q + 1))) ∧
    v p = j ∧
    (∀ q, 1 ≤ q → q < p → I.e (final (v q)) ≤ t q ∧ t q ≤ I.l (final (v q))) ∧
    I.e (final j) ≤ t p ∧
    (∀ q r, 1 ≤ q → q < r → r ≤ p → I.δ (final (v q)) (final (v r)) ≤ t r - t q) ∧
    τ = t p}

/-- The last position `n - 1` (0-based) of the sequence, i.e. the paper's position `n`. -/
def lastPos [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩

/-- The makespan of a schedule with landing times by position `t`: the landing time of the
aircraft in the last position. -/
def makespan [NeZero n] (t : Fin n → ℝ) : ℝ :=
  t lastPos

end RunwayCPS.Makespan


