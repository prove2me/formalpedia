-- Prove2me | Definitions.Def_PolytopeSchedPF_ProportionalFairness
-- name    : PolytopeSchedPF_ProportionalFairness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:30.278927+00:00
-- url     : https://prove2.me/theorems/bb8fc3e6-95a5-4c27-a44a-f6f9489f9d46
-- title:
--   Eisenberg–Gale optimum $y(S)$ and the Proportional Fairness schedule
-- statement:
--   For a set $S\subseteq J$ of jobs, the **Eisenberg–Gale convex program** is
--   $$
--   \text{(CP)}\qquad \max\ \sum_{j\in S}w_j\log y_j\quad\text{s.t.}\quad \sum_{j\in S}B_{dj}y_j\le1\ \ \forall d\in[D],\qquad y_j\ge0\ \ \forall j\in S .
--   $$
--   For positive weights it has a unique optimal solution $y(S)$, which is positive on $S$. A vector $y$ is **EG-optimal for $S$** if $y\in\mathcal P_S$, $y_j>0$ for $j\in S$, and $\sum_{j\in S}w_j\log y'_j\le\sum_{j\in S}w_j\log y_j$ for every $y'\in\mathcal P$ that is positive on $S$.
--
--   **Proportional Fairness (PF)** sets, at every time $t\ge0$, the rates of the active jobs to $y(A(t))$ and the rate of every other job to $0$. A **PF schedule** is a feasible schedule $y$ such that $y(t)$ is EG-optimal for $A(t)$ for every $t\ge0$, where $A(t)$ is the active set of $y$ itself.
--
--   PF never uses processing requirements, which makes it a nonclairvoyant online algorithm; this mission bounds its weighted completion time.
--
--   **Formalization Note** Since (CP) has $\log0=-\infty$ while Lean's `Real.log 0 = 0`, the comparison ranges only over vectors positive on $S$. For $S=\emptyset$ EG-optimality forces $y=0$. The PF schedule is a predicate (`IsPFSchedule`), not a construction; theorems that use it also assert that one exists.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §3.2, p.14 (PDF p.16), (CP) and the PF rule y^pf_j(t) = y_j(A(t))

import Mathlib
import Definitions.Def_PolytopeSchedPF_Schedule

namespace PolytopeSchedPF

/-- **Optimal solution of the Eisenberg–Gale program (CP)** for a job set `S`
(Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §3.2, p.14):
maximize `∑_{j∈S} w_j log y_j` subject to `∑_{j∈S} B_{dj} y_j ≤ 1` for all `d` and `y_j ≥ 0`.
`IsEGOptimal P w S y` says that `y ∈ P_S` (so `y` vanishes off `S`), `y_j > 0` for `j ∈ S`, and
`y` attains the maximum of `∑_{j∈S} w_j log y'_j` over all `y' ∈ P` that are positive on `S`.

**Formalization Note** (CP) has `log 0 = −∞`, while Mathlib's `Real.log 0 = 0`; the comparison
therefore ranges over vectors positive on `S` only (reading R5). Comparing with full vectors
`y' ∈ P` is the same as comparing with (CP)'s feasible set, since `y' ⊙ 1_S ∈ P`. For `S = ∅` the
condition forces `y = 0`. -/
def IsEGOptimal {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Prop :=
  y ∈ P.restricted S ∧ (∀ j ∈ S, 0 < y j) ∧
    ∀ y' ∈ P.rates, (∀ j ∈ S, 0 < y' j) →
      ∑ j ∈ S, w j * Real.log (y' j) ≤ ∑ j ∈ S, w j * Real.log (y j)

/-- **Proportional Fairness schedule** (§3.2, p.14): a feasible schedule that at every time
`t ≥ 0` uses the optimal solution of (CP) for its own set `A(t)` of active jobs, and rate `0` for
every other job: `y^pf_j(t) = y_j(A(t))` for `j ∈ A(t)` and `y^pf_j(t) = 0` otherwise.

**Formalization Note** A predicate, not a construction (reading R4): `A(t)` is the active set of the
schedule `y` itself. Theorems that use it also assert that such a schedule exists. The online,
nonclairvoyant information model is not formalized (reading R9); the rule visibly depends only on
`A(t)`, `w` and `B`. -/
def IsPFSchedule {n D : ℕ} (P : RatePolytope n D) (w p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) :
    Prop :=
  IsFeasible P p r y ∧ ∀ t : ℝ, 0 ≤ t → IsEGOptimal P w (active p r y t) (y t)

end PolytopeSchedPF


