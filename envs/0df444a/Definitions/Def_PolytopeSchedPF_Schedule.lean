-- Prove2me | Definitions.Def_PolytopeSchedPF_Schedule
-- name    : PolytopeSchedPF_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:39.412974+00:00
-- url     : https://prove2.me/theorems/1f4e5096-399a-46b5-aa9e-803254b79841
-- title:
--   Feasible schedules, completion times $C_j$, unfinished and active sets, and $\sum_j w_jC_j$
-- statement:
--   A **schedule** assigns to every time $t\ge0$ a rate vector $y(t)=(y_j(t))_{j\in J}$. For processing requirements $p\in\mathbb R^n$ and release dates $r\in\mathbb R^n$, a schedule is **feasible** if it is measurable and
--
--   1. (S1) $y(t)\in\mathcal P$ for every $t\ge0$;
--   2. (S2) every job $j$ has a time $t\ge r_j$ with $\int_{r_j}^{t}y_j(u)\,du\ge p_j$.
--
--   The **completion time** of job $j$ is the first time it has accumulated its full requirement,
--   $$
--   C_j=\min\Big\{t\ge r_j : \int_{r_j}^{t}y_j(u)\,du\ge p_j\Big\},
--   $$
--   and the objective is the **weighted completion time** $\sum_{j}w_jC_j$. At time $t$ the **unfinished** jobs are $U(t)=\{j : t<C_j\}$ and the **active** jobs are $A(t)=\{j : r_j\le t<C_j\}$. A job with $p_j=0$ completes at $r_j$ and is never active.
--
--   **Formalization Note** A schedule is a function `ℝ → Fin n → ℝ`; only its values at $t\ge0$ matter, so measurability is required of its restriction to $[0,\infty)$. Rates need not vanish outside $[r_j,C_j)$. $C_j$ is an `sInf`, which for a feasible schedule is the paper's minimum. $U(t)$ and $A(t)$ are defined through the accumulated processing: $j\in U(t)$ iff $t<r_j$ or $\int_{r_j}^t y_j<p_j$, and $j\in A(t)$ iff $r_j\le t$ and $\int_{r_j}^t y_j<p_j$; for a feasible schedule these are the sets above.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §3.1, p.13 (PDF p.15), schedule, (S1), (S2), completion time C_j, A(t), U(t), weighted completion time

import Mathlib
import Definitions.Def_PolytopeSchedPF_RatePolytope

namespace PolytopeSchedPF

/-- **Feasible schedule** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §3.1, p.13).
A schedule `y` assigns to every time `t ≥ 0` a rate vector `y(t)`; it is feasible (speed 1) for
processing requirements `p` and release dates `r` if it is measurable and
(S1) `y(t) ∈ P` for every `t ≥ 0`, and
(S2) every job `j` has a time `t ≥ r_j` with `∫_{r_j}^{t} y_j(u) du ≥ p_j`.

**Formalization Note** `y : ℝ → Fin n → ℝ`; only its values at `t ≥ 0` matter, so measurability is
required of the restriction to `[0, ∞)` and (S1) is imposed for `t ≥ 0`. Since `r_j ≥ 0` in every
item, the interval integrals only see `[0, ∞)`. Rates are not required to vanish outside
`[r_j, C_j)` (reading R8). -/
def IsFeasible {n D : ℕ} (P : RatePolytope n D) (p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) : Prop :=
  (∀ j, Measurable (fun t : Set.Ici (0 : ℝ) => y (t : ℝ) j)) ∧
  (∀ t : ℝ, 0 ≤ t → y t ∈ P.rates) ∧
  (∀ j, ∃ t : ℝ, r j ≤ t ∧ p j ≤ ∫ u in r j..t, y u j)

/-- The completion time `C_j = min{t ≥ r_j | ∫_{r_j}^{t} y_j(u) du ≥ p_j}` (p.13).

**Formalization Note** Written as `sInf` (reading R7). For a feasible schedule the set is
nonempty (S2), bounded below by `r_j` and closed, so `sInf` is the paper's minimum. A job with
`p_j = 0` completes at `r_j`. -/
noncomputable def completionTime {n : ℕ} (p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) (j : Fin n) : ℝ :=
  sInf {t : ℝ | r j ≤ t ∧ p j ≤ ∫ u in r j..t, y u j}

/-- The set `U(t)` of unfinished jobs at time `t` (p.13): the jobs not released yet or still
missing processing.

**Formalization Note** Defined through the accumulated processing instead of `C_j` (reading R6):
`j ∈ U(t)` iff `t < r_j` or `∫_{r_j}^{t} y_j < p_j`. For a feasible schedule this is the paper's
`{j | t < C_j}`. -/
noncomputable def unfinished {n : ℕ} (p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) (t : ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => t < r j ∨ ∫ u in r j..t, y u j < p j)

/-- The set `A(t)` of active jobs at time `t` (p.13): released and not yet complete.

**Formalization Note** `j ∈ A(t)` iff `r_j ≤ t` and `∫_{r_j}^{t} y_j < p_j` (reading R6); for a
feasible schedule this is the paper's `{j | r_j ≤ t < C_j}`. A job with `p_j = 0` is never active. -/
noncomputable def active {n : ℕ} (p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) (t : ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => r j ≤ t ∧ ∫ u in r j..t, y u j < p j)

/-- The weighted completion time `∑_j w_j C_j` of a schedule (p.13). -/
noncomputable def weightedCompletion {n : ℕ} (w p r : Fin n → ℝ) (y : ℝ → Fin n → ℝ) : ℝ :=
  ∑ j, w j * completionTime p r y j

end PolytopeSchedPF


