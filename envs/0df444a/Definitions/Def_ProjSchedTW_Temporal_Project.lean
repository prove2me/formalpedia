-- Prove2me | Definitions.Def_ProjSchedTW_Temporal_Project
-- name    : ProjSchedTW_Temporal_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:24:03.464301+00:00
-- url     : https://prove2.me/theorems/24649e27-83dc-49d9-9e92-484017081251
-- title:
--   §1.1 and Definition 1.3.1 — projects, the standing path assumption, schedules, time-feasible and time-optimal schedules
-- statement:
--   A **project** consists of $n\ge 1$ real activities $1,\dots,n$, a fictitious activity $0$ (project beginning) and a fictitious activity $n+1$ (project completion), integer durations $p_i\in\mathbb N$ with $p_0=p_{n+1}=0$ and $p_i>0$ for every real activity, and the AoN network $N=(V,E,\delta)$ of its minimum and maximum time lags.
--
--   The **standing assumption** on AoN networks (p. 8, a consequence of Definition 1.1.1 and Remarks 1.1.2) is: for each node $i\in V$ there are a path from node $0$ to node $i$ of nonnegative length, and a path from node $i$ to node $n+1$ whose length is at least $p_i$.
--
--   A **schedule** (Definition 1.3.1) is a vector of real start times $S=(S_0,S_1,\dots,S_{n+1})$ with $S_i\ge 0$ for all $i\in V$ and $S_0=0$. It is **time-feasible** if it satisfies the temporal constraints
--   $$S_j-S_i\ \ge\ \delta_{ij}\qquad(\langle i,j\rangle\in E).\qquad(1.2.1)$$
--   The set of time-feasible schedules is $\mathcal S_T$. A schedule $S\in\mathcal S_T$ that minimizes the project duration $S_{n+1}$ over $\mathcal S_T$ is **time-optimal**.
--
--   These are the basic objects of the book: every later chapter adds resource constraints to the time-feasible region $\mathcal S_T$.
--
--   **Formalization Note.** Start times are real numbers (integrality is a theorem, Remark 1.3.2, not part of the schedule type). The standing assumption is stated with simple paths, and is a predicate `Project.StandingAssumption` used as a hypothesis where a result needs it. Time-feasibility is a property of a schedule relative to a network, so the same predicate applies to $N$ and to $N^+$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, §1.1 p. 1 (activities, durations), §1.2 pp. 7–8 (Eq. (1.2.1), standing path property), p. 10, Definition 1.3.1

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_Network

namespace ProjSchedTW.Temporal

/-- A project (§1.1, p. 1 and §1.2, p. 7): `n ≥ 1` real activities `1, …, n`, the fictitious
activities `0` (project beginning) and `n + 1` (project completion), integer durations `p`
with `p_0 = p_{n+1} = 0` and `p_i > 0` for real activities, and the AoN network `N` of its
minimum and maximum time lags. -/
structure Project (n : ℕ) where
  /-- The AoN project network `N`. -/
  N : Network n
  /-- The durations `p_i`. -/
  p : Fin (n + 2) → ℕ
  one_le_n : 1 ≤ n
  p_zero : p 0 = 0
  p_last : p (Fin.last (n + 1)) = 0
  p_pos : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) → 0 < p i

variable {n : ℕ}

/-- The standing property of an AoN network (§1.2, p. 8, from Definition 1.1.1 and
Remarks 1.1.2): for each node `i` there are a path from `0` to `i` of nonnegative length and a
path from `i` to `n + 1` whose length is at least `p_i`. -/
def Project.StandingAssumption (P : Project n) : Prop :=
  ∀ i : Fin (n + 2),
    (∃ (m : ℕ) (w : Fin (m + 1) → Fin (n + 2)),
      IsPath P.N w ∧ w 0 = 0 ∧ w (Fin.last m) = i ∧ 0 ≤ walkLength P.N w) ∧
    (∃ (m : ℕ) (w : Fin (m + 1) → Fin (n + 2)),
      IsPath P.N w ∧ w 0 = i ∧ w (Fin.last m) = Fin.last (n + 1) ∧
        (P.p i : ℤ) ≤ walkLength P.N w)

/-- A schedule (Definition 1.3.1): real start times `S_i ≥ 0` with `S_0 = 0`. -/
def IsSchedule (S : Fin (n + 2) → ℝ) : Prop :=
  S 0 = 0 ∧ ∀ i, 0 ≤ S i

/-- A time-feasible schedule (Definition 1.3.1): a schedule satisfying the temporal
constraints (1.2.1), `S_j - S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E` of `N`. -/
def IsTimeFeasible (N : Network n) (S : Fin (n + 2) → ℝ) : Prop :=
  IsSchedule S ∧ ∀ e ∈ N.E, (N.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1

/-- A time-optimal schedule (Definition 1.3.1): a time-feasible schedule minimizing the
project duration `S_{n+1}` over all time-feasible schedules. -/
def IsTimeOptimal (N : Network n) (S : Fin (n + 2) → ℝ) : Prop :=
  IsTimeFeasible N S ∧
    ∀ S' : Fin (n + 2) → ℝ, IsTimeFeasible N S' → S (Fin.last (n + 1)) ≤ S' (Fin.last (n + 1))

end ProjSchedTW.Temporal


