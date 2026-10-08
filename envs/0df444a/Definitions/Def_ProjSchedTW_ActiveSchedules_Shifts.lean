-- Prove2me | Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts
-- name    : ProjSchedTW_ActiveSchedules_Shifts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T15:51:26.256739+00:00
-- url     : https://prove2.me/theorems/11985b04-c09b-461b-a08b-384f8305419e
-- title:
--   Definitions 2.4.1–2.4.6 — left-shifts and active, semiactive, pseudoactive, quasiactive schedules
-- statement:
--   This file defines the types of shifts of §2.4 and the four classes of schedules built from them. Let $\mathcal S$ be the feasible region and $O(S)$ the schedule-induced strict order of a project.
--
--   1. **Left-shift** (Definition 2.4.1). A shift from $S$ to $S'$ is a left-shift if $S'\le S$ componentwise and $S'\ne S$.
--   2. **Global shift** (Definition 2.4.2): $S$ and $S'$ are both feasible and $S'\neq S$.
--   3. **Local shift** (Definition 2.4.3): a global shift for which there is a continuous trajectory $x:[0,1]\to\mathcal S$ with $x(0)=S$ and $x(1)=S'$.
--   4. **Order-preserving and order-monotone shifts** (Definition 2.4.4): a global shift with $O(S)\subseteq O(S')$, respectively with $O(S)\subseteq O(S')$ or $O(S)\supseteq O(S')$.
--   5. **Schedule classes** (Definition 2.4.6). A feasible schedule $S$ is called
--      - *active* if there is no global left-shift from $S$,
--      - *semiactive* if there is no local left-shift from $S$,
--      - *pseudoactive* if there is no order-monotone left-shift from $S$,
--      - *quasiactive* if there is no order-preserving left-shift from $S$.
--
--   The sets of these schedules are $\mathcal{AS}$, $\mathcal{SAS}$, $\mathcal{PAS}$ and $\mathcal{QAS}$. They are the candidate sets that exact and heuristic methods for $PS|temp|C_{\max}$ enumerate.
--
--   **Formalization Note** The left-shift uses the book's own brief form $S'\le S$, $S'\neq S$, which is equivalent to "a nonempty set $V'$ of activities moves strictly earlier and the others stay". The trajectory is a continuous map from the unit interval into `Fin (n + 2) → ℝ` whose values all lie in $\mathcal S$. The classes are defined through the shifts, not through minimal points.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 39, Definitions 2.4.1–2.4.4; pp. 41–42, Definition 2.4.6

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project

namespace ProjSchedTW.ActiveSchedules

variable {n : ℕ} {K : Type}

/-- Definition 2.4.1 (p. 39): a left-shift from `S` to `S'` (of the nonempty set of activities
whose start times change), in the book's brief form `S' ≤ S` and `S' ≠ S`. -/
def IsLeftShift (S S' : Fin (n + 2) → ℝ) : Prop :=
  S' ≤ S ∧ S' ≠ S

/-- Definition 2.4.2 (p. 39): a global shift transforms a feasible schedule `S` into a feasible
schedule `S' ≠ S`. -/
def IsGlobalShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ S' ∈ feasibleSet P ∧ S' ≠ S

/-- Definition 2.4.3 (p. 39): a local shift is a global shift from `S` to `S'` for which there
is a continuous trajectory `x : [0, 1] → 𝒮` with `x(0) = S` and `x(1) = S'`. -/
def IsLocalShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧
    ∃ x : unitInterval → (Fin (n + 2) → ℝ), Continuous x ∧ x 0 = S ∧ x 1 = S' ∧
      ∀ τ, x τ ∈ feasibleSet P

/-- Definition 2.4.4 (p. 39): a shift between feasible schedules is order-preserving if
`O(S) ⊆ O(S')`. -/
def IsOrderPreservingShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧ scheduleOrder P S ⊆ scheduleOrder P S'

/-- Definition 2.4.4 (p. 39): a shift between feasible schedules is order-monotone if
`O(S) ⊆ O(S')` or `O(S) ⊇ O(S')`. -/
def IsOrderMonotoneShift (P : Project n K) (S S' : Fin (n + 2) → ℝ) : Prop :=
  IsGlobalShift P S S' ∧
    (scheduleOrder P S ⊆ scheduleOrder P S' ∨ scheduleOrder P S' ⊆ scheduleOrder P S)

/-- Definition 2.4.6 (pp. 41–42): a feasible schedule is active if there is no global
left-shift from it (the set `AS`). -/
def IsActive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsGlobalShift P S S' ∧ IsLeftShift S S'

/-- Definition 2.4.6: a feasible schedule is semiactive if there is no local left-shift from it
(the set `SAS`). -/
def IsSemiactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsLocalShift P S S' ∧ IsLeftShift S S'

/-- Definition 2.4.6: a feasible schedule is pseudoactive if there is no order-monotone
left-shift from it (the set `PAS`). -/
def IsPseudoactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsOrderMonotoneShift P S S' ∧ IsLeftShift S S'

/-- Definition 2.4.6: a feasible schedule is quasiactive if there is no order-preserving
left-shift from it (the set `QAS`). -/
def IsQuasiactive (P : Project n K) (S : Fin (n + 2) → ℝ) : Prop :=
  S ∈ feasibleSet P ∧ ¬ ∃ S', IsOrderPreservingShift P S S' ∧ IsLeftShift S S'

end ProjSchedTW.ActiveSchedules


