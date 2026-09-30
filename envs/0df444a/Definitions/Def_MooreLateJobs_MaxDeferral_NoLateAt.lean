-- Prove2me | Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt
-- name    : MooreLateJobs_MaxDeferral_NoLateAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:33:54.337509+00:00
-- url     : https://prove2.me/theorems/a3dabc86-41b3-407d-9481-33a6351ef514
-- title:
--   Late jobs for extended-real due-dates, and at a cost level $y$
-- statement:
--   Let each job $j$ have a due-date $D_j\in\mathbb R\cup\{\pm\infty\}$. In a sequence $S$, job $j$ is **late** if its completion time exceeds its due-date, $C_j>D_j$ (Moore 1968, p. 105), and $S$ has **no late jobs** if $C_j\le D_j$ for every job $j$ of $S$.
--
--   For deferral costs $P_i$ and a cost level $y$, the paper sets the "due-dates" $D_i=P_i^*(y)$ (p. 108). The sequence $S$ has no late jobs at level $y$ if
--   $$
--   C_j\le P_j^*(y)\qquad\text{for every job } j \text{ of } S.
--   $$
--
--   This is the feasibility notion of the section: $S_D(y)$ "has no late jobs" in this sense.
--
--   **Formalization Note** Due-dates are in `EReal` because $P^*_j(y)$ may be $+\infty$; only the comparison $C_j\le D_j$ of a real completion time with an extended real is used, never extended-real arithmetic. `IsLate t D l j` is $D_j<C_j$, `NoLate t D l` is the absence of late jobs among the entries of $l$, `dueDates P y` is $i\mapsto P_i^*(y)$, and `NoLateAt t P y l` is `NoLate t (dueDates P y) l`.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105 (definition of E and L) and p. 108 ("For arbitrary y > 0, let D_i = P_i*(y)")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_MaxDeferral_Pstar

namespace MooreLateJobs.MaxDeferral

/-- Job `j` is late in the sequence `l` for the (extended-real) due-dates `D` (p. 105):
`C_j > D_j`. A due-date `+∞` is never exceeded. -/
def IsLate {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (D : ι → EReal) (l : List ι) (j : ι) : Prop :=
  D j < ((Shared.completionTime t l j : ℝ) : EReal)

/-- The sequence `l` has no late jobs for the due-dates `D`. -/
def NoLate {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (D : ι → EReal) (l : List ι) : Prop :=
  ∀ j ∈ l, ¬ IsLate t D l j

/-- The "due-dates" at cost level `y` (p. 108): `D_i = P_i*(y)`. -/
noncomputable def dueDates {ι : Type*} (P : ι → ℝ → ℝ) (y : ℝ) : ι → EReal :=
  fun i => Pstar (P i) y

/-- The sequence `l` has no late jobs at cost level `y`: `C_j ≤ P_j*(y)` for every job `j` of
`l` (p. 108–109, "`S_D(y)` has no 'late' jobs"). -/
def NoLateAt {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (P : ι → ℝ → ℝ) (y : ℝ) (l : List ι) :
    Prop :=
  NoLate t (dueDates P y) l

end MooreLateJobs.MaxDeferral


