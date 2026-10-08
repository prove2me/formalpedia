-- Prove2me | Definitions.Def_LawlerPrec_MinMax_IsFeasible
-- name    : LawlerPrec_MinMax_IsFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:52:46.505372+00:00
-- url     : https://prove2.me/theorems/df2b44db-a567-4715-a386-ea192e9e4c64
-- title:
--   A sequence of the job set that observes the precedence constraints
-- statement:
--   A finite set $J$ of jobs is to be processed on a single machine, one at a time and without interruption, subject to arbitrary given precedence constraints. The constraints are a relation $\prec$ on jobs: $i \prec j$ means that job $i$ is required to precede job $j$.
--
--   A **sequence** of $J$ is an ordering $\pi = (\pi_1, \dots, \pi_n)$ that lists every job of $J$ exactly once. The sequence **observes the precedence constraints** (is *feasible*) if no job appears before a job it is required to follow:
--
--   $$
--   \text{for all positions } p < q:\qquad \neg\,(\pi_q \prec \pi_p).
--   $$
--
--   These are the sequences among which Lawler's problem seeks one of least maximum cost; every optimality statement of the mission compares only with feasible sequences.
--
--   **Formalization Note** A sequence is a duplicate-free list whose elements are exactly the jobs of $J$ (`MooreLateJobs.Shared.IsSchedule`, published with the Moore 1968 series), and feasibility is `List.Pairwise (fun x y => ¬ prec y x)`. The relation `prec` is arbitrary: it is not assumed transitive, irreflexive or acyclic, as "arbitrary given precedence constraints" says. If `prec` has a cycle among distinct jobs of $J$, no feasible sequence exists; a self-loop `prec j j` constrains nothing, since only distinct positions are compared.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §1 Problem Formulation

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace LawlerPrec.MinMax

/-- A sequence of the job set `J` that observes the precedence constraints `prec`
(Lawler 1973, §1, p. 544): `prec i j` means that job `i` is required to precede job `j`.
The list `l` lists every job of `J` exactly once (`MooreLateJobs.Shared.IsSchedule`), and no job
appears before a job it is required to follow: whenever `x` comes before `y` in `l`,
`prec y x` fails. The relation `prec` is arbitrary (not assumed transitive, irreflexive or
acyclic); a cycle among distinct jobs of `J` leaves no feasible sequence. -/
def IsFeasible {ι : Type*} (prec : ι → ι → Prop) (J : Finset ι) (l : List ι) : Prop :=
  MooreLateJobs.Shared.IsSchedule J l ∧ l.Pairwise (fun x y => ¬ prec y x)

end LawlerPrec.MinMax


