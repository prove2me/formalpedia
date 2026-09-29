-- Prove2me | Definitions.Def_MooreLateJobs_NumLate_earlyPart
-- name    : MooreLateJobs_NumLate_earlyPart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:04:59.741663+00:00
-- url     : https://prove2.me/theorems/7f73c7ff-a5f3-4e6b-aa43-67c70b038766
-- title:
--   The ordered sets A (early jobs) and R (late jobs) of a schedule
-- statement:
--   For a schedule $S$:
--
--   1. $A$ is the ordered set obtained by ordering the elements of the early set $E$ according to their order in $S$;
--   2. $R$ is the ordered set obtained by ordering the elements of the late set $L$ according to their order in $S$.
--
--   A schedule is **of the form** $(A,R)$ when it equals $A$ followed by $R$; a schedule of the form $(A,P)$ is $A$ followed by an arbitrary permutation $P$ of $R$. These ordered sets are the vocabulary of Lemmas 1–3.
--
--   **Formalization Note** `earlyPart t D S` and `latePart t D S` filter the list $S$ by membership in the late set of $S$, which keeps the order of $S$.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 105, Definition (A and R)

import Mathlib
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

/-- The ordered set `A` of a schedule `S` (p. 105): the early jobs of `S` (the set `E`) in their
order in `S`. -/
noncomputable def earlyPart {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (S : List ι) : List ι :=
  S.filter (fun j => j ∉ lateSet t D S)

/-- The ordered set `R` of a schedule `S` (p. 105): the late jobs of `S` (the set `L`) in their
order in `S`. -/
noncomputable def latePart {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (S : List ι) : List ι :=
  S.filter (fun j => j ∈ lateSet t D S)

end MooreLateJobs.NumLate


