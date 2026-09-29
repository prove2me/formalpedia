-- Prove2me | Definitions.Def_MooreLateJobs_NumLate_IsOptimal
-- name    : MooreLateJobs_NumLate_IsOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:04:18.701927+00:00
-- url     : https://prove2.me/theorems/02d32c84-2482-4296-84ac-f9ec8abb4aec
-- title:
--   Optimal schedule: minimum number of late jobs
-- statement:
--   A sequence $S$ is an **optimal schedule** for the job set $J$ if it is a schedule of $J$ and no schedule $S'$ of $J$ has fewer late jobs:
--   $$
--   |L(S)|\le|L(S')|\quad\text{for every schedule }S'\text{ of }J.
--   $$
--
--   This is the objective of the paper: sequence the jobs so as to minimize the number of late jobs (equivalently, maximize the number $|E|$ of early jobs).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 102 ("minimize the number of late jobs") and p. 105 ("the cardinality of the associated set, E_D, is maximal")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

/-- `l` is an optimal schedule for the job set `J`: it is a schedule of `J`, and no schedule of
`J` has fewer late jobs (the objective of p. 102, "minimize the number of late jobs"). -/
def IsOptimal {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (J : Finset ι) (l : List ι) : Prop :=
  Shared.IsSchedule J l ∧ ∀ l' : List ι, Shared.IsSchedule J l' → (lateSet t D l).card ≤ (lateSet t D l').card

end MooreLateJobs.NumLate


