-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_NonpreemptiveSchedule
-- name    : SingleMachineSched_AlphaJSched_Supplement_NonpreemptiveSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:07:56.014531+00:00
-- url     : https://prove2.me/theorems/d4ab5921-8d4b-46c0-af25-9e4a3fd17547
-- title:
--   Nonpreemptive single-machine schedules with real start times
-- statement:
--   Let $p_j$ be the integral processing time and $r_j$ the integral release date of each job $j$. A nonpreemptive schedule consists of real start times $s_j$ satisfying
--   $$s_j\ge r_j,\qquad [s_j,s_j+p_j)\cap[s_k,s_k+p_k)=\varnothing\quad(j\ne k).$$
--   Job $j$ completes at $s_j+p_j$, and its weighted completion contribution is $w_j(s_j+p_j)$. The predicate records feasibility separately from the objective and from every scheduling algorithm, so it can serve both makespan and weighted-cost comparisons. Positivity of processing times is assumed by the theorems, rather than bundled into this general feasibility predicate.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, p. 165 (PDF 1), §1

import Mathlib

namespace SingleMachineSched.AlphaJSched.Supplement

/-- Feasible nonpreemptive schedules on one machine (§1, p. 165):
`s j` is the real start time of job `j`. No optimality or priority rule is bundled here. -/
def IsNonpreemptiveSchedule {n : ℕ} (p r : Fin n → ℕ) (s : Fin n → ℝ) : Prop :=
  (∀ j, (r j : ℝ) ≤ s j) ∧
  (∀ j k, j ≠ k → s j + (p j : ℝ) ≤ s k ∨ s k + (p k : ℝ) ≤ s j)

end SingleMachineSched.AlphaJSched.Supplement


