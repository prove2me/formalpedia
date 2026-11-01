-- Prove2me | Definitions.Def_AndOrSched_LP1Optimal
-- name    : AndOrSched_LP1Optimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:20.826023+00:00
-- url     : https://prove2.me/theorems/a33cf18b-45b2-4388-b7ed-333e691799a7
-- title:
--   Optimal solutions of LP (1)
-- statement:
--   $\bar x$ is **optimal** for LP (1) if it is feasible and its objective (1a) is at most that of every feasible solution.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.7, "Let x̄ be an optimal fractional solution of LP (1)"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_LP1Obj
open scoped Classical NNReal

namespace AndOrSched

/-- `x̄` is an optimal solution of LP (1) (Happach, Schulz, arXiv:2001.07011v1, §2, p.7, "Let x̄ be an optimal fractional solution
of LP (1)"): it is feasible and its objective (1a) is at most that of every feasible solution. -/
def LP1Optimal (I : Instance) (x : I.N → ℕ → ℝ) : Prop :=
  LP1Feasible I x ∧ ∀ y, LP1Feasible I y → LP1Obj I x ≤ LP1Obj I y

end AndOrSched


