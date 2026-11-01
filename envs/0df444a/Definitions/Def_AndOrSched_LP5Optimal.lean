-- Prove2me | Definitions.Def_AndOrSched_LP5Optimal
-- name    : AndOrSched_LP5Optimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:47.10442+00:00
-- url     : https://prove2.me/theorems/abfe82c5-ade5-43fd-9726-1ba38268c9bd
-- title:
--   Optimal solutions of LP (5)
-- statement:
--   $\bar x$ is **optimal** for LP (5) with parameter $\varepsilon'$ if it is feasible and its objective (5a) is at most that of every feasible solution.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, "Let x̄ be an optimal fractional solution of LP (5)"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP5Feasible
import Definitions.Def_AndOrSched_LP5Obj
open scoped Classical NNReal

namespace AndOrSched

/-- `x̄` is an optimal solution of LP (5) for the given `ε'` (Happach, Schulz, arXiv:2001.07011v1, §2, p.9, "Let x̄ be an optimal
fractional solution of LP (5)"). -/
def LP5Optimal (I : Instance) (ε' : ℝ) (x : I.N → ℕ → ℝ) : Prop :=
  LP5Feasible I ε' x ∧ ∀ y, LP5Feasible I ε' y → LP5Obj I ε' x ≤ LP5Obj I ε' y

end AndOrSched


