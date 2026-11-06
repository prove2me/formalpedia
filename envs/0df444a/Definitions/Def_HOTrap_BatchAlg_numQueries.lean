-- Prove2me | Definitions.Def_HOTrap_BatchAlg_numQueries
-- name    : HOTrap_BatchAlg_numQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:50.659552+00:00
-- url     : https://prove2.me/theorems/fe3d0107-f3db-479d-b223-f409690baa2a
-- title:
--   Total number of gradient queries
-- statement:
--   The sum of the batch sizes. It does not depend on the objective or on the seed, which is the paper's worst-case bound $\sup_f\sup_uN(f,u)\le Q$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, p.14

import Mathlib
import Definitions.Def_HOTrap_BatchAlg

namespace HOTrap

/-- **The total number of gradient queries**: the sum of the batch sizes. It depends on neither the
objective nor the seed, which is the paper's `sup_f sup_u N(f,u) ≤ Q`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, §2, p.14. -/
def BatchAlg.numQueries {d : ℕ} {Ω : Type} (A : BatchAlg d Ω) : ℕ :=
  ∑ r ∈ Finset.range A.rounds, A.batch r

end HOTrap


