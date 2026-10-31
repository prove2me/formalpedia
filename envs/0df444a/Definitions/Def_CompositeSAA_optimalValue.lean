-- Prove2me | Definitions.Def_CompositeSAA_optimalValue
-- name    : CompositeSAA_optimalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:44.534029+00:00
-- url     : https://prove2.me/theorems/3a07849b-da19-4233-ba64-34f17763a9d9
-- title:
--   Optimal value $\vartheta=\min_{u\in U}\rho(u)$
-- statement:
--   The **optimal value** of minimizing an objective $\rho$ over a feasible set $U$ is
--
--   $$
--   \vartheta=\min_{u\in U}\rho(u).
--   $$
--
--   **Formalization Note** It is written as the infimum of $\rho(U)$. This equals the minimum whenever the minimum is attained, which every theorem of the mission assumes; on objectives unbounded below the Lean value is a junk value and is never used.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (3), p.3 and display (8), p.5

import Mathlib

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (3), p.3 and display (8), p.5: the optimal
value `ϑ = min_{u ∈ U} ρ(u)` of minimizing an objective `ρ` over a feasible set `U`.

**Formalization Note** It is the infimum `sInf (ρ '' U)`. It equals the paper's minimum whenever
the minimum is attained, which every theorem of the mission assumes (nonempty solution sets);
on a set where `ρ` is unbounded below it is Lean's junk value `0` and is never used there. -/
noncomputable def optimalValue {α : Type*} (ρ : α → ℝ) (U : Set α) : ℝ :=
  sInf (ρ '' U)

end CompositeSAA


