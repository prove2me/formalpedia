-- Prove2me | Definitions.Def_ReservationPolicy_Feasible
-- name    : ReservationPolicy_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:46.227628+00:00
-- url     : https://prove2.me/theorems/f8dabcf7-7654-4775-bfa3-8dad4c22f120
-- title:
--   Feasible transfers
-- statement:
--   Relative to a benchmark $b$, a transfer $s\ge 0$ is feasible when it is smaller than the size of admission of type $x$ in the absence of the policy, and the size of admission of type $y$ after the policy is smaller than the size of type $y$:
--   $$
--   0\le s,\qquad s<\alpha\rho_x(b),\qquad s<(1-\alpha)\bigl(1-\rho_y(b)\bigr).
--   $$
--   **Formalization Note** The second condition is $(1-\alpha)\rho_y(b)+s<1-\alpha$, written with $s$ on the left.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), p.41

import Mathlib
import Definitions.Def_ReservationPolicy_Benchmark_rhoX
import Definitions.Def_ReservationPolicy_Benchmark_rhoY

namespace ReservationPolicy

/-- The feasible transfers: `s` is nonnegative, smaller than the benchmark type-`x` admissions, and
keeps the type-`y` admissions below the size of type `y`. Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), p.41 (PDF 41). -/
def Feasible (P : Params) (b : Benchmark) (s : ℝ) : Prop :=
  0 ≤ s ∧ s < P.α * b.rhoX ∧ s < (1 - P.α) * (1 - b.rhoY P)

end ReservationPolicy


