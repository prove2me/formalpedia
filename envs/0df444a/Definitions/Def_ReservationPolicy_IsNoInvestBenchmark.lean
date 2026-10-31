-- Prove2me | Definitions.Def_ReservationPolicy_IsNoInvestBenchmark
-- name    : ReservationPolicy_IsNoInvestBenchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:46.665901+00:00
-- url     : https://prove2.me/theorems/0168cf62-2404-4f80-8559-afb12448ac7c
-- title:
--   Benchmark equilibrium in which type $x$ does not invest
-- statement:
--   A benchmark equilibrium in which type $x$ does not invest consists of two non-investing groups at a common cutoff, with seats clearing,
--   $$
--   z=\rho(\phi e_x,d)\,\alpha+\rho(\phi e_y,d)\,(1-\alpha),
--   $$
--   at which no type-$x$ student gains by investing (`NoInvestOptimal`). It is the equilibrium of Case 2 of the proof of Proposition 1.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), pp.36–37

import Mathlib
import Definitions.Def_ReservationPolicy_PlainGroup
import Definitions.Def_ReservationPolicy_NoInvestOptimal
import Definitions.Def_ReservationPolicy_Benchmark

namespace ReservationPolicy

/-- A benchmark equilibrium in which type `x` does not invest: both groups are non-investing groups
at the common cutoff, seats clear, and no type-`x` student gains by investing, (42)–(43).
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), pp.36–37 (PDF 36–37). -/
def IsNoInvestBenchmark (P : Params) (b : Benchmark) : Prop :=
  PlainGroup P b.ex b.d b.rx ∧ PlainGroup P b.ey b.d b.ry ∧
    P.z = admitProb (P.ϕ * b.ex) b.d * P.α + admitProb (P.ϕ * b.ey) b.d * (1 - P.α) ∧
    NoInvestOptimal P b.d b.rx b.ex

end ReservationPolicy


