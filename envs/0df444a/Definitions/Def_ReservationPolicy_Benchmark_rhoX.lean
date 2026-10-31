-- Prove2me | Definitions.Def_ReservationPolicy_Benchmark_rhoX
-- name    : ReservationPolicy_Benchmark_rhoX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:27.288589+00:00
-- url     : https://prove2.me/theorems/a6c93e8c-346f-4667-9df2-e282e9bc2e35
-- title:
--   Type-$x$ admission probability when type $x$ invests
-- statement:
--   In a benchmark outcome where type $x$ invests, a type-$x$ student has mean ability $e_x$ and admission probability $\rho_x=\rho(e_x,d)$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (4), p.11

import Mathlib
import Definitions.Def_ReservationPolicy_Benchmark
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The admission probability of a type-`x` student in a benchmark outcome where type `x` invests.
Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), p.11 (PDF 11). -/
noncomputable def Benchmark.rhoX (b : Benchmark) : ℝ :=
  admitProb b.ex b.d

end ReservationPolicy


