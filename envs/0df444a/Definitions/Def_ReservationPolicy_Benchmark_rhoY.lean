-- Prove2me | Definitions.Def_ReservationPolicy_Benchmark_rhoY
-- name    : ReservationPolicy_Benchmark_rhoY
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:28.53872+00:00
-- url     : https://prove2.me/theorems/3a43056d-3f60-40c7-8435-93f4a1db3258
-- title:
--   Type-$y$ admission probability
-- statement:
--   A type-$y$ student has mean ability $\phi e_y$ and admission probability $\rho_y=\rho(\phi e_y,d)$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (4), p.11

import Mathlib
import Definitions.Def_ReservationPolicy_Benchmark
import Definitions.Def_ReservationPolicy_Params
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- The admission probability of a type-`y` student in a benchmark outcome. Bao, Ni & Singh,
SSRN 3772113 (May 30, 2023), p.11 (PDF 11). -/
noncomputable def Benchmark.rhoY (P : Params) (b : Benchmark) : ℝ :=
  admitProb (P.ϕ * b.ey) b.d

end ReservationPolicy


