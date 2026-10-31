-- Prove2me | Definitions.Def_ReservationPolicy_IsInvestCandidate
-- name    : ReservationPolicy_IsInvestCandidate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:43.994697+00:00
-- url     : https://prove2.me/theorems/86210aec-080c-4d5a-ae0f-f2ac0e89e92e
-- title:
--   Second-stage equilibrium when type $x$ invests
-- statement:
--   Suppose type-$x$ students invest. An outcome $(e_x,e_y,d,r_x,r_y)$ solves the effort stage when both groups are consistent at the common cutoff $d$ (`InvestGroup`, `PlainGroup`) and seats clear:
--   $$
--   z=\rho_x\,\alpha+\rho_y\,(1-\alpha).\tag{2}
--   $$
--   This is Case 1 of the proof of Proposition 1, before the first-stage deviation is examined.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eqs. (2), (9)–(13), pp.9, 12–13

import Mathlib
import Definitions.Def_ReservationPolicy_InvestGroup
import Definitions.Def_ReservationPolicy_PlainGroup
import Definitions.Def_ReservationPolicy_Benchmark_rhoX
import Definitions.Def_ReservationPolicy_Benchmark_rhoY

namespace ReservationPolicy

/-- An outcome of the effort stage when type `x` invests: both groups are consistent at the common
cutoff, and seats clear, (2). The first-stage choice is not imposed here; it is added by
`IsInvestBenchmark`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eqs. (2), (8)–(10),
pp.9, 12–13 (PDF 9, 12–13). -/
def IsInvestCandidate (P : Params) (b : Benchmark) : Prop :=
  InvestGroup P b.ex b.d b.rx ∧ PlainGroup P b.ey b.d b.ry ∧
    P.z = b.rhoX * P.α + b.rhoY P * (1 - P.α)

end ReservationPolicy


