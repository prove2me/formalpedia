-- Prove2me | Definitions.Def_ReservationPolicy_IsInvestBenchmark
-- name    : ReservationPolicy_IsInvestBenchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:26:32.734241+00:00
-- url     : https://prove2.me/theorems/83fd9366-8684-440a-8b51-2fd002f782eb
-- title:
--   Benchmark equilibrium in which type $x$ invests
-- statement:
--   A benchmark equilibrium in which type $x$ invests is an effort-stage outcome (`IsInvestCandidate`) at which no type-$x$ student gains by not investing (`InvestOptimal`). It is the equilibrium of Case 1 of the proof of Proposition 1.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), pp.12–13, 35–36

import Mathlib
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_InvestOptimal

namespace ReservationPolicy

/-- A benchmark equilibrium in which type `x` invests: an effort-stage outcome together with the
first-stage optimality of investing, as in (30)–(31). Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), pp.12–13, 35–36 (PDF 12–13, 35–36). -/
def IsInvestBenchmark (P : Params) (b : Benchmark) : Prop :=
  IsInvestCandidate P b ∧ InvestOptimal P b.d b.rx b.ex

end ReservationPolicy


