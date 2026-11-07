-- Prove2me | Definitions.Def_GeoSemialgCSP_MULC_OPT
-- name    : GeoSemialgCSP_MULC_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:22.710215+00:00
-- url     : https://prove2.me/theorems/4e1e7bdf-7b1d-4a92-8aaa-737fe09d986b
-- title:
--   Value of a Unique Games instance
-- statement:
--   The **value** of a Unique Games instance is the maximum, over all labellings of its vertices, of the fraction of edge occurrences satisfied.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_GeoSemialgCSP_MULC
import Definitions.Def_GeoSemialgCSP_MULC_satFrac

namespace GeoSemialgCSP

/-- **Value of a Unique Games instance.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, printed p.17 (PDF p.18): the maximum
fraction of satisfied edges over all labellings. -/
noncomputable def MULC.OPT (L : MULC) : ℝ :=
  ⨆ lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M), L.satFrac lab

end GeoSemialgCSP


