-- Prove2me | Definitions.Def_GeoSemialgCSP_MULC_LeftRegular
-- name    : GeoSemialgCSP_MULC_LeftRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:14.884099+00:00
-- url     : https://prove2.me/theorems/78105778-a282-4114-ac86-815cde3a405b
-- title:
--   Left-regular Unique Games instance
-- statement:
--   A Unique Games instance is **regular on the left side** if every left vertex is incident to the same number of edge occurrences. Then choosing a left vertex uniformly and an incident edge uniformly gives a uniform edge.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_GeoSemialgCSP_MULC

namespace GeoSemialgCSP

/-- **Left regularity.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, printed p.17 (PDF p.18): the bipartite graph is regular
on the left side, i.e. all left vertices have the same number of incident edge occurrences. -/
def MULC.LeftRegular (L : MULC) : Prop :=
  ∀ v v' : Fin L.nV,
    L.edges.countP (fun e => decide (e.1 = v)) = L.edges.countP (fun e => decide (e.1 = v'))

end GeoSemialgCSP


