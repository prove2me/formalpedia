-- Prove2me | Definitions.Def_GradedReserve_Gfun__98692e
-- name    : GradedReserve_Gfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:16.34158+00:00
-- url     : https://prove2.me/theorems/98692e50-e4a5-4e61-8dda-fb96d6620281
-- title:
--   $G[x]=\int_0^1g(x(t))\,dt$
-- statement:
--   $$G[x]=\int_0^1 g(x(t))\,dt,$$
--   the rational revenue increment over $R_n(0)$ of the level function $x$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (24), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_gfun
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `G[x] = ∫₀¹ g(x(t)) dt` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (24), p.18, PDF 19). -/
noncomputable def Gfun (k : ℝ) (n : ℕ) (x : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..1, gfun k n (x t)

end GradedReserve


