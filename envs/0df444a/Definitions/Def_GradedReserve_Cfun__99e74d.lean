-- Prove2me | Definitions.Def_GradedReserve_Cfun__99e74d
-- name    : GradedReserve_Cfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:13.285001+00:00
-- url     : https://prove2.me/theorems/99e74df7-b467-4d39-aabe-af22480857eb
-- title:
--   Anchored loss $C[x]=\int_0^1c(x(t),\widetilde M(t))\,dt$
-- statement:
--   $$C[x]=\int_0^1 c\big(x(t),\widetilde M(t)\big)\,dt,\qquad \widetilde M(t)=\frac1t\int_0^tx .$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, display (25), p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_cfun
import Definitions.Def_GradedReserve_hardyAvg
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The anchored loss `C[x] = ∫₀¹ c(x(t), M̃(t)) dt` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, (25), p.18, PDF 19). -/
noncomputable def Cfun (k : ℝ) (n : ℕ) (x : ℝ → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, cfun k n (x t) (hardyAvg x t)

end GradedReserve


