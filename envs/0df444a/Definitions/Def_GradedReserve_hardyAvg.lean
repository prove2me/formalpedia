-- Prove2me | Definitions.Def_GradedReserve_hardyAvg
-- name    : GradedReserve_hardyAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:00.404611+00:00
-- url     : https://prove2.me/theorems/189b5324-1943-4ad5-a381-628fa98283c6
-- title:
--   Hardy average $\widetilde M(t)=t^{-1}\int_0^tx$
-- statement:
--   For a function $x$ on $(0,1)$,
--   $$\widetilde M(t)=\frac1t\int_0^t x(u)\,du .$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.18 (PDF 19)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The Hardy average `M̃(t) = t⁻¹ ∫₀^t x(u) du` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19). Read for
`t ∈ (0, 1)`. -/
noncomputable def hardyAvg (x : ℝ → ℝ) (t : ℝ) : ℝ := (1 / t) * ∫ u in (0:ℝ)..t, x u

end GradedReserve


