-- Prove2me | Definitions.Def_GradedReserve_typeMeasure
-- name    : GradedReserve_typeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:46.629195+00:00
-- url     : https://prove2.me/theorems/c814ad61-91ca-47f6-bc6f-ea2b10ddc503
-- title:
--   Law of one bidder's value
-- statement:
--   The probability measure on $\mathbb R$ with density $f$ on $[0,1]$: the law of one bidder's private value. Equilibrium conditions that hold "for almost every type" refer to this measure.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The law of one bidder's value (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5): the measure on `ℝ` with density `f`
on `[0, 1]`. "Almost every type" in the equilibrium conditions refers to this measure. -/
noncomputable def typeMeasure (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0:ℝ) 1)).withDensity (fun v => ENNReal.ofReal (f v))

end GradedReserve


