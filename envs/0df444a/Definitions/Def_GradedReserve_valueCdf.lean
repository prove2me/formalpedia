-- Prove2me | Definitions.Def_GradedReserve_valueCdf
-- name    : GradedReserve_valueCdf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:44.20986+00:00
-- url     : https://prove2.me/theorems/6398aedc-b087-481b-85d9-27a555465244
-- title:
--   Distribution function $F(v)=\int_0^v f$
-- statement:
--   The distribution function of the value law with density $f$ is
--   $$F(v)=\int_0^v f(u)\,du ,\qquad v\in[0,1].$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The distribution function `F(v) = ∫₀^v f` of the value law with density `f`
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5). Read on `[0, 1]`. -/
noncomputable def valueCdf (f : ℝ → ℝ) (v : ℝ) : ℝ := ∫ u in (0:ℝ)..v, f u

end GradedReserve


