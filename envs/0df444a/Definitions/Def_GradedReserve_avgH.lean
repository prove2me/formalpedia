-- Prove2me | Definitions.Def_GradedReserve_avgH
-- name    : GradedReserve_avgH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:01.28057+00:00
-- url     : https://prove2.me/theorems/10941553-9f25-45b1-ae05-e48a3d9fc04b
-- title:
--   $M(t)=\frac1t\int_0^tH(w(u))\,du$
-- statement:
--   For a level function $w$ and $t\in(0,1)$,
--   $$M(t)=\frac1t\int_0^t H(w(u))\,du .$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Lemma 3.2, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_oppCdfInt
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `M(t) = (1/t) ∫₀^t H(w(u)) du` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Lemma 3.2, p.5, PDF 6), for a level function `w`.
Read for `t ∈ (0, 1)`. -/
noncomputable def avgH (f : ℝ → ℝ) (n : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / t) * ∫ u in (0:ℝ)..t, oppCdfInt f n (w u)

end GradedReserve


