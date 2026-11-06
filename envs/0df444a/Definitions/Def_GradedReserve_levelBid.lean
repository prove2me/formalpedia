-- Prove2me | Definitions.Def_GradedReserve_levelBid
-- name    : GradedReserve_levelBid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:30.593623+00:00
-- url     : https://prove2.me/theorems/7d40a1e6-4df2-4d5f-abe9-8f0239764c42
-- title:
--   Level bid $B(t)$, display (4)
-- statement:
--   For a level function $w$, the minimal bid supporting level $t$ is
--   $$B(t)=w(t)-\frac{H(w(t))-M(t)}{Q(w(t))},$$
--   with $B(t)=0$ if $w(t)=0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Lemma 3.2, display (4), p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_oppCdfInt
import Definitions.Def_GradedReserve_avgH
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The level bid (4) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Lemma 3.2, display (4), p.5, PDF 6):
`B(t) = w(t) − (H(w(t)) − M(t))/Q(w(t))`, with `B(t) = 0` if `w(t) = 0`. -/
noncomputable def levelBid (f : ℝ → ℝ) (n : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  if w t = 0 then 0
  else w t - (oppCdfInt f n (w t) - avgH f n w t) / oppCdf f n (w t)

end GradedReserve


