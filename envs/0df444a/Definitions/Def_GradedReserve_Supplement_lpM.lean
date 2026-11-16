-- Prove2me | Definitions.Def_GradedReserve_Supplement_lpM
-- name    : GradedReserve_Supplement_lpM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:42:29.14719+00:00
-- url     : https://prove2.me/theorems/b1fa3aa1-ef4b-4c91-902c-eed95dfbd7b3
-- title:
--   $m_a(v)=vQ(v)-\int_a^vQ$
-- statement:
--   For a participation threshold $a$,
--   $$m_a(v)=vQ(v)-\int_a^v Q(t)\,dt,$$
--   the interim expected payment of a type $v\ge a$ that trades with probability $Q(v)$ when the types below $a$ exit.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.3, p.9 (PDF 10); display (50), p.31 (PDF 32)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- `m_a(v) = v Q(v) − ∫_a^v Q` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.3, p.9, PDF 10; display (50), p.31, PDF 32), the
interim expected payment of type `v ≥ a` when the types above the participation threshold `a`
trade with probability `Q(v)`. -/
noncomputable def lpM (f : ℝ → ℝ) (n : ℕ) (a v : ℝ) : ℝ :=
  v * oppCdf f n v - ∫ t in a..v, oppCdf f n t

end GradedReserve.Supplement


