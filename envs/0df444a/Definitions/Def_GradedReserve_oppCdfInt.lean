-- Prove2me | Definitions.Def_GradedReserve_oppCdfInt
-- name    : GradedReserve_oppCdfInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:49.822052+00:00
-- url     : https://prove2.me/theorems/5d6bd60d-b3a3-4dbe-89a7-c8da2383f9d6
-- title:
--   $H(v)=\int_0^v Q$
-- statement:
--   The integrated opponent distribution
--   $$H(v)=\int_0^v Q(u)\,du ,\qquad Q=F^{n-1}.$$
--   It is the equilibrium utility of type $v$ in a standard auction without reserve, and it enters the level bids of Lemma 3.2.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `H(v) = ∫₀^v Q` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5). -/
noncomputable def oppCdfInt (f : ℝ → ℝ) (n : ℕ) (v : ℝ) : ℝ := ∫ u in (0:ℝ)..v, oppCdf f n u

end GradedReserve


