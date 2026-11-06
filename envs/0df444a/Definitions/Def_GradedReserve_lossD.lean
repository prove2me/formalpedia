-- Prove2me | Definitions.Def_GradedReserve_lossD
-- name    : GradedReserve_lossD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:09.743198+00:00
-- url     : https://prove2.me/theorems/8c1a8960-d4ea-4a2c-b725-00d33ee641c7
-- title:
--   $D(b)=n\int_0^b zQ(z)f(z)\,dz$
-- statement:
--   $$D(b)=n\int_0^b z\,Q(z)\,f(z)\,dz ,$$
--   the expected revenue that anchored bidders would pay below the bid $b$; $\int_0^1D(B(t))\,dt$ is the anchored loss of Lemma 3.2.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Lemma 3.2, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `D(b) = n ∫₀^b z Q(z) f(z) dz` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Lemma 3.2, p.5, PDF 6). -/
noncomputable def lossD (f : ℝ → ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  (n : ℝ) * ∫ z in (0:ℝ)..b, z * oppCdf f n z * f z

end GradedReserve


