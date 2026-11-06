-- Prove2me | Definitions.Def_GradedReserve_revRat
-- name    : GradedReserve_revRat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:26.980591+00:00
-- url     : https://prove2.me/theorems/2696c85a-6523-431e-8def-045954913855
-- title:
--   Rational revenue $\mathrm{Rev}_{\mathrm{rat}}$ of a symmetric profile
-- statement:
--   The expected revenue of $G_\pi$ when all $n$ bidders play the symmetric strategy $\sigma$:
--   $$\mathrm{Rev}_{\mathrm{rat}}=n\int\!\!\int a\,W(a)\,\mathbf 1\{a\in[0,1]\}\,\sigma(v)(da)\,dF(v),$$
--   that is, $n$ times the expected payment of one bidder, who pays its bid when it wins.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 2.1, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_winProb
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The expected revenue `Rev_rat` of `G_π` when all `n` bidders play the symmetric strategy `σ`
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 2.1, p.4, PDF 5): `n` times the expected payment of one bidder, who pays its
bid `a` when it wins (probability `W(a)`). -/
noncomputable def revRat (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) : ℝ :=
  (n : ℝ) * ∫ v, (∫ a, (if a ∈ Icc (0:ℝ) 1 then a * winProb f n π σ a else 0) ∂(σ v))
    ∂(typeMeasure f)

end GradedReserve


