-- Prove2me | Definitions.Def_GradedReserve_Supplement_payAgainst
-- name    : GradedReserve_Supplement_payAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:34:19.359188+00:00
-- url     : https://prove2.me/theorems/368105aa-d8c9-40b9-8fc2-0b86f8534ee9
-- title:
--   Expected payment from action $b$ against a law of opponents' actions
-- statement:
--   The expected payment of bidder $i$ when it takes action $b$ and the other bidders' actions are drawn from $\mu$:
--   $$P_i(b)=\int \mathrm{pay}\big(x_{-i},b\big)_i\,\mu(dx).$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section B, p.26 (PDF 27); Theorem 4.3 part 5, p.10 (PDF 11)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The expected payment of bidder `i` when it takes action `b` and the action profile of the
others is drawn from `μ` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section B, p.26, PDF 27; Theorem 4.3 part 5, p.10, PDF 11).
Coordinate `i` of the profile drawn from `μ` is replaced by `b`. -/
noncomputable def payAgainst {n : ℕ} (M : Mechanism n) (μ : Measure (Fin n → ℝ)) (i : Fin n)
    (b : ℝ) : ℝ :=
  ∫ x, M.pay (Function.update x i b) i ∂μ

end GradedReserve.Supplement


