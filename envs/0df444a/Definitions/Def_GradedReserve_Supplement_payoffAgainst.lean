-- Prove2me | Definitions.Def_GradedReserve_Supplement_payoffAgainst
-- name    : GradedReserve_Supplement_payoffAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:34:56.994365+00:00
-- url     : https://prove2.me/theorems/2d99dbbf-539f-46bb-a3c6-37b6a599f987
-- title:
--   Interim utility $u_i(v,b)=vW_i(b)-P_i(b)$
-- statement:
--   The expected utility of a risk-neutral bidder $i$ of value $v$ that takes action $b$ against opponents whose actions are drawn from $\mu$ is
--   $$u_i(v,b)=v\,W_i(b)-P_i(b).$$
--   In $\mathrm{LP}(d,\lambda)$ this is display (41), $u_i(v,b)=[v-(1-\lambda)b]W_i(b)-\lambda b$ for a valid bid, and in $G_\pi$ it is $(v-b)W_i(b)$. Exit has utility $0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), display (41), p.26 (PDF 27); Theorem 4.3 part 5, p.10 (PDF 11)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_allocAgainst
import Definitions.Def_GradedReserve_Supplement_payAgainst
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The expected utility of a risk-neutral bidder `i` of value `v` taking action `b` against
opponents whose action profile is drawn from `μ`: value times allocation probability minus
expected payment (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), display (41), p.26, PDF 27, `uᵢ(v, b) = [v − (1 − λ)b]Wᵢ(b) − λb` for
`LP(d, λ)`, `(v − b)Wᵢ(b)` for `G_π`; Theorem 4.3 part 5, p.10, PDF 11). Exit (any action outside
`[0, 1]`) has utility `0` in every mechanism of this mission. -/
noncomputable def payoffAgainst {n : ℕ} (M : Mechanism n) (μ : Measure (Fin n → ℝ)) (i : Fin n)
    (v b : ℝ) : ℝ :=
  v * allocAgainst M μ i b - payAgainst M μ i b

end GradedReserve.Supplement


