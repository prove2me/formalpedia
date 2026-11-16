-- Prove2me | Definitions.Def_GradedReserve_Supplement_allocAgainst
-- name    : GradedReserve_Supplement_allocAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:33:51.921605+00:00
-- url     : https://prove2.me/theorems/9cba76ef-0620-4ba8-8bca-2d660f57e886
-- title:
--   Win probability $W_i(b)$ against a law of opponents' actions
-- statement:
--   Let $\mu$ be a law of action profiles. The probability that bidder $i$ receives the item when it takes action $b$ and the other bidders' actions are drawn from $\mu$ is
--   $$W_i(b)=\int \mathrm{alloc}\big(x_{-i},b\big)_i\,\mu(dx),$$
--   where $(x_{-i},b)$ replaces the $i$-th coordinate of $x$ by $b$. The law $\mu$ may have any dependence across opponents.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section B, p.26 (PDF 27); Theorem 4.3 part 5, p.10 (PDF 11)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The probability `W(b)` that bidder `i` receives the item when it takes action `b` and the
action profile of the others is drawn from `μ` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section B, p.26, PDF 27, "`Wᵢ(b)` the
allocation probability from an effective bid `b` against bidder `i`'s opponents"; Theorem 4.3
part 5, p.10, PDF 11). Coordinate `i` of the profile drawn from `μ` is replaced by `b`, so only
the law of the opponents' actions matters; `μ` may have any dependence across opponents. -/
noncomputable def allocAgainst {n : ℕ} (M : Mechanism n) (μ : Measure (Fin n → ℝ)) (i : Fin n)
    (b : ℝ) : ℝ :=
  ∫ x, M.alloc (Function.update x i b) i ∂μ

end GradedReserve.Supplement


