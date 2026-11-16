-- Prove2me | Definitions.Def_GradedReserve_Supplement_roundBid
-- name    : GradedReserve_Supplement_roundBid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:47:37.982373+00:00
-- url     : https://prove2.me/theorems/dd53b790-813b-46ab-9c17-cae20d14e77e
-- title:
--   Rounding up to the grid, $\tilde\beta=\lceil\beta/\Delta\rceil\Delta$
-- statement:
--   A positive bid $b$ is rounded up to the grid, $\tilde b=\lceil b/\Delta\rceil\Delta$; an exit, and a bid of $0$, become exit ("types with $\beta(v)=0$ exit").
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 6.1, p.11 (PDF 12)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- Rounding a bid up to the grid, `β̃ = ⌈β/Δ⌉Δ`, with exit kept (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 6.1, p.11, PDF 12:
"let `β̃ = ⌈β/Δ⌉Δ`"; part 2: "Types with `β(v) = 0` exit"). A positive bid `b` becomes `⌈b/Δ⌉Δ`;
an exit (negative action) or a bid of `0` becomes the exit action `−1`. -/
noncomputable def roundBid (Δ b : ℝ) : ℝ :=
  if b ≤ 0 then -1 else (⌈b / Δ⌉ : ℝ) * Δ

end GradedReserve.Supplement


