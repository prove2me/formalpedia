-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsGridPoint
-- name    : GradedReserve_Supplement_IsGridPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:47:22.159206+00:00
-- url     : https://prove2.me/theorems/c2717742-f27a-4b09-96ab-ca99fe7facac
-- title:
--   Point of the bid grid $\{0,\Delta,\dots,1\}$
-- statement:
--   A number $b$ is a point of the bid grid if $b=k\Delta$ for some $k\in\mathbb N$ and $b\le1$. With $1/\Delta\in\mathbb N$ the grid is $\{0,\Delta,2\Delta,\dots,1\}$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 6, p.11 (PDF 12)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- A point of the bid grid `{0, Δ, 2Δ, …, 1}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 6, p.11, PDF 12: "Interfaces accept
bids on a grid `{0, Δ, …, 1}`"). -/
def IsGridPoint (Δ b : ℝ) : Prop := ∃ k : ℕ, b = k * Δ ∧ b ≤ 1

end GradedReserve.Supplement


