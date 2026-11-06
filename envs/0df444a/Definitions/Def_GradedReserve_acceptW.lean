-- Prove2me | Definitions.Def_GradedReserve_acceptW
-- name    : GradedReserve_acceptW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:33.701757+00:00
-- url     : https://prove2.me/theorems/eff5ae81-442d-4f23-bd94-9371e90672df
-- title:
--   Maximally filled graded reserve $\pi_w(b)=\int_0^1\mathbf 1\{B(t)\le b\}dt$
-- statement:
--   The graded reserve built from the level bids of $w$,
--   $$\pi_w(b)=\int_0^1\mathbf 1\{B(t)\le b\}\,dt ,$$
--   which accepts a bid $b$ with the largest probability compatible with incentives.
--
--   **Formalization Note** The integral is written as the Lebesgue measure of $\{t\in(0,1):B(t)\le b\}$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Lemma 3.2, p.6 (PDF 7); display (16), p.15 (PDF 16)

import Mathlib
import Definitions.Def_GradedReserve_levelBid
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The maximally filled graded reserve `π_w(b) = ∫₀¹ 1{B(t) ≤ b} dt` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Lemma 3.2, p.6, PDF 7;
display (16), p.15, PDF 16), built from the level bids `B` of the level function `w`.

**Formalization Note.** The integral of the indicator is written as the Lebesgue measure of
`{t ∈ (0, 1) : B(t) ≤ b}`. -/
noncomputable def acceptW (f : ℝ → ℝ) (n : ℕ) (w : ℝ → ℝ) (b : ℝ) : ℝ :=
  (volume {t ∈ Ioo (0:ℝ) 1 | levelBid f n w t ≤ b}).toReal

end GradedReserve


