-- Prove2me | Definitions.Def_GradedReserve_threshold
-- name    : GradedReserve_threshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:03.045668+00:00
-- url     : https://prove2.me/theorems/861c5a91-417c-456b-a22c-5b2d63e9ab78
-- title:
--   Level threshold $T(t)$ of a graded reserve
-- statement:
--   For a graded reserve $\pi$ and a level $t\in(0,1)$, the bid threshold of level $t$ is
--   $$T(t)=\inf\{b:\pi(b)\ge t\},$$
--   the lowest bid that is accepted with probability at least $t$.
--
--   **Formalization Note** The infimum is over $b\in[0,1]$; a level never reached on $[0,1]$ gets $T(t)=1$ (in the paper it is $+\infty$; every level bid is at most $1$, so comparisons with $B(t)$ are unaffected).
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), proof of Lemma 3.2, p.15 (PDF 16)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The level-`t` bid threshold `T(t) = inf{b : π(b) ≥ t}` of a graded reserve `π` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), proof of
Lemma 3.2, p.15, PDF 16, "let its level-t bid threshold be T(t)").

**Formalization Note.** The infimum is over bids `b ∈ [0, 1]`; a level that `π` never reaches on
`[0, 1]` gets `T(t) = 1` (the paper's threshold is then `+∞`; every level bid is at most `1`, so
the inequality `T ≥ B` is unaffected). -/
noncomputable def threshold (π : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf (insert 1 {b ∈ Icc (0:ℝ) 1 | t ≤ π b})

end GradedReserve


