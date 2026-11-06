-- Prove2me | Definitions.Def_GradedReserve_piStar
-- name    : GradedReserve_piStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:11.568228+00:00
-- url     : https://prove2.me/theorems/c24bb47a-5970-4ece-a23c-ef767f35b562
-- title:
--   Optimal graded reserve $\pi^*(b)=\min\{(b/b_0)^p,1\}$
-- statement:
--   $$\pi^*(b)=\min\{(b/b_0)^p,\,1\},\qquad b\in[0,1].$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
import Definitions.Def_GradedReserve_bZero
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The optimal graded reserve `π*(b) = min{(b/b₀)^p, 1}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6).
Read on `b ∈ [0, 1]`. -/
noncomputable def piStar (k : ℝ) (n : ℕ) (p b : ℝ) : ℝ := min ((b / bZero k n p) ^ p) 1

end GradedReserve


