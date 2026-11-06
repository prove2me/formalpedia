-- Prove2me | Definitions.Def_GradedReserve_expMax
-- name    : GradedReserve_expMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:34.862965+00:00
-- url     : https://prove2.me/theorems/e8007975-c1a8-4233-927e-c27a5659a131
-- title:
--   Expected highest value $\mathbb E[V_{(1)}]$
-- statement:
--   The expected highest of the $n$ values, whose law has density $nQf$:
--   $$\mathbb E[V_{(1)}]=n\int_0^1 v\,Q(v)\,f(v)\,dv .$$
--   It is the ceiling for the anchored revenue of a bid-bounded mechanism.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5); proof of Lemma 3.2, p.16 (PDF 17)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `E[V₍₁₎]`, the expected highest of `n` values (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5; Lemma 3.2, p.6,
PDF 7): the maximum has density `n Q f` (p.16), so `E[V₍₁₎] = n ∫₀¹ v Q(v) f(v) dv`. -/
noncomputable def expMax (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ∫ v in (0:ℝ)..1, v * oppCdf f n v * f v

end GradedReserve


