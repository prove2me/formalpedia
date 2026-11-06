-- Prove2me | Definitions.Def_GradedReserve_xStar
-- name    : GradedReserve_xStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:13.146223+00:00
-- url     : https://prove2.me/theorems/d1bc3248-45c9-4167-88ba-da770b15b4f3
-- title:
--   Candidate $x^*(t)=\bar v^{\ell}t^{\ell/p}$
-- statement:
--   $$x^*(t)=\bar v^{\,\ell}\,t^{\ell/p},\qquad t\in(0,1),$$
--   the level function of the optimal graded reserve, in the variable $x=w^\ell$ (so $w^*(t)=\bar v\,t^{1/p}$).
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_vbar
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The candidate `x*(t) = v̄^ℓ t^{ℓ/p}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19). -/
noncomputable def xStar (k : ℝ) (n : ℕ) (p t : ℝ) : ℝ :=
  vbar k n p ^ powL k n * t ^ (powL k n / p)

end GradedReserve


