-- Prove2me | Definitions.Def_GradedReserve_cZero
-- name    : GradedReserve_cZero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:09.569025+00:00
-- url     : https://prove2.me/theorems/0b76ba05-7d59-4bd4-9eea-eb611e10b096
-- title:
--   $c_0=(p+m)/(p+\ell)$
-- statement:
--   $$c_0=\frac{p+m}{p+\ell}.$$
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powL
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- `c₀ = (p + m)/(p + ℓ)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, p.18, PDF 19). -/
noncomputable def cZero (k : ℝ) (n : ℕ) (p : ℝ) : ℝ := (p + powM k n) / (p + powL k n)

end GradedReserve


