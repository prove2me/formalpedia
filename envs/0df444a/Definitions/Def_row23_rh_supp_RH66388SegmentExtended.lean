-- Prove2me | Definitions.Def_row23_rh_supp_RH66388SegmentExtended
-- name    : row23_rh_supp_RH66388SegmentExtended
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:40:46.950375+00:00
-- url     : https://prove2.me/theorems/aed4ba1a-3480-4948-bbd2-86474ff2078f
-- title:
--   Row 23 RH support: RH66388SegmentExtended
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Segment
import Definitions.Def_row23_rh_supp_RH66388TopSlab16Final
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66388Count

/-- Extend the checked RH segment across the checked zero-free upper slab. -/
theorem segment_extended (s : ℂ) (hz : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hp : 0 < s.im)
    (ha : (121 : ℝ) ≤ s.im) (hb : s.im ≤ (66388 : ℝ) + 25 / 8192) :
    s.re = 1 / 2 := by
  by_cases h : s.im ≤ 66388
  · exact segment s hz hp ha h
  · have hc := RH66388TopSlab16R016.top_slab_clear s.re s.im h0 h1 (le_of_lt (lt_of_not_ge h)) hb
    exact False.elim (hc (by simpa only [Complex.re_add_im] using hz))

end RH66388Count
#print axioms RH66388Count.segment_extended


