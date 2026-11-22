-- Prove2me | Definitions.Def_row23_rh_supp_RH67156SegmentExtended
-- name    : row23_rh_supp_RH67156SegmentExtended
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:59:29.122491+00:00
-- url     : https://prove2.me/theorems/169e065f-dc52-4db6-bbd1-c36d37a928ca
-- title:
--   Row 23 RH support: RH67156SegmentExtended
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156Segment
import Definitions.Def_row23_rh_supp_RH67156TopSlab16Final
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156Count

/-- Extend the checked RH segment across the checked zero-free upper slab. -/
theorem segment_extended (s : ℂ) (hz : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hp : 0 < s.im)
    (ha : (121 : ℝ) ≤ s.im) (hb : s.im ≤ (67156 : ℝ) + 25 / 8192) :
    s.re = 1 / 2 := by
  by_cases h : s.im ≤ 67156
  · exact segment s hz hp ha h
  · have hc := RH67156TopSlab16R016.top_slab_clear s.re s.im h0 h1 (le_of_lt (lt_of_not_ge h)) hb
    exact False.elim (hc (by simpa only [Complex.re_add_im] using hz))

end RH67156Count
#print axioms RH67156Count.segment_extended


