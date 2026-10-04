-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapRightStationaryFullRadialChart
-- name    : CK_GeneralCK_PureGapZeroCapRightStationaryFullRadialChart
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T12:19:19.346073+00:00
-- url     : https://prove2.me/theorems/2edbaf6b-add1-436a-a7f5-1c78ee317c9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapRightStationaryFullRadialChart` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapRightStationaryFullRadialChart` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapRightStationaryFullRadialChart` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapRightStationaryFullRadialChart (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapRightStationaryFullRadialChart.lean)

import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_PureGapMeanStationarity

-- ===== source module GeneralCK.PureGapZeroCapRightStationaryFullRadialChart =====
section

/-!
# Full right-cap radial chart and the maximal-entropy obstruction

At a positive second cap, write the two entropy coordinates as `H u,H b`.
The free first mean is `a`, with `u<a<b<1/2`.  The value and derivative
below use the actual project profiles.  The two radii in the derivative
coincide precisely at `b=1/2`, explaining why the `f=1` chart is a
special case rather than a direct owner for `f<1`.
-/

namespace GeneralCK

/-- Exact value on the right cap's strict three-mean chamber. -/
theorem canonicalPureGap_rightCap_full_radial_eq {u a b : ℝ}
    (hu : 0 < u) (hua : u < a) (hab : a < b) (hb : b < 1 / 2) :
    canonicalPureGap a b (H u) (H b) =
      interiorCost u b +
        F (b - a) ((H u + H b) / 2) -
        F (b - u) ((H u + H b) / 2) +
        F (1 - a - b) ((H u + H b) / 2) -
        eta ((H u + H b) / 2) +
        (eta (H u) - F (1 - 2 * a) (H u)) / 2 := by
  have huHalf : u ≤ 1 / 2 := (hua.trans (hab.trans hb)).le
  have hbHalf : b ≤ 1 / 2 := hb.le
  have hcorr : entropyCorrection (H u) (H b) =
      interiorCost u b - F (b - u) ((H u + H b) / 2) := by
    simp only [entropyCorrection, atomCorrection,
      entropyInverse_H_lower hu.le huHalf,
      entropyInverse_H_lower (hu.trans (hua.trans hab)).le hbHalf]
    rw [abs_of_nonpos (by linarith : u - b ≤ 0)]
    ring
  have hright : radialPhi (1 - 2 * b) (H b) = 0 := by
    simpa [radialPhi, phi, abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * b)]
      using phi_at_entropy_cap (hu.trans (hua.trans hab)) hbHalf
  rw [canonicalPureGap, hcorr, hright]
  simp only [radialPhi]
  ring

/-- Exact first-mean derivative along the full right cap. -/
theorem deriv_canonicalPureGap_rightCap_full_radial {u a b : ℝ}
    (hu : 0 < u) (hua : u < a) (hab : a < b) (hb : b < 1 / 2) :
    deriv (fun x => canonicalPureGap x b (H u) (H b)) a =
      -deriv (fun r => F r ((H u + H b) / 2)) (b - a) -
        deriv (fun r => F r ((H u + H b) / 2)) (1 - a - b) +
        deriv (fun r => F r (H u)) (1 - 2 * a) := by
  have hHu : 0 < H u := H_pos hu (by linarith)
  have hHb : 0 < H b := H_pos (hu.trans (hua.trans hab)) (by linarith)
  exact deriv_canonicalPureGap_left hab (by linarith) (by linarith) hHu hHb

/-- The two first-mean radial arguments merge only at the maximal
second cap.  For every strict `b<1/2` they are distinct. -/
theorem rightCap_stationary_radii_eq_iff_half (a b : ℝ) :
    b - a = 1 - a - b ↔ b = 1 / 2 := by
  constructor <;> intro h <;> linarith

theorem rightCap_stationary_radii_ne_of_lt_half {a b : ℝ}
    (hb : b < 1 / 2) :
    b - a ≠ 1 - a - b := by
  intro h
  have hhalf := (rightCap_stationary_radii_eq_iff_half a b).mp h
  linarith

#print axioms canonicalPureGap_rightCap_full_radial_eq
#print axioms deriv_canonicalPureGap_rightCap_full_radial
#print axioms rightCap_stationary_radii_eq_iff_half
#print axioms rightCap_stationary_radii_ne_of_lt_half

end GeneralCK

end


