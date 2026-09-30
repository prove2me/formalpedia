-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_GapLB
-- name    : CK_CKLaneM07_CE_GapLB
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:50:56.864986+00:00
-- url     : https://prove2.me/theorems/560cf0ca-43eb-4f46-8cba-92d2bf7e2a30
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.GapLB` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.GapLB` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.GapLB` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.GapLB (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/GapLB.lean)

import Definitions.Def_CK_CKLaneM07_CE_Bridge
import Definitions.Def_CK_GeneralCK_RadialConvexity

-- ===== source module CKLaneM07.CE.GapLB =====
section

/-!
# Lane M07 / CE-stat row 3: a stationarity-free lower bound for the Case-E pure gap

For a Case-E configuration (`0 < e < f ≤ 1`, `ι f < c < 1/2`, `a = ι e`, `b = ι f`, `h = (e+f)/2`,
`u_E = ι h`, `t_C = rc(1 − 2c, f)`), convexity of `F(·, h)` and `F(·, f)` in the radius (tangent lines at
the cap contacts `1 − 2u_E` and `1 − 2c`) gives

`canonicalPureGap a c e f ≥ F(c − a, h) − F(b − a, h) + (b − a)(J a − J b)/2
                             + Υ(u_E)(2u_E − a − c) + Υ(t_C)(c − b)`.

No stationarity is used.  The right side has no `O(1)` cancellation: its first-order part is the
Jensen gap `2ι((e+f)/2) − ι e − ι f` of the convex `ι`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open GeneralCK CKLaneN1.CEStat Set

/-- tangent line of a convex differentiable function -/
theorem tangent_le {f : ℝ → ℝ} {S : Set ℝ} {x y f' : ℝ} (hfc : ConvexOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasDerivAt f f' x) : f x + f' * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with h | h | h
  · have := hfc.le_slope_of_hasDerivAt hx hy h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at this
    linarith
  · subst h; simp
  · have := hfc.slope_le_of_hasDerivAt hy hx h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at this
    linarith

/-- the tangent inequality for `F(·, h)` at a positive radius -/
theorem F_tangent {h z₀ z : ℝ} (hh : 0 < h) (hz₀ : 0 < z₀) (hz : 0 ≤ z) :
    F z₀ h + radialSlope (radialContact z₀ h) * (z - z₀) ≤ F z h :=
  tangent_le (convexOn_F_radius hh) (show z₀ ∈ Ici (0 : ℝ) from hz₀.le) (show z ∈ Ici (0 : ℝ) from hz)
    (hasDerivAt_F_radius_slope hz₀ hh)

/-- the cap contact: `rc(1 − 2 ι h, h) = ι h` for `0 < h < 1` -/
theorem cap_contact {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    radialContact (1 - 2 * entropyInverse h) h = entropyInverse h := by
  have hp := entropyInverse_pos h0 h1.le
  have hl := entropyInverse_lt_half h0.le h1
  apply radialContact_eq_of_equation (by linarith) h0 hp hl
  rw [(entropyInverse_spec h0.le h1.le).2.2]; ring

/-- `η h = F(1 − 2 ι h, h)` for `0 < h < 1` -/
theorem eta_eq_F {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    eta h = F (1 - 2 * entropyInverse h) h := by
  have hl := entropyInverse_lt_half h0.le h1
  have hz : (1 - 2 * entropyInverse h) ≠ 0 := by linarith
  simp only [eta, h1.ne, if_false, F, hz, cap_contact h0 h1]

/-- the stationarity-free lower bound (bits) -/
noncomputable def gapLB (e f c : ℝ) : ℝ :=
  F (c - entropyInverse e) ((e + f) / 2) - F (entropyInverse f - entropyInverse e) ((e + f) / 2) +
    (entropyInverse f - entropyInverse e) * (J (entropyInverse e) - J (entropyInverse f)) / 2 +
    radialSlope (entropyInverse ((e + f) / 2)) *
      (2 * entropyInverse ((e + f) / 2) - entropyInverse e - c) +
    radialSlope (radialContact (1 - 2 * c) f) * (c - entropyInverse f)

theorem gapLB_le {e f c : ℝ} (hp : PointFree e f c) :
    gapLB e f c ≤ canonicalPureGap (entropyInverse e) c e f := by
  have P := ptFacts hp
  have hh := P.hh
  have hh1 := P.hh1
  have huE := entropyInverse_pos hh (le_of_lt hh1)
  have huE' := entropyInverse_lt_half hh.le hh1
  have hf1' : f ≠ 1 := by
    intro hf
    have : entropyInverse f = 1 / 2 := by rw [hf, GeneralCK.Scalar.entropyInverse_one]
    linarith [P.hb2]
  have hf1 : f < 1 := lt_of_le_of_ne P.hf1 hf1'
  -- tangent at the cap contact of `h`
  have t1 := F_tangent (z₀ := 1 - 2 * entropyInverse ((e + f) / 2)) (z := 1 - entropyInverse e - c)
    hh (by linarith) P.hcen.le
  rw [cap_contact hh hh1] at t1
  -- tangent at the right radius `1 − 2c` of `f`
  have t2 := F_tangent (z₀ := 1 - 2 * c) (z := 1 - 2 * entropyInverse f) P.hf0 P.hcr
    (by linarith [P.hb2])
  have hcorr : entropyCorrection e f =
      (entropyInverse f - entropyInverse e) * (J (entropyInverse e) - J (entropyInverse f)) / 2 -
        F (entropyInverse f - entropyInverse e) ((e + f) / 2) := by
    unfold entropyCorrection atomCorrection interiorCost
    rw [P.hHa, P.hHb, abs_of_neg (by linarith [P.hab] : entropyInverse e - entropyInverse f < 0),
      neg_sub]
  have hra : radialContact (1 - 2 * entropyInverse e) e = entropyInverse e := cap_contact P.he P.he1
  have hphi_a : radialPhi (1 - 2 * entropyInverse e) e = 0 := by
    unfold radialPhi
    rw [eta_eq_F P.he P.he1]; ring
  have hphi_f : radialPhi (1 - 2 * c) f = F (1 - 2 * entropyInverse f) f - F (1 - 2 * c) f := by
    unfold radialPhi; rw [eta_eq_F P.hf0 hf1]
  have hphi_h : radialPhi (1 - entropyInverse e - c) ((e + f) / 2) =
      F (1 - 2 * entropyInverse ((e + f) / 2)) ((e + f) / 2) -
        F (1 - entropyInverse e - c) ((e + f) / 2) := by
    unfold radialPhi; rw [eta_eq_F hh hh1]
  unfold canonicalPureGap gapLB
  rw [hcorr, hphi_a, hphi_f, hphi_h]
  nlinarith [t1, t2]

end CKLaneM07.CE

end


