-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLowRangeEnvelope
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryLowRangeEnvelope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:22:14.991211+00:00
-- url     : https://prove2.me/theorems/18149d5c-6787-4c26-8a9e-64b93d500cb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryLowRangeEnvelope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryLowRangeEnvelope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryLowRangeEnvelope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryLowRangeEnvelope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryLowRangeEnvelope.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryLowAnchors

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryLowRangeEnvelope =====
section

/-! A strengthened global upper envelope, including low and middle normalized
ranges missed by the preceding stationary exclusion. -/

namespace GeneralCK.ZeroCapLeftStationaryLowRangeEnvelope

open ZeroCapLeftStationaryRayEnvelope ZeroCapLeftStationaryLowAnchors

noncomputable def upperEnvelope (x : ℝ) : ℝ :=
  min (ZeroCapLeftStationaryRayEnvelope.upperEnvelope x)
    (min ((193 / 100) * max 1 (x / (9 / 50)))
      ((29 / 10) * max 1 (x / (3 / 10))))

theorem theta_le_upperEnvelope {x : ℝ} (hx : 0 < x) : e8Theta x ≤ upperEnvelope x := by
  apply le_min (ZeroCapLeftStationaryRayEnvelope.theta_le_upperEnvelope hx)
  exact le_min (theta_upper_ray (by norm_num) hx theta_nine_fiftieths_upper)
    (theta_upper_ray (by norm_num) hx theta_three_tenths_upper)

theorem upperEnvelope_le_previous (x : ℝ) :
    upperEnvelope x ≤ ZeroCapLeftStationaryRayEnvelope.upperEnvelope x := min_le_left _ _

theorem lowerEnvelope_mono : Monotone lowerEnvelope := by
  intro x y hxy
  unfold lowerEnvelope
  gcongr

theorem lowerEnvelope_ge_26_div_25 {x : ℝ} (hx : 3 / 32 ≤ x) :
    (26 / 25 : ℝ) ≤ lowerEnvelope x :=
  (by norm_num [lowerEnvelope] : (26 / 25 : ℝ) ≤ lowerEnvelope (3 / 32)).trans
    (lowerEnvelope_mono hx)

theorem lowerEnvelope_ge_111_div_100 {x : ℝ} (hx : 1 / 10 ≤ x) :
    (111 / 100 : ℝ) ≤ lowerEnvelope x :=
  (by norm_num [lowerEnvelope] : (111 / 100 : ℝ) ≤ lowerEnvelope (1 / 10)).trans
    (lowerEnvelope_mono hx)

theorem lowerEnvelope_ge_91_div_50 {x : ℝ} (hx : 1 / 5 ≤ x) :
    (91 / 50 : ℝ) ≤ lowerEnvelope x :=
  (by norm_num [lowerEnvelope] : (91 / 50 : ℝ) ≤ lowerEnvelope (1 / 5)).trans
    (lowerEnvelope_mono hx)

theorem upperEnvelope_le_low {x : ℝ} (hx : x ≤ 19 / 100) :
    upperEnvelope x ≤ 41 / 20 := by
  calc
    upperEnvelope x ≤ (193 / 100) * max 1 (x / (9 / 50)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    _ ≤ (193 / 100) * max 1 ((19 / 100) / (9 / 50)) := by gcongr
    _ ≤ 41 / 20 := by norm_num

theorem upperEnvelope_le_middle {x : ℝ} (hx : x ≤ 301 / 1000) :
    upperEnvelope x ≤ 291 / 100 := by
  calc
    upperEnvelope x ≤ (29 / 10) * max 1 (x / (3 / 10)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    _ ≤ (29 / 10) * max 1 ((301 / 1000) / (3 / 10)) := by gcongr
    _ ≤ 291 / 100 := by norm_num

def closedRegion (a e f c : ℝ) : Prop :=
  1 / 100 ≤ lowerEnvelope ((c - a) / (e + f)) +
    lowerEnvelope ((1 - 2 * c) / (2 * f)) - upperEnvelope ((1 - a - c) / (e + f))

theorem derivative_margin {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : closedRegion a e f c) :
    1 / 100 ≤ deriv (fun y => canonicalPureGap a y e f) c := by
  let U := (c - a) / (e + f)
  let V := (1 - a - c) / (e + f)
  let W := (1 - 2 * c) / (2 * f)
  have hUpos : 0 < U := div_pos (sub_pos.mpr hac) (add_pos he hf)
  have hVpos : 0 < V := div_pos (by linarith) (add_pos he hf)
  have hWpos : 0 < W := div_pos (by linarith) (mul_pos two_pos hf)
  have hDeriv : deriv (fun y => canonicalPureGap a y e f) c =
      e8Theta U - e8Theta V + e8Theta W := by
    rw [deriv_canonicalPureGap_right hac (by linarith) hc he hf,
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) hf]
    congr 1 <;> dsimp [U, V, W] <;> field_simp <;> ring
  change 1 / 100 ≤ lowerEnvelope U + lowerEnvelope W - upperEnvelope V at hr
  rw [hDeriv]
  linarith only [hr, lowerEnvelope_le_theta hUpos,
    lowerEnvelope_le_theta hWpos, theta_le_upperEnvelope hVpos]

theorem no_stationary {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : closedRegion a e f c) : deriv (fun y => canonicalPureGap a y e f) c ≠ 0 := by
  have h := derivative_margin hac hc he hf hr
  linarith

theorem previousRegion_subset {a e f c : ℝ}
    (hr : ZeroCapLeftStationaryRayEnvelope.closedRegion a e f c) : closedRegion a e f c := by
  unfold closedRegion
  change 1 / 100 ≤ lowerEnvelope ((c - a) / (e + f)) +
    lowerEnvelope ((1 - 2 * c) / (2 * f)) -
      ZeroCapLeftStationaryRayEnvelope.upperEnvelope ((1 - a - c) / (e + f)) at hr
  linarith only [hr, upperEnvelope_le_previous ((1 - a - c) / (e + f))]

/-- The low normalized range has a full new stationary exclusion. -/
theorem low_pair_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hU : (3 / 32) * (e + f) ≤ c - a)
    (hW : (3 / 16) * f ≤ 1 - 2 * c)
    (hV : 1 - a - c ≤ (19 / 100) * (e + f)) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hu := lowerEnvelope_ge_26_div_25 ((le_div_iff₀ hE).mpr hU)
  have hw := lowerEnvelope_ge_26_div_25 (x := (1 - 2 * c) / (2 * f))
    ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hW]))
  have hv := upperEnvelope_le_low ((div_le_iff₀ hE).mpr hV)
  unfold closedRegion
  linarith only [hu, hw, hv]

/-- An asymmetric middle range, with either assignment of the positive terms. -/
theorem middle_pair_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hpair : ((1 / 10) * (e + f) ≤ c - a ∧ (2 / 5) * f ≤ 1 - 2 * c) ∨
      ((1 / 5) * (e + f) ≤ c - a ∧ (1 / 5) * f ≤ 1 - 2 * c))
    (hV : 1 - a - c ≤ (301 / 1000) * (e + f)) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hv := upperEnvelope_le_middle ((div_le_iff₀ hE).mpr hV)
  unfold closedRegion
  rcases hpair with hfirst | hsecond
  · have hu := lowerEnvelope_ge_111_div_100 ((le_div_iff₀ hE).mpr hfirst.1)
    have hw := lowerEnvelope_ge_91_div_50 (x := (1 - 2 * c) / (2 * f))
      ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hfirst.2]))
    linarith only [hu, hw, hv]
  · have hu := lowerEnvelope_ge_91_div_50 ((le_div_iff₀ hE).mpr hsecond.1)
    have hw := lowerEnvelope_ge_111_div_100 (x := (1 - 2 * c) / (2 * f))
      ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hsecond.2]))
    linarith only [hu, hw, hv]

theorem residual_iff {a e f c : ℝ} : ¬closedRegion a e f c ↔
    lowerEnvelope ((c - a) / (e + f)) + lowerEnvelope ((1 - 2 * c) / (2 * f)) -
      upperEnvelope ((1 - a - c) / (e + f)) < 1 / 100 := by
  simp only [closedRegion, not_le]

#print axioms theta_le_upperEnvelope
#print axioms upperEnvelope_le_previous
#print axioms lowerEnvelope_mono
#print axioms upperEnvelope_le_low
#print axioms upperEnvelope_le_middle
#print axioms derivative_margin
#print axioms no_stationary
#print axioms previousRegion_subset
#print axioms low_pair_subset
#print axioms middle_pair_subset
#print axioms residual_iff

end GeneralCK.ZeroCapLeftStationaryLowRangeEnvelope

namespace GeneralCK

def LeftStationaryOutsideLowRangeEnvelopeOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryLowRangeEnvelope.closedRegion (entropyInverse e) e f c →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideLowRangeEnvelope
    (h : LeftStationaryOutsideLowRangeEnvelopeOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hr : ZeroCapLeftStationaryLowRangeEnvelope.closedRegion (entropyInverse e) e f c
  · have hac := (entropyInverse_mono he.le hf.le hef.le).trans_lt hfc
    exact False.elim (ZeroCapLeftStationaryLowRangeEnvelope.no_stationary
      hac hc he (he.trans hef) hr hstation)
  · exact h e f c he hef hf hfc hc hstation hr

theorem leftStationary_outsideRayEnvelope_of_lowRange
    (h : LeftStationaryOutsideLowRangeEnvelopeOwner) : LeftStationaryOutsideRayEnvelopeOwner := by
  intro e f c he hef hf hfc hc hstation _houtside
  exact leftStationary_of_outsideLowRangeEnvelope h e f c he hef hf hfc hc hstation

theorem leftStationary_outsideRayEnvelope_iff_lowRange :
    LeftStationaryOutsideRayEnvelopeOwner ↔ LeftStationaryOutsideLowRangeEnvelopeOwner := by
  constructor
  · intro h e f c he hef hf hfc hc hstation _houtside
    exact leftStationary_of_outsideRayEnvelope h e f c he hef hf hfc hc hstation
  · exact leftStationary_outsideRayEnvelope_of_lowRange

#print axioms leftStationary_of_outsideLowRangeEnvelope
#print axioms leftStationary_outsideRayEnvelope_of_lowRange
#print axioms leftStationary_outsideRayEnvelope_iff_lowRange

end GeneralCK

end


