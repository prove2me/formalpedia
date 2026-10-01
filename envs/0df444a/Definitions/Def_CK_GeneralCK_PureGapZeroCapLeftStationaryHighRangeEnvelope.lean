-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryHighRangeEnvelope
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryHighRangeEnvelope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:49:05.477918+00:00
-- url     : https://prove2.me/theorems/487edfe3-a114-4632-ab3b-9365b09746db
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryHighRangeEnvelope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryHighRangeEnvelope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryHighRangeEnvelope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryHighRangeEnvelope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryHighRangeEnvelope.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryHighAnchors

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryHighRangeEnvelope =====
section

/-! Stronger global slope envelopes and full higher normalized stationary
exclusions. The preceding low-range exclusion is preserved. -/

namespace GeneralCK.ZeroCapLeftStationaryHighRangeEnvelope

open ZeroCapLeftStationaryRayEnvelope ZeroCapLeftStationaryHighAnchors

noncomputable def lowerEnvelope (x : ℝ) : ℝ :=
  max (ZeroCapLeftStationaryRayEnvelope.lowerEnvelope x)
    ((89 / 20) * min 1 (x / (7 / 10)))

noncomputable def upperEnvelope (x : ℝ) : ℝ :=
  min (ZeroCapLeftStationaryLowRangeEnvelope.upperEnvelope x)
    ((59 / 10) * max 1 (x / (5 / 4)))

theorem lowerEnvelope_le_theta {x : ℝ} (hx : 0 < x) : lowerEnvelope x ≤ e8Theta x :=
  max_le (ZeroCapLeftStationaryRayEnvelope.lowerEnvelope_le_theta hx)
    (theta_lower_ray (by norm_num) hx theta_seven_tenths_lower)

theorem theta_le_upperEnvelope {x : ℝ} (hx : 0 < x) : e8Theta x ≤ upperEnvelope x :=
  le_min (ZeroCapLeftStationaryLowRangeEnvelope.theta_le_upperEnvelope hx)
    (theta_upper_ray (by norm_num) hx theta_five_quarters_upper)

theorem previous_le_lowerEnvelope (x : ℝ) :
    ZeroCapLeftStationaryRayEnvelope.lowerEnvelope x ≤ lowerEnvelope x := le_max_left _ _

theorem upperEnvelope_le_previous (x : ℝ) :
    upperEnvelope x ≤ ZeroCapLeftStationaryLowRangeEnvelope.upperEnvelope x := min_le_left _ _

theorem lowerEnvelope_ge_three {x : ℝ} (hx : 25 / 76 ≤ x) :
    (3 : ℝ) ≤ lowerEnvelope x :=
  (ZeroCapLeftStationaryRayEnvelope.lowerEnvelope_ge_second hx).trans
    (previous_le_lowerEnvelope x)

theorem lowerEnvelope_ge_89_div_20 {x : ℝ} (hx : 7 / 10 ≤ x) :
    (89 / 20 : ℝ) ≤ lowerEnvelope x := by
  have hr : (1 : ℝ) ≤ x / (7 / 10) :=
    (le_div_iff₀ (by norm_num)).mpr (by simpa using hx)
  unfold lowerEnvelope
  rw [min_eq_left hr, mul_one]
  exact le_max_right _ _

theorem upperEnvelope_le_59_div_10 {x : ℝ} (hx : x ≤ 5 / 4) :
    upperEnvelope x ≤ 59 / 10 := by
  have hr : x / (5 / 4) ≤ (1 : ℝ) := (div_le_one (by norm_num)).mpr hx
  exact (min_le_right _ _).trans (by rw [max_eq_left hr, mul_one])

theorem upperEnvelope_le_744_div_100 {x : ℝ} (hx : x ≤ 63 / 40) :
    upperEnvelope x ≤ 744 / 100 := by
  calc
    upperEnvelope x ≤ (59 / 10) * max 1 (x / (5 / 4)) := min_le_right _ _
    _ ≤ (59 / 10) * max 1 ((63 / 40) / (5 / 4)) := by gcongr
    _ ≤ 744 / 100 := by norm_num

theorem upperEnvelope_le_889_div_100 {x : ℝ} (hx : x ≤ 47 / 25) :
    upperEnvelope x ≤ 889 / 100 := by
  calc
    upperEnvelope x ≤ (59 / 10) * max 1 (x / (5 / 4)) := min_le_right _ _
    _ ≤ (59 / 10) * max 1 ((47 / 25) / (5 / 4)) := by gcongr
    _ ≤ 889 / 100 := by norm_num

def closedRegion (a e f c : ℝ) : Prop :=
  0 < lowerEnvelope ((c - a) / (e + f)) +
    lowerEnvelope ((1 - 2 * c) / (2 * f)) - upperEnvelope ((1 - a - c) / (e + f))

theorem envelope_le_derivative {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f) :
    lowerEnvelope ((c - a) / (e + f)) +
      lowerEnvelope ((1 - 2 * c) / (2 * f)) - upperEnvelope ((1 - a - c) / (e + f)) ≤
        deriv (fun y => canonicalPureGap a y e f) c := by
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
    congr 1 <;> dsimp [U, V, W] <;> field_simp
  change lowerEnvelope U + lowerEnvelope W - upperEnvelope V ≤ _
  rw [hDeriv]
  linarith only [lowerEnvelope_le_theta hUpos,
    lowerEnvelope_le_theta hWpos, theta_le_upperEnvelope hVpos]

theorem derivative_positive {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : closedRegion a e f c) :
    0 < deriv (fun y => canonicalPureGap a y e f) c :=
  hr.trans_le (envelope_le_derivative hac hc he hf)

theorem derivative_margin {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : 1 / 100 ≤ lowerEnvelope ((c - a) / (e + f)) +
      lowerEnvelope ((1 - 2 * c) / (2 * f)) - upperEnvelope ((1 - a - c) / (e + f))) :
    1 / 100 ≤ deriv (fun y => canonicalPureGap a y e f) c :=
  hr.trans (envelope_le_derivative hac hc he hf)

theorem no_stationary {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hr : closedRegion a e f c) : deriv (fun y => canonicalPureGap a y e f) c ≠ 0 :=
  (derivative_positive hac hc he hf hr).ne'

theorem previousRegion_subset {a e f c : ℝ}
    (hr : ZeroCapLeftStationaryLowRangeEnvelope.closedRegion a e f c) : closedRegion a e f c := by
  unfold closedRegion
  change 1 / 100 ≤ ZeroCapLeftStationaryRayEnvelope.lowerEnvelope ((c - a) / (e + f)) +
    ZeroCapLeftStationaryRayEnvelope.lowerEnvelope ((1 - 2 * c) / (2 * f)) -
      ZeroCapLeftStationaryLowRangeEnvelope.upperEnvelope ((1 - a - c) / (e + f)) at hr
  linarith only [hr, upperEnvelope_le_previous ((1 - a - c) / (e + f)),
    previous_le_lowerEnvelope ((c - a) / (e + f)),
    previous_le_lowerEnvelope ((1 - 2 * c) / (2 * f))]

/-- The preceding high-pair range extends from V<=5/6 to V<=5/4. -/
theorem moderate_pair_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hU : (25 / 76) * (e + f) ≤ c - a)
    (hW : (25 / 38) * f ≤ 1 - 2 * c)
    (hV : 1 - a - c ≤ (5 / 4) * (e + f)) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hu := lowerEnvelope_ge_three ((le_div_iff₀ hE).mpr hU)
  have hw := lowerEnvelope_ge_three (x := (1 - 2 * c) / (2 * f))
    ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hW]))
  have hv := upperEnvelope_le_59_div_10 ((div_le_iff₀ hE).mpr hV)
  unfold closedRegion
  linarith only [hu, hw, hv]

theorem high_pair_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hU : (7 / 10) * (e + f) ≤ c - a)
    (hW : (7 / 5) * f ≤ 1 - 2 * c)
    (hV : 1 - a - c ≤ (47 / 25) * (e + f)) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hu := lowerEnvelope_ge_89_div_20 ((le_div_iff₀ hE).mpr hU)
  have hw := lowerEnvelope_ge_89_div_20 (x := (1 - 2 * c) / (2 * f))
    ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hW]))
  have hv := upperEnvelope_le_889_div_100 ((div_le_iff₀ hE).mpr hV)
  unfold closedRegion
  linarith only [hu, hw, hv]

theorem mixed_pair_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hpair : ((25 / 76) * (e + f) ≤ c - a ∧ (7 / 5) * f ≤ 1 - 2 * c) ∨
      ((7 / 10) * (e + f) ≤ c - a ∧ (25 / 38) * f ≤ 1 - 2 * c))
    (hV : 1 - a - c ≤ (63 / 40) * (e + f)) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hv := upperEnvelope_le_744_div_100 ((div_le_iff₀ hE).mpr hV)
  unfold closedRegion
  rcases hpair with hfirst | hsecond
  · have hu := lowerEnvelope_ge_three ((le_div_iff₀ hE).mpr hfirst.1)
    have hw := lowerEnvelope_ge_89_div_20 (x := (1 - 2 * c) / (2 * f))
      ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hfirst.2]))
    linarith only [hu, hw, hv]
  · have hu := lowerEnvelope_ge_89_div_20 ((le_div_iff₀ hE).mpr hsecond.1)
    have hw := lowerEnvelope_ge_three (x := (1 - 2 * c) / (2 * f))
      ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hsecond.2]))
    linarith only [hu, hw, hv]

theorem residual_iff {a e f c : ℝ} : ¬closedRegion a e f c ↔
    lowerEnvelope ((c - a) / (e + f)) + lowerEnvelope ((1 - 2 * c) / (2 * f)) -
      upperEnvelope ((1 - a - c) / (e + f)) ≤ 0 := by
  simp only [closedRegion, not_lt]

#print axioms lowerEnvelope_le_theta
#print axioms theta_le_upperEnvelope
#print axioms previous_le_lowerEnvelope
#print axioms upperEnvelope_le_previous
#print axioms envelope_le_derivative
#print axioms derivative_positive
#print axioms derivative_margin
#print axioms no_stationary
#print axioms previousRegion_subset
#print axioms moderate_pair_subset
#print axioms high_pair_subset
#print axioms mixed_pair_subset
#print axioms residual_iff

end GeneralCK.ZeroCapLeftStationaryHighRangeEnvelope

namespace GeneralCK

def LeftStationaryOutsideHighRangeEnvelopeOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryHighRangeEnvelope.closedRegion (entropyInverse e) e f c →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideHighRangeEnvelope
    (h : LeftStationaryOutsideHighRangeEnvelopeOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hr : ZeroCapLeftStationaryHighRangeEnvelope.closedRegion (entropyInverse e) e f c
  · have hac := (entropyInverse_mono he.le hf.le hef.le).trans_lt hfc
    exact False.elim (ZeroCapLeftStationaryHighRangeEnvelope.no_stationary
      hac hc he (he.trans hef) hr hstation)
  · exact h e f c he hef hf hfc hc hstation hr

theorem leftStationary_outsideLowRangeEnvelope_of_highRange
    (h : LeftStationaryOutsideHighRangeEnvelopeOwner) : LeftStationaryOutsideLowRangeEnvelopeOwner := by
  intro e f c he hef hf hfc hc hstation _houtside
  exact leftStationary_of_outsideHighRangeEnvelope h e f c he hef hf hfc hc hstation

theorem leftStationary_outsideLowRangeEnvelope_iff_highRange :
    LeftStationaryOutsideLowRangeEnvelopeOwner ↔ LeftStationaryOutsideHighRangeEnvelopeOwner := by
  constructor
  · intro h e f c he hef hf hfc hc hstation _houtside
    exact leftStationary_of_outsideLowRangeEnvelope h e f c he hef hf hfc hc hstation
  · exact leftStationary_outsideLowRangeEnvelope_of_highRange

#print axioms leftStationary_of_outsideHighRangeEnvelope
#print axioms leftStationary_outsideLowRangeEnvelope_of_highRange
#print axioms leftStationary_outsideLowRangeEnvelope_iff_highRange

end GeneralCK

end


