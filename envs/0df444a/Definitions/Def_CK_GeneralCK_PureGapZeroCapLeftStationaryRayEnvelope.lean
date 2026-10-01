-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryRayEnvelope
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryRayEnvelope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T13:56:59.319046+00:00
-- url     : https://prove2.me/theorems/ebb00642-e70d-4a99-98d4-6f0bbbfd3f10
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryRayEnvelope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryRayEnvelope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryRayEnvelope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryRayEnvelope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryRayEnvelope.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryAnchorRegion

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryRayEnvelope =====
section

/-!
# Ray envelopes for the remaining left-stationary comparison

Monotonicity and the decreasing quotient Theta(x)/x extend the accepted
point anchors along entire rays. The resulting rational envelopes give a
larger unconditional stationary exclusion and an exact residual contract.
-/

namespace GeneralCK.ZeroCapLeftStationaryRayEnvelope

open ZeroCapLeftStationaryNarrowMiddleCertified

theorem theta_lower_ray {r x l : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hl : l ≤ e8Theta r) : l * min 1 (x / r) ≤ e8Theta x := by
  by_cases hxr : x ≤ r
  · rw [min_eq_right ((div_le_one hr).mpr hxr)]
    have hratio := antitoneOn_e8Theta_div hx hr hxr
    calc
      l * (x / r) ≤ e8Theta r * (x / r) :=
        mul_le_mul_of_nonneg_right hl (div_nonneg hx.le hr.le)
      _ = x * (e8Theta r / r) := by ring
      _ ≤ x * (e8Theta x / x) := mul_le_mul_of_nonneg_left hratio hx.le
      _ = e8Theta x := by field_simp
  · have hrx : r ≤ x := (lt_of_not_ge hxr).le
    rw [min_eq_left ((le_div_iff₀ hr).mpr (by simpa using hrx)), mul_one]
    exact hl.trans (strictMonoOn_e8Theta_pos.monotoneOn hr hx hrx)

theorem theta_upper_ray {r x u : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hu : e8Theta r ≤ u) : e8Theta x ≤ u * max 1 (x / r) := by
  by_cases hxr : x ≤ r
  · rw [max_eq_left ((div_le_one hr).mpr hxr), mul_one]
    exact (strictMonoOn_e8Theta_pos.monotoneOn hx hr hxr).trans hu
  · have hrx : r ≤ x := (lt_of_not_ge hxr).le
    rw [max_eq_right ((le_div_iff₀ hr).mpr (by simpa using hrx))]
    have hratio := antitoneOn_e8Theta_div hr hx hrx
    calc
      e8Theta x = x * (e8Theta x / x) := by field_simp
      _ ≤ x * (e8Theta r / r) := mul_le_mul_of_nonneg_left hratio hx.le
      _ = e8Theta r * (x / r) := by ring
      _ ≤ u * (x / r) := mul_le_mul_of_nonneg_right hu (div_nonneg hx.le hr.le)

noncomputable def lowerEnvelope (x : ℝ) : ℝ :=
  max ((121 / 100) * min 1 (x / (3175 / 29184)))
    (3 * min 1 (x / (25 / 76)))

noncomputable def upperEnvelope (x : ℝ) : ℝ :=
  (417 / 100) * max 1 (x / (375 / 646))

theorem lowerEnvelope_le_theta {x : ℝ} (hx : 0 < x) : lowerEnvelope x ≤ e8Theta x := by
  apply max_le
  · exact theta_lower_ray (by norm_num) hx theta1_lower
  · exact theta_lower_ray (by norm_num) hx theta2_lower

theorem theta_le_upperEnvelope {x : ℝ} (hx : 0 < x) : e8Theta x ≤ upperEnvelope x :=
  theta_upper_ray (by norm_num) hx theta3_upper

theorem lowerEnvelope_ge_first {x : ℝ} (hx : 3175 / 29184 ≤ x) :
    (121 / 100 : ℝ) ≤ lowerEnvelope x := by
  have hr : (1 : ℝ) ≤ x / (3175 / 29184) :=
    (le_div_iff₀ (by norm_num)).mpr (by simpa using hx)
  unfold lowerEnvelope
  rw [min_eq_left hr, mul_one]
  exact le_max_left _ _

theorem lowerEnvelope_ge_second {x : ℝ} (hx : 25 / 76 ≤ x) :
    (3 : ℝ) ≤ lowerEnvelope x := by
  have hr : (1 : ℝ) ≤ x / (25 / 76) :=
    (le_div_iff₀ (by norm_num)).mpr (by simpa using hx)
  unfold lowerEnvelope
  rw [min_eq_left hr, mul_one]
  exact le_max_right _ _

theorem upperEnvelope_le_base {x : ℝ} (hx : x ≤ 375 / 646) :
    upperEnvelope x ≤ 417 / 100 := by
  have hr : x / (375 / 646) ≤ (1 : ℝ) := (div_le_one (by norm_num)).mpr hx
  simp only [upperEnvelope, max_eq_left hr, mul_one, le_refl]

theorem upperEnvelope_le_599 {x : ℝ} (hx : x ≤ 5 / 6) :
    upperEnvelope x ≤ 599 / 100 := by
  have hm : upperEnvelope x ≤ upperEnvelope (5 / 6) := by
    unfold upperEnvelope
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le_max le_rfl (div_le_div_of_nonneg_right hx (by norm_num))
  exact hm.trans (by norm_num [upperEnvelope])

/-- An explicit rational envelope comparison, containing no slope function. -/
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

/-- Both previously closed anchor polyhedra lie in the new envelope region. -/
theorem anchorRegion_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hr : ZeroCapLeftStationaryAnchorRegion.closedRegion a e f c) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hV := upperEnvelope_le_base ((div_le_iff₀ hE).mpr hr.1)
  unfold closedRegion
  rcases hr.2 with hfirst | hsecond
  · have hU := lowerEnvelope_ge_first ((le_div_iff₀ hE).mpr hfirst.1)
    have hW := lowerEnvelope_ge_second (x := (1 - 2 * c) / (2 * f))
      ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hfirst.2]))
    linarith only [hU, hV, hW]
  · have hU := lowerEnvelope_ge_second ((le_div_iff₀ hE).mpr hsecond.1)
    have hW := lowerEnvelope_ge_first (x := (1 - 2 * c) / (2 * f))
      ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hsecond.2]))
    linarith only [hU, hV, hW]

/-- When both positive terms use the second lower anchor, the entire
normalized range V<=5/6 is excluded, beyond the old V<=375/646 face. -/
theorem high_pair_subset {a e f c : ℝ} (he : 0 < e) (hf : 0 < f)
    (hU : (25 / 76) * (e + f) ≤ c - a)
    (hW : (25 / 38) * f ≤ 1 - 2 * c)
    (hV : 1 - a - c ≤ (5 / 6) * (e + f)) : closedRegion a e f c := by
  have hE : 0 < e + f := add_pos he hf
  have hu := lowerEnvelope_ge_second ((le_div_iff₀ hE).mpr hU)
  have hw := lowerEnvelope_ge_second (x := (1 - 2 * c) / (2 * f))
    ((le_div_iff₀ (mul_pos two_pos hf)).mpr (by linarith only [hW]))
  have hv := upperEnvelope_le_599 ((div_le_iff₀ hE).mpr hV)
  unfold closedRegion
  linarith only [hu, hw, hv]

theorem no_stationary_high_pair {a e f c : ℝ}
    (hac : a < c) (hc : c < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hU : (25 / 76) * (e + f) ≤ c - a)
    (hW : (25 / 38) * f ≤ 1 - 2 * c)
    (hV : 1 - a - c ≤ (5 / 6) * (e + f)) :
    deriv (fun y => canonicalPureGap a y e f) c ≠ 0 :=
  no_stationary hac hc he hf (high_pair_subset he hf hU hW hV)

theorem residual_iff {a e f c : ℝ} : ¬closedRegion a e f c ↔
    lowerEnvelope ((c - a) / (e + f)) + lowerEnvelope ((1 - 2 * c) / (2 * f)) -
      upperEnvelope ((1 - a - c) / (e + f)) < 1 / 100 := by
  simp only [closedRegion, not_le]

#print axioms theta_lower_ray
#print axioms theta_upper_ray
#print axioms lowerEnvelope_le_theta
#print axioms theta_le_upperEnvelope
#print axioms upperEnvelope_le_599
#print axioms derivative_margin
#print axioms no_stationary
#print axioms anchorRegion_subset
#print axioms high_pair_subset
#print axioms no_stationary_high_pair
#print axioms residual_iff

end GeneralCK.ZeroCapLeftStationaryRayEnvelope

namespace GeneralCK

def LeftStationaryOutsideRayEnvelopeOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryRayEnvelope.closedRegion (entropyInverse e) e f c →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideRayEnvelope (h : LeftStationaryOutsideRayEnvelopeOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hr : ZeroCapLeftStationaryRayEnvelope.closedRegion (entropyInverse e) e f c
  · have hac := (entropyInverse_mono he.le hf.le hef.le).trans_lt hfc
    exact False.elim (ZeroCapLeftStationaryRayEnvelope.no_stationary
      hac hc he (he.trans hef) hr hstation)
  · exact h e f c he hef hf hfc hc hstation hr

theorem leftStationary_outsideAnchorRegion_of_rayEnvelope
    (h : LeftStationaryOutsideRayEnvelopeOwner) : LeftStationaryOutsideAnchorRegionOwner := by
  intro e f c he hef hf hfc hc hstation _houtside
  exact leftStationary_of_outsideRayEnvelope h e f c he hef hf hfc hc hstation

theorem leftStationary_outsideAnchorRegion_iff_rayEnvelope :
    LeftStationaryOutsideAnchorRegionOwner ↔ LeftStationaryOutsideRayEnvelopeOwner := by
  constructor
  · intro h e f c he hef hf hfc hc hstation _houtside
    exact leftStationary_of_outsideAnchorRegion h e f c he hef hf hfc hc hstation
  · exact leftStationary_outsideAnchorRegion_of_rayEnvelope

#print axioms leftStationary_of_outsideRayEnvelope
#print axioms leftStationary_outsideAnchorRegion_of_rayEnvelope
#print axioms leftStationary_outsideAnchorRegion_iff_rayEnvelope

end GeneralCK

end


