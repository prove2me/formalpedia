-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryCompactReduction
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryCompactReduction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:18:24.918479+00:00
-- url     : https://prove2.me/theorems/aaebe184-bd42-4783-a748-39ef16134ef1
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryCompactReduction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryCompactReduction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryCompactReduction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryCompactReduction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryCompactReduction.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryRatioExclusion

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryCompactReduction =====
section

/-! The normalized residual has a genuine unbounded low-entropy tail.
An entropy floor gives a compact box, with an explicit separate tail owner. -/

namespace GeneralCK.ZeroCapLeftStationaryCompactReduction

open Set ZeroCapLeftStationaryHighRangeEnvelope ZeroCapLeftStationaryRatioExclusion

theorem lowerEnvelope_le_cap (x : ℝ) : lowerEnvelope x ≤ 89 / 20 := by
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (x / (3175 / 29184)))
    (by norm_num : (0 : ℝ) ≤ 121 / 100)
  have h2 := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (x / (25 / 76)))
    (by norm_num : (0 : ℝ) ≤ 3)
  have h3 := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (x / (7 / 10)))
    (by norm_num : (0 : ℝ) ≤ 89 / 20)
  unfold lowerEnvelope ZeroCapLeftStationaryRayEnvelope.lowerEnvelope
  exact max_le (max_le (by linarith only [h1]) (by linarith only [h2])) (by linarith only [h3])

theorem linear_le_upperEnvelope {x : ℝ} (hx : 0 ≤ x) :
    (118 / 25) * x ≤ upperEnvelope x := by
  unfold upperEnvelope ZeroCapLeftStationaryLowRangeEnvelope.upperEnvelope
    ZeroCapLeftStationaryRayEnvelope.upperEnvelope
  apply le_min
  · apply le_min
    · calc
        (118 / 25) * x ≤ (417 / 100) * (x / (375 / 646)) := by nlinarith only [hx]
        _ ≤ (417 / 100) * max 1 (x / (375 / 646)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    · apply le_min
      · calc
          (118 / 25) * x ≤ (193 / 100) * (x / (9 / 50)) := by nlinarith only [hx]
          _ ≤ (193 / 100) * max 1 (x / (9 / 50)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
      · calc
          (118 / 25) * x ≤ (29 / 10) * (x / (3 / 10)) := by nlinarith only [hx]
          _ ≤ (29 / 10) * max 1 (x / (3 / 10)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  · calc
      (118 / 25) * x = (59 / 10) * (x / (5 / 4)) := by ring
      _ ≤ (59 / 10) * max 1 (x / (5 / 4)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

/-- Both rational residual inequalities hold on an unbounded cone.
This statement does not assume or assert stationarity. -/
theorem residual_on_large_cone {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 2 ≤ v) (hgap : 1 ≤ v - u) :
    lowerEnvelope u + lowerEnvelope w - upperEnvelope v ≤ 0 ∧
      lowerEnvelope w * u - (v - u) * upperEnvelope u ≤ 0 := by
  constructor
  · have hv0 : 0 ≤ v := by linarith
    nlinarith only [lowerEnvelope_le_cap u, lowerEnvelope_le_cap w,
      linear_le_upperEnvelope hv0, hv]
  · have hprod := mul_le_mul_of_nonneg_left (linear_le_upperEnvelope hu)
      (show 0 ≤ v - u by linarith)
    have hscale := mul_le_mul_of_nonneg_right hgap
      (show 0 ≤ (118 / 25 : ℝ) * u by positivity)
    have hlow := mul_le_mul_of_nonneg_right (lowerEnvelope_le_cap w) hu
    nlinarith only [hprod, hscale, hlow, hu]

theorem inverse_le_eighth_of_small_entropy {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 16) :
    0 ≤ entropyInverse h ∧ entropyInverse h ≤ 1 / 8 := by
  have hH : h ≤ H (1 / 8) := by
    linarith only [hh', ZeroCapLeftStationaryHighAnchors.entropy_eighth_lower]
  have hm := entropyInverse_mono hh (H_le_one (1 / 8)) hH
  rw [entropyInverse_H_lower (by norm_num) (by norm_num)] at hm
  exact ⟨(entropyInverse_spec hh (by linarith)).1, hm⟩

/-- An actual entropy-inverse family remains in the rational residual,
with all three coordinates bounded below by a quantity diverging as f->0.
No stationarity claim is made about these points. -/
theorem physical_tail_family {f : ℝ} (hf : 0 < f) (hf' : f ≤ 1 / 16) :
    entropyInverse f < 1 / 4 ∧
    ¬ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse (f / 2)) (f / 2) f (1 / 4) ∧
    1 / (12 * f) ≤ ((1 / 4) - entropyInverse (f / 2)) / (f / 2 + f) ∧
    1 / (12 * f) ≤ (1 - entropyInverse (f / 2) - (1 / 4)) / (f / 2 + f) ∧
    1 / (12 * f) ≤ (1 - 2 * (1 / 4)) / (2 * f) := by
  let a := entropyInverse (f / 2)
  let U := ((1 / 4) - a) / (f / 2 + f)
  let V := (1 - a - (1 / 4)) / (f / 2 + f)
  let W := (1 - 2 * (1 / 4)) / (2 * f)
  have ha : 0 ≤ a ∧ a ≤ 1 / 8 := inverse_le_eighth_of_small_entropy (by positivity) (by linarith)
  have hb := inverse_le_eighth_of_small_entropy hf.le hf'
  have hE : 0 < f / 2 + f := by positivity
  have hU : 0 ≤ U := div_nonneg (by linarith) hE.le
  have hV : 2 ≤ V := (le_div_iff₀ hE).mpr (by linarith)
  have hgap : 1 ≤ V - U := by
    have hid : V - U = (1 / 2) / (f / 2 + f) := by dsimp [U, V]; ring
    rw [hid]
    apply (le_div_iff₀ hE).mpr
    linarith
  have hres := residual_on_large_cone (w := W) hU hV hgap
  have hlowU : 1 / (12 * f) ≤ U := by
    apply (div_le_div_iff₀ (by positivity : 0 < 12 * f) hE).mpr
    have hm := mul_le_mul_of_nonneg_right ha.2 (show 0 ≤ 12 * f by positivity)
    nlinarith only [hm]
  have hlowV : 1 / (12 * f) ≤ V := hlowU.trans (by linarith only [hgap])
  have hlowW : 1 / (12 * f) ≤ W := by
    apply (div_le_div_iff₀ (by positivity : 0 < 12 * f) (by positivity : 0 < 2 * f)).mpr
    nlinarith only [hf]
  refine ⟨by linarith [hb.2], ?_, hlowU, hlowV, hlowW⟩
  apply ZeroCapLeftStationaryRatioExclusion.residual_iff.mpr
  exact hres

theorem physical_residual_unbounded (M : ℝ) (hM : 0 ≤ M) :
    ∃ e f : ℝ, 0 < e ∧ e < f ∧ f < 1 ∧ entropyInverse f < 1 / 4 ∧
      ¬ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse e) e f (1 / 4) ∧
      M < ((1 / 4) - entropyInverse e) / (e + f) ∧
      M < (1 - entropyInverse e - (1 / 4)) / (e + f) ∧
      M < (1 - 2 * (1 / 4)) / (2 * f) := by
  let f : ℝ := 1 / (16 * (M + 1))
  have hd : 0 < 16 * (M + 1) := by positivity
  have hf : 0 < f := div_pos one_pos hd
  have hf' : f ≤ 1 / 16 := (div_le_iff₀ hd).mpr (by nlinarith only [hM])
  have heq : f * (16 * (M + 1)) = 1 := by dsimp [f]; field_simp
  have hMf : M < 1 / (12 * f) := by
    apply (lt_div_iff₀ (by positivity : 0 < 12 * f)).mpr
    nlinarith only [heq, hf, mul_nonneg hf.le hM]
  obtain ⟨hb, hr, hU, hV, hW⟩ := physical_tail_family hf hf'
  exact ⟨f / 2, f, by positivity, by linarith, by linarith, hb, hr,
    hMf.trans_le hU, hMf.trans_le hV, hMf.trans_le hW⟩

noncomputable def normalizedPoint (a e f c : ℝ) : ℝ × ℝ × ℝ :=
  ((c - a) / (e + f), (1 - a - c) / (e + f), (1 - 2 * c) / (2 * f))

def compactBox : Set (ℝ × ℝ × ℝ) :=
  Icc 0 8 ×ˢ (Icc 0 16 ×ˢ Icc 0 8)

theorem compactBox_isCompact : IsCompact compactBox :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem normalizedPoint_mem_compactBox {a e f c : ℝ}
    (ha : 0 ≤ a) (hac : a < c) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 1 / 16 ≤ f) : normalizedPoint a e f c ∈ compactBox := by
  have hfpos : 0 < f := by linarith
  have hE : 0 < e + f := add_pos he hfpos
  have hU : 0 ≤ (c - a) / (e + f) := div_nonneg (by linarith) hE.le
  have hV : 0 ≤ (1 - a - c) / (e + f) := div_nonneg (by linarith) hE.le
  have hW : 0 ≤ (1 - 2 * c) / (2 * f) := div_nonneg (by linarith) (by positivity)
  have hUhi : (c - a) / (e + f) ≤ 8 := (div_le_iff₀ hE).mpr (by linarith)
  have hVhi : (1 - a - c) / (e + f) ≤ 16 := (div_le_iff₀ hE).mpr (by linarith)
  have hWhi : (1 - 2 * c) / (2 * f) ≤ 8 :=
    (div_le_iff₀ (mul_pos two_pos hfpos)).mpr (by linarith)
  exact ⟨⟨hU, hUhi⟩, ⟨hV, hVhi⟩, ⟨hW, hWhi⟩⟩

#print axioms lowerEnvelope_le_cap
#print axioms linear_le_upperEnvelope
#print axioms residual_on_large_cone
#print axioms physical_tail_family
#print axioms physical_residual_unbounded
#print axioms compactBox_isCompact
#print axioms normalizedPoint_mem_compactBox

end GeneralCK.ZeroCapLeftStationaryCompactReduction

namespace GeneralCK

def LeftStationaryCompactBoxOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse e) e f c →
    1 / 16 ≤ f →
    ZeroCapLeftStationaryCompactReduction.normalizedPoint (entropyInverse e) e f c ∈
      ZeroCapLeftStationaryCompactReduction.compactBox →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

def LeftStationaryLowEntropyTailOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ZeroCapLeftStationaryRatioExclusion.closedRegion (entropyInverse e) e f c →
    f < 1 / 16 → 0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_outsideRatioExclusion_of_compact_and_tail
    (hcompact : LeftStationaryCompactBoxOwner) (htail : LeftStationaryLowEntropyTailOwner) :
    LeftStationaryOutsideRatioExclusionOwner := by
  intro e f c he hef hf hfc hc hstation hr
  by_cases hfloor : 1 / 16 ≤ f
  · have ha := (entropyInverse_spec he.le (hef.le.trans hf.le)).1
    have hac := (entropyInverse_mono he.le hf.le hef.le).trans_lt hfc
    exact hcompact e f c he hef hf hfc hc hstation hr hfloor
      (ZeroCapLeftStationaryCompactReduction.normalizedPoint_mem_compactBox ha hac hc he hfloor)
  · exact htail e f c he hef hf hfc hc hstation hr (lt_of_not_ge hfloor)

theorem leftStationary_outsideRatioExclusion_iff_compact_and_tail :
    LeftStationaryOutsideRatioExclusionOwner ↔
      LeftStationaryCompactBoxOwner ∧ LeftStationaryLowEntropyTailOwner := by
  constructor
  · intro h
    constructor
    · intro e f c he hef hf hfc hc hstation hr _hfloor _hbox
      exact h e f c he hef hf hfc hc hstation hr
    · intro e f c he hef hf hfc hc hstation hr _htail
      exact h e f c he hef hf hfc hc hstation hr
  · rintro ⟨hcompact, htail⟩
    exact leftStationary_outsideRatioExclusion_of_compact_and_tail hcompact htail

#print axioms leftStationary_outsideRatioExclusion_of_compact_and_tail
#print axioms leftStationary_outsideRatioExclusion_iff_compact_and_tail

end GeneralCK

end


