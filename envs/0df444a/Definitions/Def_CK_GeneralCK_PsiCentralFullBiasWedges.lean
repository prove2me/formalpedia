-- Prove2me | Definitions.Def_CK_GeneralCK_PsiCentralFullBiasWedges
-- name    : CK_GeneralCK_PsiCentralFullBiasWedges
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:06:39.019821+00:00
-- url     : https://prove2.me/theorems/96f3ad53-cc6d-4e73-9158-18873e7fa02c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiCentralFullBiasWedges` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiCentralFullBiasWedges` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiCentralFullBiasWedges` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiCentralFullBiasWedges (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiCentralFullBiasWedges.lean)

import Definitions.Def_CK_GeneralCK_PsiCentralTwentyFourWedge

-- ===== source module GeneralCK.PsiCentralFullBiasWedges =====
section

/-!
# Retained-child wedges through the full central bias range

The split loss bound extends through bias two fifths. This closes both the
ratio-24 wedge and the ratio-16 wedge above entropy 1/40, with actual law
cost and both child profiles retained.
-/

namespace GeneralCK.PsiCentralFullBiasWedges

open Set PsiChildEntropyCoupling PsiSignedSplit

theorem capacity_quadratic_thirteen_sixteenths {z : ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ 13 / 16) : capacity z ≤ (691 / 1044) * z ^ 2 := by
  have hz1 : z < 1 := by linarith
  rw [capacity_eq_Cn (by rw [abs_of_nonneg hz]; exact hz1)]
  have hs : z ^ 2 ≤ 169 / 256 := by nlinarith
  have hn : 0 < 1 - z ^ 2 := by linarith
  have hf : z ^ 2 / (12 * (1 - z ^ 2)) ≤ (169 / 1044 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (1 - z ^ 2))).mpr
    nlinarith only [hs]
  have h := LowInformation.Cn_upper_sharp hz hz1
  have hh := mul_le_mul_of_nonneg_left hf (sq_nonneg z)
  have he : z ^ 2 * (z ^ 2 / (12 * (1 - z ^ 2))) = z ^ 4 / (12 * (1 - z ^ 2)) := by ring
  rw [he] at hh
  linarith

theorem split_loss {c q : ℝ} (hc : 8 / 15 ≤ c)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 5) :
    2 * c * capacity ((13 * q / 6) / (2 * c)) ≤ 3 * q ^ 2 := by
  have hk : |13 * q / 6| < 2 * (8 / 15 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have h := loss_antitone (c₁ := (8 / 15 : ℝ)) (c₂ := c)
    (k := 13 * q / 6) (by norm_num) hc hk
  rw [show (13 * q / 6) / (2 * (8 / 15 : ℝ)) = 65 * q / 32 by ring] at h
  have hb := capacity_quadratic_thirteen_sixteenths
    (z := 65 * q / 32) (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

/-- A reusable conversion of a logarithmic chord into parent gain. -/
theorem parent_gain_of_chord {E q c : ℝ} (hE : 0 < E) (hEu : E ≤ 1 / 32)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 5)
    (hchord : c * (q ^ 2 / E) ≤ Real.log (1 + (5 / 7) * (q ^ 2 / E)) / Real.log 2) :
    (c + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  let C := 1 - H ((1 - q) / 2)
  let R := q ^ 2 / E
  have hC : 0 ≤ C := sub_nonneg.mpr (H_le_one _)
  have hL : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Certificates.PilotData.log_two.2
    norm_num at h
    linarith
  have hClower := SmallMean.Cn_ge_half_sq hq (show q ≤ 1 by linarith)
  change q ^ 2 / 2 ≤ Real.log 2 * C at hClower
  have hClow : (5 / 7) * q ^ 2 ≤ C := by
    have hm := mul_le_mul_of_nonneg_right hL hC
    nlinarith only [hm, hClower]
  have harg : (5 / 7) * R ≤ C / E := by
    have hm := div_le_div_of_nonneg_right hClow hE.le
    convert! hm using 1 <;> dsimp [R] <;> ring
  have hphys : E + C ≤ 1 := by
    have hh := PsiParentPhiFloor.entropy_chord
      (show 0 ≤ (1 - q) / 2 by linarith) (show (1 - q) / 2 ≤ 1 / 2 by linarith)
    dsimp [C]
    linarith
  have hg := eta_increment_ge_linear_log hE hC hphys
  have hm : Real.log (1 + (5 / 7) * R) ≤ Real.log (1 + C / E) :=
    Real.log_le_log (by positivity) (by linarith only [harg])
  have hlog := div_le_div_of_nonneg_right hm log_two_pos.le
  have hER : E * R = q ^ 2 := by dsimp [R]; field_simp
  change c * R ≤ Real.log (1 + (5 / 7) * R) / Real.log 2 at hchord
  change (c + (10 / 7) * E) * R ≤ eta E - eta (E + C)
  nlinarith only [hchord, hlog, hg, hClow, hER]

theorem parent_gain_ratio28 {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 1 / 48)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 5) (hqE : q ≤ 28 * E) :
    (4 / 15 + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  apply parent_gain_of_chord hE (by linarith) hq hqu
  apply PsiCentralTwentyFourWedge.logarithmic_chord (by positivity)
  apply (div_le_iff₀ hE).mpr
  have h1 := mul_nonneg hq (sub_nonneg.mpr hqE)
  have h2 := mul_nonneg hE.le (sub_nonneg.mpr hqu)
  nlinarith only [h1, h2, hE]

theorem parent_gain_entropy_band {E q : ℝ}
    (hEl : 1 / 40 ≤ E) (hEu : E ≤ 1 / 32) (hq : 0 ≤ q) (hqu : q ≤ 2 / 5) :
    (3 / 8 + (10 / 7) * E) * (q ^ 2 / E) ≤
      eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hE : 0 < E := by linarith
  apply parent_gain_of_chord hE hEu hq hqu
  apply PsiCentralSixteenWedge.logarithmic_chord (by positivity)
  apply (div_le_iff₀ hE).mpr
  nlinarith only [mul_nonneg hq (sub_nonneg.mpr hqu), hqu, hEl]

theorem retained_child_margin {d q E t : ℝ}
    (hE : 0 < E) (hdu : d ≤ 1 / 2)
    (hq : 0 ≤ q) (hqu : q ≤ 2 / 5) (hqd : q ≤ d) (hqE : q ≤ 28 * E)
    (hregion : 24 * E ≤ d ∨ (1 / 40 ≤ E ∧ 16 * E ≤ d)) (ht : |t| < 1) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage d q E t +
      (1 / 100) * (q ^ 2 / E) ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  have hEu : E ≤ 1 / 32 := by rcases hregion with h | h <;> linarith
  have hd : 0 ≤ d := hq.trans hqd
  have hc := PsiCentralTwentyFourWedge.endpoint_coefficient hd hdu
  have hk : |13 * q / 6| < 2 * endpointCoefficient d := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 13 * q / 6)]
    linarith
  have hloss := split_loss hc hq hqu
  obtain ⟨hA, hAu⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hq hqd
  have hs := PsiQuarterBias.signed_split_of_loss (by linarith : 0 < endpointCoefficient d)
    hq (by norm_num : (0 : ℝ) ≤ 3) hk hloss hE hA hAu ht
  have hdec := retained_child_decomposition (C := 1 - H ((1 - q) / 2))
    hq hqd hE (by linarith) ht
  rcases hregion with h24 | h16
  · have hEu24 : E ≤ 1 / 48 := by linarith
    have hg := parent_gain_ratio28 hE hEu24 hq hqu hqE
    have hr := PsiCentralTwentyFourWedge.radial_average_loss hE h24 q
    rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
      abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
    have hr' : radialLoss d q E ≤ (5 / 24) * (q ^ 2 / E) := by
      unfold radialLoss
      linarith only [hr]
    have hbudget : (5 / 24 + 3 * E + 1 / 100) * (q ^ 2 / E) ≤
        (4 / 15 + (10 / 7) * E) * (q ^ 2 / E) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have he : (5 / 24 + 3 * E + 1 / 100) * (q ^ 2 / E) =
        (5 / 24 + 1 / 100) * (q ^ 2 / E) + 3 * q ^ 2 := by
      field_simp
      ring
    rw [he] at hbudget
    linarith only [hg, hbudget, hr', hs, hdec]
  · have hg := parent_gain_entropy_band h16.1 hEu hq hqu
    have hr := PsiCentralSixteenWedge.radial_average_loss hE h16.2 q
    rw [abs_of_nonneg (show 0 ≤ d - q by linarith),
      abs_of_nonneg (show 0 ≤ d + q by linarith)] at hr
    have hr' : radialLoss d q E ≤ (5 / 16) * (q ^ 2 / E) := by
      unfold radialLoss
      linarith only [hr]
    have hbudget : (5 / 16 + 3 * E + 1 / 100) * (q ^ 2 / E) ≤
        (3 / 8 + (10 / 7) * E) * (q ^ 2 / E) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have he : (5 / 16 + 3 * E + 1 / 100) * (q ^ 2 / E) =
        (5 / 16 + 1 / 100) * (q ^ 2 / E) + 3 * q ^ 2 := by
      field_simp
      ring
    rw [he] at hbudget
    linarith only [hg, hbudget, hr', hs, hdec]

/-- Actual-law closure on the union of the full-bias wedges. -/
theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hdu : μ.b - μ.a ≤ 1 / 2) (hq : 1 - μ.a - μ.b ≤ 2 / 5)
    (hregion : 24 * μ.meanEntropy ≤ μ.b - μ.a ∨
      (1 / 40 ≤ μ.meanEntropy ∧ 16 * μ.meanEntropy ≤ μ.b - μ.a))
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a := by linarith
  have hqE := (PsiThreeTenthsTail28.law_active_bias_lt_twenty_eight_entropy μ hq hactive).le
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hm := retained_child_margin (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
    (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f))
    hE hdu hq0 hq hqd hqE hregion ht
  have hchild := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd (by rwa [hmean])
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  rw [hca, hcb, hce, hcf, hmean] at hchild
  rw [hmean] at hm
  have hd8 : 8 * μ.meanEntropy ≤ μ.b - μ.a := by
    rcases hregion with h | h <;> linarith
  have hcost := PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd8
  change μ.gap ≤ eta (μ.meanEntropy + (1 - H μ.midpoint)) -
    childAverage (μ.b - μ.a) (1 - μ.a - μ.b) μ.meanEntropy
      ((μ.e - μ.f) / (μ.e + μ.f)) at hchild
  linarith only [hm, hchild, hcost]

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hb : 1 / 2 ≤ μ.b)
    (hdu : μ.b - μ.a ≤ 1 / 2) (hq : 1 - μ.a - μ.b ≤ 2 / 5)
    (hregion : 24 * μ.meanEntropy ≤ μ.b - μ.a ∨
      (1 / 40 ≤ μ.meanEntropy ∧ 16 * μ.meanEntropy ≤ μ.b - μ.a))
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm := law_gap_margin μ hsum hb hdu hq hregion hactive
  have hn : 0 ≤ (1 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  linarith only [hm, hn]

/-- Exact complement of the union within the preceding central owner. -/
def centralRegion (a b E : ℝ) : Prop :=
  PsiCentralTwentyFourWedge.centralRegion a b E ∧
    (1 - a - b < 3 / 10 ∨ (b - a < 24 * E ∧ (E < 1 / 40 ∨ b - a < 16 * E)))

def CentralOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    centralRegion μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

theorem toTwentyFourCentralOwner (h : CentralOwner) :
    PsiCentralTwentyFourWedge.CentralOwner := by
  intro k μ hab hregion hactive
  by_cases hw : 3 / 10 ≤ 1 - μ.a - μ.b ∧
      (24 * μ.meanEntropy ≤ μ.b - μ.a ∨
        (1 / 40 ≤ μ.meanEntropy ∧ 16 * μ.meanEntropy ≤ μ.b - μ.a))
  · have h28 : PsiThreeTenthsTail28.centralRegion μ.a μ.b μ.meanEntropy := hregion.1.1
    have hbase : PsiCentralAnalytic.centralRegion μ.a μ.b μ.meanEntropy :=
      h28.1.1.1.1.1.1.1.1.1.1
    exact law_gap_le_cost μ hbase.1.le hbase.2.1
      (by linarith [hbase.2.2.1, hw.1])
      (by linarith [hbase.2.2.1, hbase.2.1]) hw.2 hactive.le
  · apply h k μ hab ⟨hregion, ?_⟩ hactive
    by_contra hn
    push Not at hn
    apply hw
    refine ⟨hn.1, ?_⟩
    by_cases hd24 : 24 * μ.meanEntropy ≤ μ.b - μ.a
    · exact Or.inl hd24
    · exact Or.inr (hn.2 (lt_of_not_ge hd24))

#print axioms capacity_quadratic_thirteen_sixteenths
#print axioms split_loss
#print axioms parent_gain_of_chord
#print axioms parent_gain_ratio28
#print axioms parent_gain_entropy_band
#print axioms retained_child_margin
#print axioms law_gap_margin
#print axioms law_gap_le_cost
#print axioms toTwentyFourCentralOwner

end GeneralCK.PsiCentralFullBiasWedges

end


