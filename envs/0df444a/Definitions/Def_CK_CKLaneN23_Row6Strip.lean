-- Prove2me | Definitions.Def_CK_CKLaneN23_Row6Strip
-- name    : CK_CKLaneN23_Row6Strip
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:57:33.06299+00:00
-- url     : https://prove2.me/theorems/d9568825-102a-4cc8-bba5-5dd190faac8d
-- title:
--   Courtade–Kumar proof module `CKLaneN23.Row6Strip` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.Row6Strip` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.Row6Strip` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.Row6Strip (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/Row6Strip.lean)

import Definitions.Def_CK_CKLaneN23_Row5HighBias
import Definitions.Def_CK_GeneralCK_PsiLowEntropyRedesign
import Definitions.Def_CK_GeneralCK_PsiFourRatioBridge
import Definitions.Def_CK_GeneralCK_MixedDerivative

-- ===== source module CKLaneN23.Row6Strip =====
section

/-!
# Lane N23 — row 6 `NoSepA_StripRem` (NO_SEPARATION §4, the low-entropy strip)

Row 6 of `CKLaneN23.sameSideHalf_of_certificate_rows`: central means, `d ≤ 1/50`,
`4E ≤ d < 8E`, `q ≤ 8E`, `E > 10^-6`, strict psi-activity `⟹ gap ≤ cost`
(so `E ≤ d/4 ≤ 1/200`).

Archived argument (NO_SEPARATION §4): in the psi-parent branch retain `phi` at both children;
`F(d,E) - R_B ≥ [η(E) - η(E+C(q))] - [radial second difference] - [entropy-split loss]`, with
the split loss controlled by the semiconvexity of `Φ(z,·)` (from the GLOBAL_MIXED bound
`z F_zz ≤ 13/6`), the radial Jensen loss by `f'(4)/8 < 81/100`, and the parent gain by
`η(E) - η(E+C) ≥ C/(L(E+C))` with `C(q) ≥ q²/(2L)`. Then `ζ ≥ F(d,E)`.

Reused compiled F-C theorems (no numerical or regional hypotheses):
* `global_mixed_derivative_bound` (`z F_zz ≤ 13/6`, 105 closed rational intervals + analytic
  tails), through `PsiEntropySlopeVariation` / `PsiLowEntropyRedesign.child_slope_bounds`
  (`0 ≤ Φ_h(c+δ) - Φ_h(c-δ) ≤ 13δ/(3E)`) and `PsiChildEntropyCoupling.child_average_lower`
  (compensated convexity, `compensation r = 1/L - 13r/6`);
* `PsiSignedSplit` (exact minimum of the signed split objective);
* `F_average_difference_le`, `antitoneOn_F_radius_ratio`, `deriv_F_radius_slope`,
  `hasDerivAt_radialSlope` (radial Jensen);
* `eta_increment_ge_rational`, `SmallMean.Cn_ge_half_sq` (parent gain);
* `PsiRetainedChildBridge` (retained child phi), `PsiEndpointPlane.law_radial_lower`.

New here: `radialSlope(v(4)) ≤ 162/25` (so the radial loss is at most `(81/100) q²/E`, the
archived constant), the parent gain `≥ (21/25) q²/E` on `E ≤ 1/200`, the split loss
`≥ -2δ²` for `δ ≤ 1/25`, and the final comparison `21/25 - 81/100 - 1/100 > 0`.
-/

namespace CKLaneN23.Row6

open GeneralCK Set PsiChildEntropyCoupling PsiSignedSplit PsiExtendedEntropyCurvature

/-! ## The radial slope at ratio four -/

theorem two_kap_ge_sq {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    (1 - 2 * v) ^ 2 ≤ 2 * Certificates.Mixed.kap v := by
  unfold Certificates.Mixed.kap
  have hp : 0 < v * (1 - v) := mul_pos hv (by linarith)
  have hq : v * (1 - v) ≤ 1 / 4 := by nlinarith [sq_nonneg (v - 1 / 2)]
  have hl : Real.log (v * (1 - v)) ≤ Real.log (1 / 4) := Real.log_le_log hp hq
  have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Row5.log_two_bounds.1]
  have hsq : (1 - 2 * v) ^ 2 ≤ 1 := by nlinarith
  nlinarith

theorem radialSlope_antitoneOn : AntitoneOn radialSlope (Ioo 0 (1 / 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 (1 / 2))
  · intro v hv
    exact (hasDerivAt_radialSlope hv.1 hv.2).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioo] at hv
    exact (hasDerivAt_radialSlope hv.1 hv.2).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Ioo] at hv
    rw [(hasDerivAt_radialSlope hv.1 hv.2).deriv]
    have hhn : 0 ≤ Certificates.Mixed.hn v := by
      rw [Certificates.Mixed.hn_eq_H_mul_log]
      exact mul_nonneg (H_nonneg hv.1.le (by linarith [hv.2])) log_two_pos.le
    have hk := two_kap_ge_sq hv.1 hv.2
    have hnum : -Certificates.Mixed.hn v *
        (2 * Certificates.Mixed.kap v - (1 - 2 * v) ^ 2) ≤ 0 := by
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hhn (by linarith))
    have hden : 0 ≤ 4 * Real.log 2 * v ^ 2 * (1 - v) ^ 2 * Certificates.Mixed.kap v ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) log_two_pos.le)
        (sq_nonneg v)) (sq_nonneg (1 - v))) (sq_nonneg _)
    exact div_nonpos_of_nonpos_of_nonneg hnum hden

theorem log_five_thirds : (102165124753 / 200000000000 : ℝ) ≤ Real.log (5 / 3) ∧
    Real.log (5 / 3) ≤ (510825623767 / 1000000000000 : ℝ) := by
  have h := Certificates.checkLog_sound (w := (1 / 4 : ℚ)) (n := 10)
    (lo := (102165124753 / 200000000000 : ℚ)) (hi := (510825623767 / 1000000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_eighty_seventyseven : (1911060641 / 50000000000 : ℝ) ≤ Real.log (80 / 77) ∧
    Real.log (80 / 77) ≤ (38221212821 / 1000000000000 : ℝ) := by
  have h := Certificates.checkLog_sound (w := (3 / 157 : ℚ)) (n := 5)
    (lo := (1911060641 / 50000000000 : ℚ)) (hi := (38221212821 / 1000000000000 : ℚ))
    (by norm_num [Certificates.checkLog, Certificates.logLower, Certificates.logUpper,
      Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_eighty_thirds : Real.log (80 / 3) = 4 * Real.log 2 + Real.log (5 / 3) := by
  rw [show (80 / 3 : ℝ) = (2 : ℝ) ^ (4 : ℕ) * (5 / 3) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  ring

theorem binEntropy_three_eightieths :
    H (3 / 80) * Real.log 2 = (3 / 80) * Real.log (80 / 3) + (77 / 80) * Real.log (80 / 77) := by
  rw [H, div_mul_cancel₀ _ log_two_pos.ne', Real.binEntropy]
  norm_num

/-- Contact bracket at ratio four: `3/80 ≤ v(4)`. -/
theorem contact_four_lower : (3 / 80 : ℝ) ≤ radialContact 4 1 := by
  rw [le_radialContact_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have he := binEntropy_three_eightieths
  have hX := log_eighty_thirds
  have h53 := log_five_thirds
  have h77 := log_eighty_seventyseven
  have hL := Row5.log_two_bounds
  have hLpos := log_two_pos
  -- H(3/80) * L ≤ (37/160) * L
  have hb : H (3 / 80) * Real.log 2 ≤ (37 / 160) * Real.log 2 := by
    rw [he, hX]
    nlinarith [h53.2, h77.2, hL.1, hL.2]
  have hH : H (3 / 80) ≤ 37 / 160 := le_of_mul_le_mul_right hb hLpos
  nlinarith

theorem radialSlope_three_eightieths : radialSlope (3 / 80) ≤ 162 / 25 := by
  have hX := log_eighty_thirds
  have h53 := log_five_thirds
  have h77 := log_eighty_seventyseven
  have hL := Row5.log_two_bounds
  have hLpos := log_two_pos
  have hXl : 4 * (34657359 / 50000000) + 102165124753 / 200000000000 ≤ Real.log (80 / 3) := by
    rw [hX]; linarith [hL.1, h53.1]
  have hXu : Real.log (80 / 3) ≤ 4 * (693147181 / 1000000000) + 510825623767 / 1000000000000 := by
    rw [hX]; linarith [hL.2, h53.2]
  have hJ : J (3 / 80) = (Real.log (80 / 3) - Real.log (80 / 77)) / Real.log 2 := by
    unfold J
    rw [← Real.log_div (show (80 / 3 : ℝ) ≠ 0 by norm_num) (show (80 / 77 : ℝ) ≠ 0 by norm_num)]
    norm_num
  have hhn : Certificates.Mixed.hn (3 / 80) =
      (3 / 80) * Real.log (80 / 3) + (77 / 80) * Real.log (80 / 77) := by
    rw [Certificates.Mixed.hn_eq_H_mul_log, binEntropy_three_eightieths]
  have hkap : Certificates.Mixed.kap (3 / 80) = (Real.log (80 / 3) + Real.log (80 / 77)) / 2 := by
    unfold Certificates.Mixed.kap
    rw [← Real.log_mul (show (80 / 3 : ℝ) ≠ 0 by norm_num) (show (80 / 77 : ℝ) ≠ 0 by norm_num),
      show (3 / 80 : ℝ) * (1 - 3 / 80) = ((80 / 3) * (80 / 77))⁻¹ by norm_num, Real.log_inv]
    ring
  unfold radialSlope
  rw [hJ, hhn, hkap]
  have hT1 : (Real.log (80 / 3) - Real.log (80 / 77)) / Real.log 2 ≤ 4682 / 1000 := by
    rw [div_le_iff₀ hLpos]
    linarith [h77.1, hL.1]
  have hS : 0 < Real.log (80 / 3) + Real.log (80 / 77) := by linarith [h77.1]
  have hDn : 0 < 2 * Real.log 2 * (3 / 80) * (1 - 3 / 80) *
      ((Real.log (80 / 3) + Real.log (80 / 77)) / 2) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hLpos) (by norm_num)) (by norm_num))
      (by linarith)
  have hLXY : (34657359 / 50000000) *
      (4 * (34657359 / 50000000) + 102165124753 / 200000000000 + 1911060641 / 50000000000) ≤
      Real.log 2 * (Real.log (80 / 3) + Real.log (80 / 77)) :=
    mul_le_mul hL.1 (by linarith [h77.1]) (by norm_num) hLpos.le
  have hT2 : (1 - 2 * (3 / 80 : ℝ)) *
      ((3 / 80) * Real.log (80 / 3) + (77 / 80) * Real.log (80 / 77)) /
      (2 * Real.log 2 * (3 / 80) * (1 - 3 / 80) *
        ((Real.log (80 / 3) + Real.log (80 / 77)) / 2)) ≤ 1782 / 1000 := by
    rw [div_le_iff₀ hDn]
    nlinarith [h77.2, hLXY]
  linarith

theorem radialSlope_contact_four : radialSlope (radialContact 4 1) ≤ 162 / 25 := by
  have hv := contact_four_lower
  have hpos := radialContact_pos (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 1)
  have hlt := radialContact_lt_half (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 1)
  have hm := radialSlope_antitoneOn ⟨by norm_num, by norm_num⟩ ⟨hpos, hlt⟩ hv
  exact hm.trans radialSlope_three_eightieths

/-- Radial Jensen constant: `f'(x)/(2x) ≤ 81/100` for `x ≥ 4` (archived `f'(4)/8 < 81/100`). -/
theorem radial_ratio_le_81 {x : ℝ} (hx : 4 ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ 81 / 100 := by
  have hm := antitoneOn_F_radius_ratio (by norm_num : (0 : ℝ) < 1)
    (show (4 : ℝ) ∈ Ioi 0 by norm_num) (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have he : deriv (fun r => F r 1) 4 / (2 * 4) ≤ 81 / 100 := by
    rw [deriv_F_radius_slope (by norm_num) (by norm_num)]
    have h := radialSlope_contact_four
    norm_num
    linarith
  exact hm.trans he

theorem radial_average_loss_81 {d E : ℝ} (hE : 0 < E) (hd : 4 * E ≤ d) (q : ℝ) :
    (F |d - q| E + F |d + q| E) / 2 - F d E ≤ (81 / 100) * (q ^ 2 / E) := by
  have hd0 : 0 < d := by linarith
  have hx : 4 ≤ d / E := (le_div_iff₀ hE).2 hd
  have hb := radial_ratio_le_81 hx
  have hh := F_average_difference_le hd0 hE q
  have heq : q ^ 2 / (2 * d) * deriv (fun r => F r E) d =
      (q ^ 2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd0 hE]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ q ^ 2 / E by positivity)
  rw [heq] at hh
  nlinarith only [hh, hp]

/-! ## Parent gain on `E ≤ 1/200` -/

theorem parent_gain_strip {E q : ℝ} (hE : 0 < E) (hEu : E ≤ 1 / 200) (hq : 0 ≤ q)
    (hqE : q ≤ 8 * E) :
    (21 / 25) * (q ^ 2 / E) ≤ eta E - eta (E + (1 - H ((1 - q) / 2))) := by
  have hL : 0 < Real.log 2 := log_two_pos
  have hLu := Row5.log_two_bounds.2
  have hq1 : q ≤ 1 := by linarith
  have hc : 0 ≤ 1 - H ((1 - q) / 2) := sub_nonneg.mpr (H_le_one _)
  have hcq : 1 - H ((1 - q) / 2) ≤ q ^ 2 := by
    have h := PsiSmallDistance.biasDeficit_le_sq (r := q) (by rw [abs_of_nonneg hq]; exact hq1)
    rwa [PsiSmallDistance.biasDeficit_eq] at h
  have hq2 : q ^ 2 ≤ 64 * E ^ 2 := by nlinarith
  have hE2 : E ^ 2 ≤ E / 200 := by nlinarith
  have hphys : E + (1 - H ((1 - q) / 2)) ≤ 1 := by nlinarith
  have hgain := eta_increment_ge_rational hE hc hphys
  have hc2L : q ^ 2 ≤ 2 * Real.log 2 * (1 - H ((1 - q) / 2)) := by
    have h := SmallMean.Cn_ge_half_sq hq hq1
    unfold SmallMean.Cn at h
    linarith
  have hkey : 42 * Real.log 2 ^ 2 * E + 21 * Real.log 2 * q ^ 2 ≤ 25 * E := by
    have h1 : Real.log 2 ^ 2 * E ≤ (693147181 / 1000000000) ^ 2 * E := by
      apply mul_le_mul_of_nonneg_right _ hE.le
      nlinarith
    have h2 : Real.log 2 * q ^ 2 ≤ (693147181 / 1000000000) * (64 * (E / 200)) := by
      have h3 : q ^ 2 ≤ 64 * (E / 200) := by linarith
      calc Real.log 2 * q ^ 2 ≤ (693147181 / 1000000000) * q ^ 2 :=
            mul_le_mul_of_nonneg_right hLu (sq_nonneg q)
        _ ≤ (693147181 / 1000000000) * (64 * (E / 200)) :=
            mul_le_mul_of_nonneg_left h3 (by norm_num)
    nlinarith
  have hbase : (21 / 25) * (q ^ 2 / E) ≤
      (1 - H ((1 - q) / 2)) / (Real.log 2 * (E + (1 - H ((1 - q) / 2)))) := by
    have hpos25 : 0 ≤ 25 * E - 21 * q ^ 2 * Real.log 2 := by nlinarith [sq_nonneg (Real.log 2)]
    have p1 := mul_le_mul_of_nonneg_right hc2L hpos25
    have p2 := mul_le_mul_of_nonneg_left hkey (sq_nonneg q)
    have hden : 0 < Real.log 2 * (E + (1 - H ((1 - q) / 2))) := mul_pos hL (by linarith)
    rw [show (21 / 25) * (q ^ 2 / E) = (21 * q ^ 2) / (25 * E) by ring,
      div_le_div_iff₀ (by linarith) hden]
    have key2 : 2 * Real.log 2 * (21 * q ^ 2 * (Real.log 2 * (E + (1 - H ((1 - q) / 2))))) ≤
        2 * Real.log 2 * ((1 - H ((1 - q) / 2)) * (25 * E)) := by
      nlinarith [p1, p2]
    exact le_of_mul_le_mul_left key2 (by positivity)
  linarith

/-! ## Signed entropy split, `δ ≤ 1/25` -/

theorem split_loss_le_two_sq {c δ : ℝ} (hc : 2 / 3 ≤ c) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 25) :
    2 * c * capacity ((13 * δ / 6) / (2 * c)) ≤ 2 * δ ^ 2 := by
  have hk : |13 * δ / 6| < 2 * (2 / 3 : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have h := loss_antitone (c₁ := (2 / 3 : ℝ)) (c₂ := c) (k := 13 * δ / 6) (by norm_num) hc hk
  have he : (13 * δ / 6) / (2 * (2 / 3 : ℝ)) = 13 * δ / 8 := by ring
  rw [he] at h
  have hb := capacity_small_quadratic (z := 13 * δ / 8) (by positivity) (by linarith)
  nlinarith [sq_nonneg δ]

theorem objective_ge_neg_two_sq {c δ t : ℝ} (hc : 2 / 3 ≤ c) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 25)
    (ht : |t| < 1) : -(2 * δ ^ 2) ≤ objective c (13 * δ / 6) t := by
  have hcpos : 0 < c := by linarith
  have hk : |13 * δ / 6| < 2 * c := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hz := (objective_minimum hcpos hk).1
  have h := objective_lower hcpos.le hz ht
  have he : 2 * c * ((13 * δ / 6) / (2 * c)) = 13 * δ / 6 :=
    mul_div_cancel₀ _ (by positivity : 2 * c ≠ 0)
  rw [he] at h
  linarith [split_loss_le_two_sq hc hδ hδ']

theorem signed_split_ge_neg_two_sq {c δ E A t : ℝ} (hc : 2 / 3 ≤ c) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 25) (hE : 0 < E) (hA : 0 ≤ A) (hA' : A ≤ 13 * δ / (3 * E))
    (ht : |t| < 1) :
    -(2 * δ ^ 2) ≤ c * barrier t + E * t * A / 2 + (13 * δ / 6) * (tilt t - t) := by
  by_cases ht0 : 0 ≤ t
  · have hb : 0 ≤ c * barrier t := mul_nonneg (by linarith) (barrier_nonneg ht)
    have hl : 0 ≤ E * t * A / 2 := by positivity
    have ht1 : t < 1 := (abs_lt.mp ht).2
    have hm : 0 ≤ (13 * δ / 6) * (tilt t - t) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (tilt_ge_self ht0 ht1))
    nlinarith [sq_nonneg δ]
  · have htneg : t ≤ 0 := le_of_not_ge ht0
    have hEA : E * A ≤ 13 * δ / 3 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 3 * E)).mp hA'
      nlinarith
    have hlin := mul_le_mul_of_nonpos_left hEA htneg
    have hobj := objective_ge_neg_two_sq (t := -t) hc hδ hδ'
      (by simpa only [abs_neg] using ht)
    unfold objective at hobj
    rw [barrier_neg, tilt_neg] at hobj
    nlinarith

theorem half_compensation_ge {r : ℝ} (hr : r ≤ 1 / 25) : 2 / 3 ≤ compensation r / 2 := by
  unfold compensation
  have hLu := Row5.log_two_bounds.2
  have hLpos := log_two_pos
  have h1 : (10 / 7 : ℝ) ≤ 1 / Real.log 2 := by
    rw [le_div_iff₀ hLpos]
    linarith
  linarith

/-! ## The strip margin, both orientations -/

theorem strip_margin_core {d q E t c₀ δ : ℝ} (hE : 0 < E) (hEu : E ≤ 1 / 200)
    (hd4 : 4 * E ≤ d) (hq : 0 ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1) (hδ : 0 ≤ δ)
    (hδc : δ ≤ c₀) (hc₀ : c₀ ≤ 1 / 25) (hδq : δ ≤ q)
    (hrad : F (c₀ + δ) E + F (c₀ - δ) E = F |d - q| E + F |d + q| E) :
    eta (E + (1 - H ((1 - q) / 2))) - childAverage c₀ δ E t ≤ F d E := by
  have hchild := child_average_lower hδ hδc hE (by linarith) ht
  obtain ⟨hA, hA'⟩ := PsiLowEntropyRedesign.child_slope_bounds hE (by linarith) hδ hδc
  have hc := half_compensation_ge (r := c₀) hc₀
  have hs := signed_split_ge_neg_two_sq hc hδ (by linarith) hE hA hA' ht
  have hr := radial_average_loss_81 hE hd4 q
  have hg := parent_gain_strip hE hEu hq hqE
  have hsmall : 2 * δ ^ 2 ≤ (1 / 100) * (q ^ 2 / E) := by
    have hsq : δ ^ 2 ≤ q ^ 2 := by nlinarith
    rw [← mul_div_assoc, le_div_iff₀ hE]
    nlinarith
  have hn : 0 ≤ q ^ 2 / E := by positivity
  unfold radialPhi at hchild
  nlinarith only [hchild, hs, hr, hg, hsmall, hn, hrad]

/-! ## Row 6 -/

/-- Row 6 of `sameSideHalf_of_certificate_rows`, unconditionally. -/
theorem row_noSepA_stripRem : NoSepA_StripRem := by
  intro k μ hab _hsum ha _hb hd _hE11 hd4 hq8 _hEl _hd8 hact
  have hE := meanEntropy_pos' μ
  have hact' : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy :=
    (show phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy from hact).le
  have hEu : μ.meanEntropy ≤ 1 / 200 := by linarith
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hab' : μ.a < μ.b := by linarith
  have hcost := PsiEndpointPlane.law_radial_lower μ hab'
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  by_cases hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a
  · have hc := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
      (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
      (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd (by rwa [hmean])
    have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
    have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
    rw [hca, hcb, hce, hcf] at hc
    change μ.gap ≤ _ at hc
    have hrad : F ((μ.b - μ.a) + (1 - μ.a - μ.b)) μ.meanEntropy +
        F ((μ.b - μ.a) - (1 - μ.a - μ.b)) μ.meanEntropy =
        F |(μ.b - μ.a) - (1 - μ.a - μ.b)| μ.meanEntropy +
          F |(μ.b - μ.a) + (1 - μ.a - μ.b)| μ.meanEntropy := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (μ.b - μ.a) - (1 - μ.a - μ.b)),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ (μ.b - μ.a) + (1 - μ.a - μ.b))]
      ring
    have hm := strip_margin_core (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
      (t := (μ.e - μ.f) / (μ.e + μ.f)) (c₀ := μ.b - μ.a) (δ := 1 - μ.a - μ.b)
      hE hEu hd4 hq0 hq8 ht hq0 hqd (by linarith) le_rfl hrad
    linarith
  · have hdq : μ.b - μ.a ≤ 1 - μ.a - μ.b := (lt_of_not_ge hqd).le
    have hra : |1 - 2 * μ.a| = (1 - μ.a - μ.b) + (μ.b - μ.a) := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * μ.a)]
      ring
    have hrb : |1 - 2 * μ.b| = (1 - μ.a - μ.b) - (μ.b - μ.a) := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * μ.b)]
      ring
    have hchildren : (phi μ.a μ.e + phi μ.b μ.f) / 2 =
        childAverage (1 - μ.a - μ.b) (μ.b - μ.a) μ.meanEntropy
          ((μ.e - μ.f) / (μ.e + μ.f)) := by
      unfold phi childAverage radialPhi
      rw [hra, hrb, hce, hcf]
    have hparent : psi μ.midpoint μ.meanEntropy =
        eta (μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2))) := by
      rw [hmean]
      unfold psi
      congr 1
      ring
    have hgap := PsiRetainedChildBridge.hybrid_gap_le_retained_phi hact'
    change μ.gap ≤ psi μ.midpoint μ.meanEntropy - (phi μ.a μ.e + phi μ.b μ.f) / 2 at hgap
    rw [hchildren, hparent] at hgap
    have e1 : (1 - μ.a - μ.b) + (μ.b - μ.a) = |(μ.b - μ.a) + (1 - μ.a - μ.b)| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (μ.b - μ.a) + (1 - μ.a - μ.b))]
      ring
    have e2 : (1 - μ.a - μ.b) - (μ.b - μ.a) = |(μ.b - μ.a) - (1 - μ.a - μ.b)| := by
      rw [abs_of_nonpos (by linarith : (μ.b - μ.a) - (1 - μ.a - μ.b) ≤ 0)]
      ring
    have hrad : F ((1 - μ.a - μ.b) + (μ.b - μ.a)) μ.meanEntropy +
        F ((1 - μ.a - μ.b) - (μ.b - μ.a)) μ.meanEntropy =
        F |(μ.b - μ.a) - (1 - μ.a - μ.b)| μ.meanEntropy +
          F |(μ.b - μ.a) + (1 - μ.a - μ.b)| μ.meanEntropy := by
      rw [e1, e2]
      ring
    have hm := strip_margin_core (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
      (t := (μ.e - μ.f) / (μ.e + μ.f)) (c₀ := 1 - μ.a - μ.b) (δ := μ.b - μ.a)
      hE hEu hd4 hq0 hq8 ht (by linarith) hdq (by linarith) hdq hrad
    linarith

end CKLaneN23.Row6

end


