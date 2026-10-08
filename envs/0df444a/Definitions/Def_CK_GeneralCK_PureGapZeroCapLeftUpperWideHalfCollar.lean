-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperWideHalfCollar
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperWideHalfCollar
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T04:45:19.209389+00:00
-- url     : https://prove2.me/theorems/74adb413-6380-45c0-b4c2-7b27d048945a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperWideHalfCollar` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperWideHalfCollar` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperWideHalfCollar` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperWideHalfCollar (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperWideHalfCollar.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperAfterHalfCollarAndNarrow

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperWideHalfCollar =====
section

/-!
# Enlarged zero-cap left-upper half collar

The actual logarithm, entropy, inverse-entropy, and radial-contact estimates
are proved through bias 1/22. A sharpened quartic coefficient lower bound
then dominates the actual error 526 z^6 on this entire larger collar.
-/

namespace GeneralCK.ZeroCapLeftUpperWideHalfCollar

theorem leftUpper_J_half_bias_cubic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 22) :
    |J (1 / 2 - q) - (4 * q / Real.log 2 + 16 * q ^ 3 / (3 * Real.log 2))| ≤
      25 * q ^ 5 := by
  have hlog := leftUpper_log_ratio_cubic_remainder
    (show 0 ≤ 2 * q by positivity) (show 2 * q < 1 by linarith)
  have hden : 0 < 5 * (1 - 2 * q) := by linarith
  have hbound : 2 * (2 * q) ^ 5 / (5 * (1 - 2 * q)) ≤ 15 * q ^ 5 := by
    apply (div_le_iff₀ hden).2
    have hcoeff : (64 : ℝ) ≤ 15 * (5 * (1 - 2 * q)) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hq 5)
    nlinarith only [hmul]
  have hL : (3 / 5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [leftUpper_J_half_bias_log (by linarith) (by linarith)]
  have heq :
      (Real.log (1 + 2 * q) - Real.log (1 - 2 * q)) / Real.log 2 -
        (4 * q / Real.log 2 + 16 * q ^ 3 / (3 * Real.log 2)) =
      ((Real.log (1 + 2 * q) - Real.log (1 - 2 * q)) -
        (2 * (2 * q) + 2 * (2 * q) ^ 3 / 3)) / Real.log 2 := by ring
  rw [heq, abs_div, abs_of_pos log_two_pos]
  apply (div_le_iff₀ log_two_pos).2
  have hmul := mul_le_mul_of_nonneg_right hL (show 0 ≤ 25 * q ^ 5 by positivity)
  nlinarith only [hlog.trans hbound, hmul]

theorem leftUpper_eta_half_bias_quartic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 22) :
    |eta (H (1 / 2 - q)) / 2 - leftUpperHalfEtaBJet q (Real.log 2)| ≤
      25 * q ^ 6 := by
  by_cases hzero : q = 0
  · subst q
    norm_num only [sub_zero, H_half, eta_one, zero_div, leftUpperHalfEtaBJet,
      zero_pow, OfNat.ofNat_ne_zero, mul_zero, add_zero, sub_self, abs_zero]
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
  have heta := Comparison.eta_H (show 0 < 1 / 2 - q by linarith)
    (show 1 / 2 - q < 1 / 2 by linarith)
  rw [heta]
  have heq :
      (1 - 2 * (1 / 2 - q)) * J (1 / 2 - q) / 2 -
        leftUpperHalfEtaBJet q (Real.log 2) =
      q * (J (1 / 2 - q) -
        (4 * q / Real.log 2 + 16 * q ^ 3 / (3 * Real.log 2))) := by
    unfold leftUpperHalfEtaBJet
    ring
  rw [heq, abs_mul, abs_of_nonneg hq]
  calc
    _ ≤ q * (25 * q ^ 5) :=
      mul_le_mul_of_nonneg_left (leftUpper_J_half_bias_cubic_remainder hq hqmax) hq
    _ = 25 * q ^ 6 := by ring

theorem leftUpper_interior_half_bias_quartic_remainder {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 22) :
    |interiorCost (1 / 2 - z) (1 / 2 - w) -
        leftUpperHalfInteriorJet z w (Real.log 2)| ≤ 25 * z ^ 6 := by
  have hz : 0 ≤ z := hw.trans hwz
  have hzJ := leftUpper_J_half_bias_cubic_remainder hz hzmax
  have hwJ := leftUpper_J_half_bias_cubic_remainder hw (hwz.trans hzmax)
  have hdiff : 0 ≤ (z - w) / 2 := by linarith
  have heq :
      interiorCost (1 / 2 - z) (1 / 2 - w) -
        leftUpperHalfInteriorJet z w (Real.log 2) =
      (z - w) / 2 *
        ((J (1 / 2 - z) -
            (4 * z / Real.log 2 + 16 * z ^ 3 / (3 * Real.log 2))) -
          (J (1 / 2 - w) -
            (4 * w / Real.log 2 + 16 * w ^ 3 / (3 * Real.log 2)))) := by
    unfold interiorCost leftUpperHalfInteriorJet
    ring
  rw [heq, abs_mul, abs_of_nonneg hdiff]
  calc
    _ ≤ (z - w) / 2 * (25 * z ^ 5 + 25 * w ^ 5) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hzJ hwJ)) hdiff
    _ ≤ z / 2 * (25 * z ^ 5 + 25 * z ^ 5) := by
      gcongr
      · linarith
    _ = 25 * z ^ 6 := by ring

private theorem sixth_barrier {f f' : ℝ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hzero : f 0 = 0)
    (hd : ∀ t ∈ Set.Icc 0 q, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Set.Icc 0 q, |f' t| ≤ 25 * t ^ 5) :
    |f q| ≤ (25 / 6 : ℝ) * q ^ 6 := by
  have hB (t : ℝ) : HasDerivAt (fun x : ℝ => (25 / 6 : ℝ) * x ^ 6)
      (25 * t ^ 5) t := by
    convert! (hasDerivAt_pow 6 t).const_mul (25 / 6 : ℝ) using 1 <;> norm_num <;> ring
  have hc : ContinuousOn f (Set.Icc 0 q) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hBc : ContinuousOn (fun x : ℝ => (25 / 6 : ℝ) * x ^ 6) (Set.Icc 0 q) :=
    fun t _ => (hB t).continuousAt.continuousWithinAt
  have hupper := image_le_of_deriv_right_le_deriv_boundary hc
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (show f 0 ≤ (25 / 6 : ℝ) * (0 : ℝ) ^ 6 by simp [hzero]) hBc
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => (abs_le.mp (hb t ⟨ht.1, ht.2.le⟩)).2)
    (show q ∈ Set.Icc 0 q from ⟨hq, le_rfl⟩)
  have hlower := image_le_of_deriv_right_le_deriv_boundary hc.neg
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).neg.hasDerivWithinAt)
    (show -f 0 ≤ (25 / 6 : ℝ) * (0 : ℝ) ^ 6 by simp [hzero]) hBc
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => (neg_le_iff_add_nonneg).2
      (by linarith [(abs_le.mp (hb t ⟨ht.1, ht.2.le⟩)).1]))
    (show q ∈ Set.Icc 0 q from ⟨hq, le_rfl⟩)
  change -f q ≤ _ at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem leftUpper_entropy_half_bias_quartic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 22) :
    |1 - H (1 / 2 - q) - (2 * q ^ 2 / Real.log 2 +
        4 * q ^ 4 / (3 * Real.log 2))| ≤ (25 / 6 : ℝ) * q ^ 6 := by
  let E : ℝ → ℝ := fun t => 1 - H (1 / 2 - t) -
    (2 * t ^ 2 / Real.log 2 + 4 * t ^ 4 / (3 * Real.log 2))
  change |E q| ≤ _
  apply sixth_barrier hq (f' := fun t => J (1 / 2 - t) -
    (4 * t / Real.log 2 + 16 * t ^ 3 / (3 * Real.log 2)))
  · norm_num [E, H_half]
  · intro t ht
    have hdH := (Comparison.hasDerivAt_H
      (show 0 < 1 / 2 - t by linarith [ht.2])
      (show 1 / 2 - t < 1 by linarith [ht.1])).comp t
        ((hasDerivAt_id t).const_sub (1 / 2 : ℝ))
    have hd2 := ((hasDerivAt_pow 2 t).const_mul 2).div_const (Real.log 2)
    have hd4 := ((hasDerivAt_pow 4 t).const_mul 4).div_const (3 * Real.log 2)
    convert! (hdH.const_sub 1).sub (hd2.add hd4) using 1 <;> simp [E] <;> ring
  · intro t ht
    exact leftUpper_J_half_bias_cubic_remainder ht.1 (ht.2.trans hqmax)

private theorem quartic_square_control {z delta D2 D4 : ℝ}
    (hz : 0 ≤ z) (hzmax : z ≤ 1 / 22) (hdelta : 0 ≤ delta)
    (hD20 : 0 ≤ D2) (hD2 : D2 ≤ 3 * z ^ 2)
    (hD40 : 0 ≤ D4) (hD4 : D4 ≤ 2 * z ^ 4)
    (herr : |delta - D2 - D4| ≤ (25 / 6 : ℝ) * z ^ 6) :
    delta ≤ 4 * z ^ 2 ∧ |delta ^ 2 - D2 ^ 2| ≤ 16 * z ^ 6 := by
  have hz2 : z ^ 2 ≤ (1 / 22 : ℝ) ^ 2 := by gcongr
  have hz4 : z ^ 4 ≤ z ^ 2 / 484 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (sq_nonneg z)]
  have hz6 : z ^ 6 ≤ z ^ 4 / 484 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (pow_nonneg hz 4)]
  have hdiff : |delta - D2| ≤ (9 / 4 : ℝ) * z ^ 4 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp herr).1, (abs_le.mp herr).2,
      pow_nonneg hz 4]
  have hdup : delta ≤ 4 * z ^ 2 := by
    linarith [(abs_le.mp hdiff).2, sq_nonneg z]
  refine ⟨hdup, ?_⟩
  have hsum : |delta + D2| ≤ 7 * z ^ 2 := by
    rw [abs_of_nonneg (add_nonneg hdelta hD20)]
    linarith
  calc
    |delta ^ 2 - D2 ^ 2| = |delta - D2| * |delta + D2| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ((9 / 4 : ℝ) * z ^ 4) * (7 * z ^ 2) :=
      mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ ≤ 16 * z ^ 6 := by nlinarith [pow_nonneg hz 6]

private theorem half_jet_bounds {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) :
    0 ≤ leftUpperHalfD2 z w (Real.log 2) ∧
    leftUpperHalfD2 z w (Real.log 2) ≤ 3 * z ^ 2 ∧
    0 ≤ leftUpperHalfD4 z w (Real.log 2) ∧
    leftUpperHalfD4 z w (Real.log 2) ≤ 2 * z ^ 4 := by
  have hz := hw.trans hwz
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hw2 : w ^ 2 ≤ z ^ 2 := by gcongr
  have hw4 : w ^ 4 ≤ z ^ 4 := by gcongr
  refine ⟨by unfold leftUpperHalfD2; positivity, ?_,
    by unfold leftUpperHalfD4; positivity, ?_⟩
  · unfold leftUpperHalfD2
    apply (div_le_iff₀ log_two_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 3 * z ^ 2 by positivity)]
  · unfold leftUpperHalfD4
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.log 2)).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 6 * z ^ 4 by positivity)]

theorem leftUpper_halfEntropy_deficit_quartic_remainder {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 22) :
    |(1 - (H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
        leftUpperHalfD2 z w (Real.log 2) -
        leftUpperHalfD4 z w (Real.log 2)| ≤ (25 / 6 : ℝ) * z ^ 6 := by
  have hz := hw.trans hwz
  have hEz := leftUpper_entropy_half_bias_quartic_remainder hz hzmax
  have hEw := leftUpper_entropy_half_bias_quartic_remainder hw (hwz.trans hzmax)
  have hw6 : w ^ 6 ≤ z ^ 6 := by gcongr
  have heq : (1 - (H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
      leftUpperHalfD2 z w (Real.log 2) - leftUpperHalfD4 z w (Real.log 2) =
      ((1 - H (1 / 2 - z) - (2 * z ^ 2 / Real.log 2 + 4 * z ^ 4 / (3 * Real.log 2))) +
       (1 - H (1 / 2 - w) - (2 * w ^ 2 / Real.log 2 + 4 * w ^ 4 / (3 * Real.log 2)))) / 2 := by
    unfold leftUpperHalfD2 leftUpperHalfD4
    ring
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hEz).1, (abs_le.mp hEz).2,
    (abs_le.mp hEw).1, (abs_le.mp hEw).2]

theorem leftUpper_eta_deficit_quadratic_remainder {q : ℝ}
    (hq : 0 ≤ q) (hqmax : q ≤ 1 / 22) :
    |eta (H (1 / 2 - q)) -
      (4 * (1 - H (1 / 2 - q)) +
        (4 * Real.log 2 / 3) * (1 - H (1 / 2 - q)) ^ 2)| ≤ 83 * q ^ 6 := by
  let delta := 1 - H (1 / 2 - q)
  let D2 := leftUpperHalfD2 q q (Real.log 2)
  let D4 := leftUpperHalfD4 q q (Real.log 2)
  have hD := half_jet_bounds hq (le_refl q)
  have hE : |delta - D2 - D4| ≤ (25 / 6 : ℝ) * q ^ 6 := by
    convert leftUpper_halfEntropy_deficit_quartic_remainder hq (le_refl q) hqmax using 1 <;>
      dsimp [delta, D2, D4] <;> ring
  have hdelta : 0 ≤ delta := sub_nonneg.mpr (H_le_one _)
  have hsq := (quartic_square_control hq hqmax hdelta hD.1 hD.2.1
    hD.2.2.1 hD.2.2.2 hE).2
  have hc0 : 0 ≤ 4 * Real.log 2 / 3 := by positivity
  have hc1 : 4 * Real.log 2 / 3 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hprod : |(4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2)| ≤ 16 * q ^ 6 := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc
      _ ≤ 1 * (16 * q ^ 6) := mul_le_mul hc1 hsq (abs_nonneg _) (by norm_num)
      _ = 16 * q ^ 6 := one_mul _
  have hEta := leftUpper_eta_half_bias_quartic_remainder hq hqmax
  have hjet : 2 * leftUpperHalfEtaBJet q (Real.log 2) =
      4 * D2 + 4 * D4 + (4 * Real.log 2 / 3) * D2 ^ 2 := by
    dsimp [D2, D4, leftUpperHalfEtaBJet, leftUpperHalfD2, leftUpperHalfD4]
    field_simp [ne_of_gt log_two_pos]
    ring
  have heq : eta (H (1 / 2 - q)) - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2) =
      2 * (eta (H (1 / 2 - q)) / 2 - leftUpperHalfEtaBJet q (Real.log 2)) -
      4 * (delta - D2 - D4) - (4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2) := by
    linarith only [hjet]
  change |eta (H (1 / 2 - q)) - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2)| ≤ _
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hEta).1, (abs_le.mp hEta).2,
    (abs_le.mp hE).1, (abs_le.mp hE).2, (abs_le.mp hprod).1,
    (abs_le.mp hprod).2, pow_nonneg hq 6]

theorem leftUpper_middle_eta_quartic_remainder {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 22) :
    |eta ((H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
      leftUpperHalfEtaJet (leftUpperHalfD2 z w (Real.log 2))
        (leftUpperHalfD4 z w (Real.log 2)) (Real.log 2)| ≤ 116 * z ^ 6 := by
  have hz := hw.trans hwz
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  let delta := 1 - h
  let D2 := leftUpperHalfD2 z w (Real.log 2)
  let D4 := leftUpperHalfD4 z w (Real.log 2)
  have hm0 : 0 ≤ h := by
    have ha := H_pos (show 0 < 1 / 2 - z by linarith)
      (show 1 / 2 - z < 1 by linarith)
    have hb := H_pos (show 0 < 1 / 2 - w by linarith)
      (show 1 / 2 - w < 1 by linarith)
    dsimp [h]
    linarith
  have hm1 : h ≤ 1 := by
    dsimp [h]
    linarith [H_le_one (1 / 2 - z), H_le_one (1 / 2 - w)]
  have hinv := leftUpper_halfEntropyInverse_between
    (show 0 ≤ 1 / 2 - z by linarith)
    (show 1 / 2 - z ≤ 1 / 2 - w by linarith)
    (show 1 / 2 - w ≤ 1 / 2 by linarith)
  let q := 1 / 2 - entropyInverse h
  have hq0 : 0 ≤ q := by
    change 0 ≤ 1 / 2 - entropyInverse h
    change _ ∧ entropyInverse h ≤ 1 / 2 - w at hinv
    linarith [hinv.2]
  have hqz : q ≤ z := by
    change 1 / 2 - entropyInverse h ≤ z
    change 1 / 2 - z ≤ entropyInverse h ∧ _ at hinv
    linarith [hinv.1]
  have hEq : H (1 / 2 - q) = h := by
    simpa only [q, sub_sub_cancel] using (entropyInverse_spec hm0 hm1).2.2
  have hEtaq := leftUpper_eta_deficit_quadratic_remainder hq0 (hqz.trans hzmax)
  rw [hEq] at hEtaq
  have hEta : |eta h - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2)| ≤
      83 * z ^ 6 := hEtaq.trans (by gcongr)
  have hD := half_jet_bounds hw hwz
  have hE : |delta - D2 - D4| ≤ (25 / 6 : ℝ) * z ^ 6 :=
    leftUpper_halfEntropy_deficit_quartic_remainder hw hwz hzmax
  have hsq := (quartic_square_control hz hzmax (show 0 ≤ delta from sub_nonneg.mpr hm1)
    hD.1 hD.2.1 hD.2.2.1 hD.2.2.2 hE).2
  have hc0 : 0 ≤ 4 * Real.log 2 / 3 := by positivity
  have hc1 : 4 * Real.log 2 / 3 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hprod : |(4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2)| ≤ 16 * z ^ 6 := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc
      _ ≤ 1 * (16 * z ^ 6) := mul_le_mul hc1 hsq (abs_nonneg _) (by norm_num)
      _ = 16 * z ^ 6 := one_mul _
  have heq : eta h - leftUpperHalfEtaJet D2 D4 (Real.log 2) =
      (eta h - (4 * delta + (4 * Real.log 2 / 3) * delta ^ 2)) +
      4 * (delta - D2 - D4) + (4 * Real.log 2 / 3) * (delta ^ 2 - D2 ^ 2) := by
    unfold leftUpperHalfEtaJet
    ring
  change |eta h - leftUpperHalfEtaJet D2 D4 (Real.log 2)| ≤ _
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hEta).1, (abs_le.mp hEta).2,
    (abs_le.mp hE).1, (abs_le.mp hE).2, (abs_le.mp hprod).1,
    (abs_le.mp hprod).2, pow_nonneg hz 6]

theorem leftUpper_halfEntropy_radial_data {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 22) :
    let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
    (9 / 10 : ℝ) ≤ h ∧ h ≤ 1 ∧
      0 ≤ 1 - h ∧ 1 - h ≤ 4 * z ^ 2 ∧
      |1 - h - leftUpperHalfD2 z w (Real.log 2)| ≤ 3 * z ^ 4 := by
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  let D2 := leftUpperHalfD2 z w (Real.log 2)
  let D4 := leftUpperHalfD4 z w (Real.log 2)
  have hz := hw.trans hwz
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hw2 : w ^ 2 ≤ z ^ 2 := by gcongr
  have hw4 : w ^ 4 ≤ z ^ 4 := by gcongr
  have hD2 : D2 ≤ 3 * z ^ 2 := by
    apply (div_le_iff₀ log_two_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 3 * z ^ 2 by positivity)]
  have hD40 : 0 ≤ D4 := by dsimp [D4, leftUpperHalfD4]; positivity
  have hD4 : D4 ≤ 2 * z ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * Real.log 2)).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 6 * z ^ 4 by positivity)]
  have hz2 : z ^ 2 ≤ (1 / 22 : ℝ) ^ 2 := by gcongr
  have hz4 : z ^ 4 ≤ z ^ 2 / 484 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (sq_nonneg z)]
  have hz6 : z ^ 6 ≤ z ^ 4 / 484 := by
    nlinarith only [mul_le_mul_of_nonneg_right hz2 (pow_nonneg hz 4)]
  have hE : |1 - h - D2 - D4| ≤ (25 / 6 : ℝ) * z ^ 6 :=
    leftUpper_halfEntropy_deficit_quartic_remainder hw hwz hzmax
  have hdiff : |1 - h - D2| ≤ 3 * z ^ 4 := by
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hE).1, (abs_le.mp hE).2, pow_nonneg hz 4]
  have hdelta : 1 - h ≤ 4 * z ^ 2 := by
    linarith [(abs_le.mp hdiff).2, sq_nonneg z]
  have hm1 : h ≤ 1 := by
    dsimp [h]
    linarith [H_le_one (1 / 2 - z), H_le_one (1 / 2 - w)]
  exact ⟨(show (9 / 10 : ℝ) ≤ h by linarith), hm1,
    (show 0 ≤ 1 - h by linarith), hdelta, hdiff⟩

private theorem contact_taylor_control {t rho delta L : ℝ}
    (ht : 0 ≤ t) (htr : t ≤ rho) (hL : (2 / 3 : ℝ) ≤ L)
    (heq : rho - t = rho * delta) (hdelta : delta ≤ t ^ 2)
    (herr : |delta - t ^ 2 / (2 * L)| ≤ t ^ 4 / 4) :
    |t - rho + rho ^ 3 / (2 * L)| ≤ (7 / 4 : ℝ) * rho ^ 5 ∧
    |t ^ 3 - rho ^ 3| ≤ 3 * rho ^ 5 := by
  have hr : 0 ≤ rho := ht.trans htr
  have hLp : 0 < L := by linarith
  have ht2 : t ^ 2 ≤ rho ^ 2 := by gcongr
  have ht4 : t ^ 4 ≤ rho ^ 4 := by gcongr
  have hgap : rho - t ≤ rho ^ 3 := by
    rw [heq]
    calc
      rho * delta ≤ rho * t ^ 2 := mul_le_mul_of_nonneg_left hdelta hr
      _ ≤ rho * rho ^ 2 := mul_le_mul_of_nonneg_left ht2 hr
      _ = rho ^ 3 := by ring
  have hsquare : rho ^ 2 - t ^ 2 ≤ 2 * rho ^ 4 := by
    have hp := mul_le_mul hgap (show rho + t ≤ 2 * rho by linarith)
      (by linarith : 0 ≤ rho + t) (pow_nonneg hr 3)
    nlinarith only [hp]
  have hsquare0 : 0 ≤ rho ^ 2 - t ^ 2 := by linarith
  have hsdiv : (rho ^ 2 - t ^ 2) / (2 * L) ≤ (3 / 2 : ℝ) * rho ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).2
    nlinarith [mul_le_mul_of_nonneg_right hL (show 0 ≤ 3 * rho ^ 4 by positivity)]
  have htri : |(rho ^ 2 - t ^ 2) / (2 * L) + (t ^ 2 / (2 * L) - delta)| ≤
      (3 / 2 : ℝ) * rho ^ 4 + rho ^ 4 / 4 := by
    calc
      _ ≤ |(rho ^ 2 - t ^ 2) / (2 * L)| + |t ^ 2 / (2 * L) - delta| := abs_add_le _ _
      _ = (rho ^ 2 - t ^ 2) / (2 * L) + |delta - t ^ 2 / (2 * L)| := by
        rw [abs_of_nonneg (div_nonneg hsquare0 (by positivity)), abs_sub_comm]
      _ ≤ (3 / 2 : ℝ) * rho ^ 4 + rho ^ 4 / 4 := by linarith
  have hid : t - rho + rho ^ 3 / (2 * L) =
      rho * ((rho ^ 2 - t ^ 2) / (2 * L) + (t ^ 2 / (2 * L) - delta)) := by
    calc
      _ = rho ^ 3 / (2 * L) - rho * delta := by linarith only [heq]
      _ = _ := by ring
  constructor
  · rw [hid, abs_mul, abs_of_nonneg hr]
    have hp := mul_le_mul_of_nonneg_left htri hr
    nlinarith only [hp]
  · rw [abs_of_nonpos (sub_nonpos.mpr (by gcongr : t ^ 3 ≤ rho ^ 3))]
    have hmid : rho ^ 2 + rho * t + t ^ 2 ≤ 3 * rho ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left htr hr]
    have hp := mul_le_mul hgap hmid (by positivity : 0 ≤ rho ^ 2 + rho * t + t ^ 2)
      (pow_nonneg hr 3)
    nlinarith only [hp]

theorem leftUpper_F_contact_quartic_remainder {r h : ℝ}
    (hr : 0 ≤ r) (hrmax : r ≤ 1 / 22) (hhlo : (9 / 10 : ℝ) ≤ h) :
    |F r h - (2 * r ^ 2 / (Real.log 2 * h) +
      (2 / (3 * Real.log 2) - 1 / (Real.log 2) ^ 2) * r ^ 4 / h ^ 3)| ≤
      16 * r ^ 6 := by
  by_cases hr0 : r = 0
  · subst r
    norm_num [F]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hh : 0 < h := by linarith
  let v := radialContact r h
  let q := 1 / 2 - v
  let t := 2 * q
  let rho := r / h
  let L := Real.log 2
  let c := 2 / (3 * L) - 1 / L ^ 2
  have hL : (2 / 3 : ℝ) ≤ L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hLp : 0 < L := log_two_pos
  have hv0 : 0 < v := radialContact_pos hrp hh
  have hvhalf : v < 1 / 2 := radialContact_lt_half hrp hh
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrho : 0 ≤ rho := div_nonneg hr hh.le
  have hcEq : r * H v = h * t := by
    have he := radialContact_equation hrp hh
    dsimp [v, t, q] at *
    nlinarith only [he]
  have htr : t ≤ rho := by
    apply (le_div_iff₀ hh).2
    nlinarith [mul_le_mul_of_nonneg_left (H_le_one v) hr]
  have hrhomax : rho ≤ 1 / 19 := by
    apply (div_le_iff₀ hh).2
    linarith
  have hqmax : q ≤ 1 / 22 := by dsimp [t] at htr; linarith
  have hqeq : 1 / 2 - q = v := by dsimp [q]; ring
  have hdata := leftUpper_halfEntropy_radial_data hq (le_refl q) hqmax
  have hHavg : (H (1 / 2 - q) + H (1 / 2 - q)) / 2 = H v := by rw [hqeq]; ring
  dsimp only at hdata
  rw [hHavg] at hdata
  have hdelta : 1 - H v ≤ t ^ 2 := by
    have he := hdata.2.2.2.1
    dsimp [t]
    nlinarith only [he]
  have hD2 : leftUpperHalfD2 q q L = t ^ 2 / (2 * L) := by
    dsimp [leftUpperHalfD2, t]
    ring
  have herr : |1 - H v - t ^ 2 / (2 * L)| ≤ t ^ 4 / 4 := by
    have he := hdata.2.2.2.2
    change |1 - H v - leftUpperHalfD2 q q L| ≤ 3 * q ^ 4 at he
    rw [hD2] at he
    exact he.trans (by dsimp [t]; nlinarith [pow_nonneg hq 4])
  have heq : rho - t = rho * (1 - H v) := by
    dsimp [rho]
    field_simp [ne_of_gt hh]
    nlinarith only [hcEq]
  have hTaylor := contact_taylor_control ht htr hL heq hdelta herr
  have hJ := leftUpper_J_half_bias_cubic_remainder hq hqmax
  rw [hqeq] at hJ
  have hJpoly : 4 * q / L + 16 * q ^ 3 / (3 * L) =
      (2 / L) * t + (2 / (3 * L)) * t ^ 3 := by dsimp [t]; ring
  change |J v - (4 * q / L + 16 * q ^ 3 / (3 * L))| ≤ 25 * q ^ 5 at hJ
  rw [hJpoly] at hJ
  have hq5 : q ^ 5 ≤ (rho / 2) ^ 5 := by
    have hqr : q ≤ rho / 2 := by dsimp [t] at htr; linarith
    gcongr
  have hJerr : |J v - ((2 / L) * t + (2 / (3 * L)) * t ^ 3)| ≤
      (25 / 32 : ℝ) * rho ^ 5 := by nlinarith only [hJ, hq5]
  have hA0 : 0 ≤ 2 / L := by positivity
  have hA : 2 / L ≤ 3 := (div_le_iff₀ hLp).2 (by linarith)
  have hB0 : 0 ≤ 2 / (3 * L) := by positivity
  have hB : 2 / (3 * L) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hT1 : |(2 / L) * (t - rho + rho ^ 3 / (2 * L))| ≤
      (21 / 4 : ℝ) * rho ^ 5 := by
    rw [abs_mul, abs_of_nonneg hA0]
    have hp := mul_le_mul hA hTaylor.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith only [hp]
  have hT3 : |(2 / (3 * L)) * (t ^ 3 - rho ^ 3)| ≤ 3 * rho ^ 5 := by
    rw [abs_mul, abs_of_nonneg hB0]
    simpa only [one_mul] using
      mul_le_mul hB hTaylor.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hJid : J v - ((2 / L) * rho + c * rho ^ 3) =
      (J v - ((2 / L) * t + (2 / (3 * L)) * t ^ 3)) +
      (2 / L) * (t - rho + rho ^ 3 / (2 * L)) +
      (2 / (3 * L)) * (t ^ 3 - rho ^ 3) := by
    dsimp [c]
    field_simp [ne_of_gt hLp] <;> ring
  have hJtotal : |J v - ((2 / L) * rho + c * rho ^ 3)| ≤
      (289 / 32 : ℝ) * rho ^ 5 := by
    rw [hJid]
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hJerr).1, (abs_le.mp hJerr).2,
      (abs_le.mp hT1).1, (abs_le.mp hT1).2, (abs_le.mp hT3).1, (abs_le.mp hT3).2]
  have hFid : F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3) =
      r * (J v - ((2 / L) * rho + c * rho ^ 3)) := by
    rw [F, if_neg hr0]
    dsimp [v, rho]
    field_simp [ne_of_gt hh, ne_of_gt hLp] <;> ring
  change |F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3)| ≤ _
  rw [hFid, abs_mul, abs_of_nonneg hr]
  calc
    _ ≤ r * ((289 / 32 : ℝ) * rho ^ 5) := mul_le_mul_of_nonneg_left hJtotal hr
    _ = ((289 / 32 : ℝ) * r ^ 6) / h ^ 5 := by dsimp [rho]; ring
    _ ≤ 16 * r ^ 6 := by
      apply (div_le_iff₀ (pow_pos hh 5)).2
      have hh5 : (9 / 10 : ℝ) ^ 5 ≤ h ^ 5 := by gcongr
      have hc : (289 / 32 : ℝ) ≤ 16 * h ^ 5 := by nlinarith only [hh5]
      nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg hr 6)]

theorem leftUpper_F_half_bias_quartic_remainder {z w r : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 22)
    (hr : 0 ≤ r) (hrz : r ≤ z) :
    |F r ((H (1 / 2 - z) + H (1 / 2 - w)) / 2) -
      leftUpperHalfFJet r (leftUpperHalfD2 z w (Real.log 2)) (Real.log 2)| ≤
      120 * z ^ 6 := by
  have hz := hw.trans hwz
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  let delta := 1 - h
  let D2 := leftUpperHalfD2 z w (Real.log 2)
  let L := Real.log 2
  let c := 2 / (3 * L) - 1 / L ^ 2
  have hdata := leftUpper_halfEntropy_radial_data hw hwz hzmax
  change (9 / 10 : ℝ) ≤ h ∧ h ≤ 1 ∧ 0 ≤ delta ∧ delta ≤ 4 * z ^ 2 ∧
    |delta - D2| ≤ 3 * z ^ 4 at hdata
  have hh : 0 < h := by linarith [hdata.1]
  have hdelta0 : 0 ≤ delta := hdata.2.2.1
  have hdeltaBound : delta ≤ 4 * z ^ 2 := hdata.2.2.2.1
  have hLp : 0 < L := log_two_pos
  have hL : (2 / 3 : ℝ) ≤ L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hLhi : L ≤ 3 / 4 := by dsimp [L]; linarith [Real.log_two_lt_d9]
  have hdelta2 : delta ^ 2 ≤ 16 * z ^ 4 := by
    calc
      delta ^ 2 ≤ (4 * z ^ 2) ^ 2 := by gcongr
      _ = 16 * z ^ 4 := by ring
  have hdeltaDiv : delta ^ 2 / h ≤ 18 * z ^ 4 := by
    apply (div_le_iff₀ hh).2
    nlinarith [mul_le_mul_of_nonneg_right hdata.1 (show 0 ≤ 18 * z ^ 4 by positivity)]
  have hinvId : 1 / h - 1 - D2 = (delta - D2) + delta ^ 2 / h := by
    dsimp [delta]
    field_simp [ne_of_gt hh] <;> ring
  have hinv : |1 / h - 1 - D2| ≤ 21 * z ^ 4 := by
    rw [hinvId]
    have ha := abs_add_le (delta - D2) (delta ^ 2 / h)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg delta) hh.le)] at ha
    linarith [hdata.2.2.2.2]
  have hh2 : h ^ 2 ≤ 1 := by
    have hp := mul_le_mul hdata.2.1 hdata.2.1 hh.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hp]
  have hnum : delta * (1 + h + h ^ 2) ≤ 12 * z ^ 2 := by
    have hp := mul_le_mul hdata.2.2.2.1 (show 1 + h + h ^ 2 ≤ 3 by linarith [hdata.2.1])
      (by positivity : 0 ≤ 1 + h + h ^ 2) (by positivity : 0 ≤ 4 * z ^ 2)
    nlinarith only [hp]
  have hinv3Id : 1 / h ^ 3 - 1 = delta * (1 + h + h ^ 2) / h ^ 3 := by
    dsimp [delta]
    field_simp [ne_of_gt hh] <;> ring
  have hinv3 : |1 / h ^ 3 - 1| ≤ 17 * z ^ 2 := by
    rw [hinv3Id, abs_of_nonneg (by positivity :
      0 ≤ delta * (1 + h + h ^ 2) / h ^ 3)]
    apply (div_le_iff₀ (pow_pos hh 3)).2
    have hh3 : (9 / 10 : ℝ) ^ 3 ≤ h ^ 3 := by gcongr; exact hdata.1
    have hc : (12 : ℝ) ≤ 17 * h ^ 3 := by nlinarith only [hh3]
    nlinarith only [hnum, mul_le_mul_of_nonneg_right hc (sq_nonneg z)]
  have hcForm : c = (2 * L - 3) / (3 * L ^ 2) := by
    dsimp [c]
    field_simp [ne_of_gt hLp] <;> ring
  have hcabs : |c| ≤ 2 := by
    rw [hcForm]
    have hden : 0 < 3 * L ^ 2 := by positivity
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hden).2
      nlinarith [sq_nonneg (L - 2 / 3)]
    · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le).trans (by norm_num)
  have hA0 : 0 ≤ 2 / L := by positivity
  have hA : 2 / L ≤ 3 := (div_le_iff₀ hLp).2 (by linarith)
  have hr2 : r ^ 2 ≤ z ^ 2 := by gcongr
  have hr4 : r ^ 4 ≤ z ^ 4 := by gcongr
  have hr6 : r ^ 6 ≤ z ^ 6 := by gcongr
  have hContact : |F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3)| ≤
      16 * z ^ 6 :=
    (leftUpper_F_contact_quartic_remainder hr (hrz.trans hzmax) hdata.1).trans
      (mul_le_mul_of_nonneg_left hr6 (by norm_num))
  have hLeading : |((2 / L) * r ^ 2) * (1 / h - 1 - D2)| ≤ 63 * z ^ 6 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 / L) * r ^ 2)]
    have hAr : (2 / L) * r ^ 2 ≤ 3 * z ^ 2 :=
      mul_le_mul hA hr2 (sq_nonneg r) (by norm_num)
    have hp := mul_le_mul hAr hinv (abs_nonneg _) (by positivity : 0 ≤ 3 * z ^ 2)
    nlinarith only [hp]
  have hFourth : |(c * r ^ 4) * (1 / h ^ 3 - 1)| ≤ 34 * z ^ 6 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr 4)]
    have hCr : |c| * r ^ 4 ≤ 2 * z ^ 4 :=
      mul_le_mul hcabs hr4 (pow_nonneg hr 4) (by norm_num)
    have hp := mul_le_mul hCr hinv3 (abs_nonneg _) (by positivity : 0 ≤ 2 * z ^ 4)
    nlinarith only [hp]
  have heq : F r h - leftUpperHalfFJet r D2 L =
      (F r h - (2 * r ^ 2 / (L * h) + c * r ^ 4 / h ^ 3)) +
      ((2 / L) * r ^ 2) * (1 / h - 1 - D2) +
      (c * r ^ 4) * (1 / h ^ 3 - 1) := by
    dsimp [leftUpperHalfFJet, c]
    ring
  change |F r h - leftUpperHalfFJet r D2 L| ≤ _
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hContact).1, (abs_le.mp hContact).2,
    (abs_le.mp hLeading).1, (abs_le.mp hLeading).2,
    (abs_le.mp hFourth).1, (abs_le.mp hFourth).2, pow_nonneg hz 6]

private noncomputable def leftUpperHalfActualRadial (z w : ℝ) : ℝ :=
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  interiorCost (1 / 2 - z) (1 / 2 - w) +
    2 * F z h - F (z - w) h - eta h + eta (H (1 / 2 - w)) / 2

theorem leftUpper_halfCollar_actual_radial_error {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 22) :
    |leftUpperHalfActualRadial z w -
      leftUpperHalfCombinedJet z w (Real.log 2)| ≤ 526 * z ^ 6 := by
  have hz : 0 ≤ z := hw.trans hwz
  have hrzw : 0 ≤ z - w := by linarith
  have hrzwz : z - w ≤ z := by linarith
  have hI := leftUpper_interior_half_bias_quartic_remainder hw hwz hzmax
  have hFz := leftUpper_F_half_bias_quartic_remainder
    hw hwz hzmax hz (le_refl z)
  have hFzw := leftUpper_F_half_bias_quartic_remainder
    hw hwz hzmax hrzw hrzwz
  have hM := leftUpper_middle_eta_quartic_remainder hw hwz hzmax
  have hB0 := leftUpper_eta_half_bias_quartic_remainder hw (hwz.trans hzmax)
  have hw6 : w ^ 6 ≤ z ^ 6 := by gcongr
  have hB :
      |eta (H (1 / 2 - w)) / 2 -
        leftUpperHalfEtaBJet w (Real.log 2)| ≤ 25 * z ^ 6 :=
    hB0.trans (by gcongr)
  apply abs_le.mpr
  constructor
  · unfold leftUpperHalfActualRadial leftUpperHalfCombinedJet
    dsimp
    linarith only [(abs_le.mp hI).1, (abs_le.mp hI).2,
      (abs_le.mp hFz).1, (abs_le.mp hFz).2,
      (abs_le.mp hFzw).1, (abs_le.mp hFzw).2,
      (abs_le.mp hM).1, (abs_le.mp hM).2,
      (abs_le.mp hB).1, (abs_le.mp hB).2]
  · unfold leftUpperHalfActualRadial leftUpperHalfCombinedJet
    dsimp
    linarith only [(abs_le.mp hI).1, (abs_le.mp hI).2,
      (abs_le.mp hFz).1, (abs_le.mp hFz).2,
      (abs_le.mp hFzw).1, (abs_le.mp hFzw).2,
      (abs_le.mp hM).1, (abs_le.mp hM).2,
      (abs_le.mp hB).1, (abs_le.mp hB).2]

theorem quartic_coefficient_lower (lambda : ℝ) :
    (10 / 9 : ℝ) ≤ leftUpperQuarticCoefficient (Real.log 2) lambda := by
  let L := Real.log 2
  have hLlo : (3 / 5 : ℝ) ≤ L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hLhi : L ≤ (347 / 500 : ℝ) := by dsimp [L]; linarith [Real.log_two_lt_d9]
  have hLpos : 0 < L := log_two_pos
  have hfour : 0 ≤ (10 * L - 3) * lambda ^ 4 :=
    mul_nonneg (by linarith) (by positivity)
  have htwo : 0 ≤ (18 - 20 * L) * lambda ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg lambda)
  have hLsq : L ^ 2 ≤ (347 / 500 : ℝ) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hLhi)
      (show 0 ≤ (347 / 500 : ℝ) + L by linarith)
    nlinarith only [hp]
  change (10 / 9 : ℝ) ≤ leftUpperQuarticCoefficient L lambda
  unfold leftUpperQuarticCoefficient leftUpperQuarticNumerator
  apply (le_div_iff₀ (by positivity : 0 < 3 * L ^ 2)).mpr
  nlinarith only [hfour, htwo, hLsq, hLhi]

/-- Strict actual-gap positivity on the enlarged collar, including z=1/22.
No Taylor remainder or finite certificate premise remains. -/
theorem leftUpper_halfCollar_positive {z lambda : ℝ}
    (hz : 0 < z) (hzmax : z ≤ 1 / 22)
    (hlambda : 0 < lambda) (hlambda1 : lambda < 1) :
    0 < canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) := by
  have hw : 0 ≤ lambda * z := (mul_pos hlambda hz).le
  have hwz : lambda * z ≤ z := by
    nlinarith [mul_le_mul_of_nonneg_right hlambda1.le hz.le]
  have herr := leftUpper_halfCollar_actual_radial_error hw hwz hzmax
  rw [leftUpperHalfCombinedJet_eq_quartic
    (z := z) (lambda := lambda) (L := Real.log 2) log_two_pos.ne'] at herr
  have hP := quartic_coefficient_lower lambda
  have hz2 : z ^ 2 ≤ (1 / 22 : ℝ) ^ 2 := by
    have hp : 0 ≤ ((1 / 22 : ℝ) - z) * ((1 / 22 : ℝ) + z) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [hp]
  have hsmall : 526 * z ^ 2 < (10 / 9 : ℝ) := by
    nlinarith only [hz2]
  have hcoef : 0 < leftUpperQuarticCoefficient (Real.log 2) lambda - 526 * z ^ 2 := by
    linarith
  have hquartic : 0 < z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda -
      526 * z ^ 6 := by
    have hp := mul_pos (pow_pos hz 4) hcoef
    nlinarith only [hp]
  have ha : 0 < 1 / 2 - z := by linarith
  have hab : 1 / 2 - z < 1 / 2 - lambda * z := by
    nlinarith [mul_lt_mul_of_pos_right hlambda1 hz]
  have hb : 1 / 2 - lambda * z < 1 / 2 := by
    nlinarith [mul_pos hlambda hz]
  have hid : canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) =
      leftUpperHalfActualRadial z (lambda * z) := by
    rw [canonicalPureGap_leftUpper_radial_eq ha hab hb]
    unfold leftUpperHalfActualRadial
    ring
  rw [hid]
  linarith only [hquartic, (abs_le.mp herr).1]

theorem leftUpper_probability_positive {a b : ℝ}
    (ha : 5 / 11 ≤ a) (hab : a < b) (hb : b < 1 / 2) :
    0 < canonicalPureGap a (1 / 2) (H a) (H b) := by
  let z : ℝ := 1 / 2 - a
  let lambda : ℝ := (1 / 2 - b) / z
  have hz : 0 < z := by dsimp [z]; linarith
  have hzmax : z ≤ 1 / 22 := by dsimp [z]; linarith
  have hw : 0 < 1 / 2 - b := by linarith
  have hwz : 1 / 2 - b < z := by dsimp [z]; linarith
  have hlambda : 0 < lambda := div_pos hw hz
  have hlambda1 : lambda < 1 := (div_lt_one hz).2 hwz
  have hza : 1 / 2 - z = a := by dsimp [z]; ring
  have hzb : 1 / 2 - lambda * z = b := by
    dsimp [lambda]
    rw [div_mul_cancel₀ _ hz.ne']
    ring
  have hp := leftUpper_halfCollar_positive hz hzmax hlambda hlambda1
  rwa [hza, hzb] at hp

#print axioms leftUpper_J_half_bias_cubic_remainder
#print axioms leftUpper_entropy_half_bias_quartic_remainder
#print axioms leftUpper_eta_deficit_quadratic_remainder
#print axioms leftUpper_middle_eta_quartic_remainder
#print axioms leftUpper_F_contact_quartic_remainder
#print axioms leftUpper_F_half_bias_quartic_remainder
#print axioms leftUpper_halfCollar_actual_radial_error
#print axioms quartic_coefficient_lower
#print axioms leftUpper_halfCollar_positive
#print axioms leftUpper_probability_positive

end GeneralCK.ZeroCapLeftUpperWideHalfCollar

namespace GeneralCK

/-- Exact remaining left-upper obligation after the wider half collar.
The previously closed narrow rectangle remains excluded. -/
def LeftUpperOutsideWideHalfCollarAndNarrowOwner : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 / 2 → a < 5 / 11 →
    ¬ ((1 / 8 : ℝ) ≤ a ∧ a ≤ 129 / 1024 ∧
      129 / 1024 ≤ b ∧ b ≤ 65 / 512) →
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b)

theorem leftUpper_outsideHalfCollarAndNarrow_of_wide
    (h : LeftUpperOutsideWideHalfCollarAndNarrowOwner) :
    LeftUpperOutsideHalfCollarAndNarrowOwner := by
  intro a b ha hab hb _ha31 hrect
  by_cases hwide : 5 / 11 ≤ a
  · exact (ZeroCapLeftUpperWideHalfCollar.leftUpper_probability_positive hwide hab hb).le
  · exact h a b ha hab hb (lt_of_not_ge hwide) hrect

theorem leftUpper_outsideHalfCollarAndNarrow_iff_wide :
    LeftUpperOutsideHalfCollarAndNarrowOwner ↔ LeftUpperOutsideWideHalfCollarAndNarrowOwner := by
  constructor
  · intro h a b ha hab hb hawide hrect
    exact h a b ha hab hb (by linarith) hrect
  · exact leftUpper_outsideHalfCollarAndNarrow_of_wide

theorem zeroCap_leftUpper_of_outsideWideHalfCollarAndNarrow
    (h : LeftUpperOutsideWideHalfCollarAndNarrowOwner) :
    ∀ e f, 0 < e → e < f → f < 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f :=
  zeroCap_leftUpper_of_outsideHalfCollarAndNarrow
    (leftUpper_outsideHalfCollarAndNarrow_of_wide h)

#print axioms leftUpper_outsideHalfCollarAndNarrow_of_wide
#print axioms leftUpper_outsideHalfCollarAndNarrow_iff_wide
#print axioms zeroCap_leftUpper_of_outsideWideHalfCollarAndNarrow

end GeneralCK

end


