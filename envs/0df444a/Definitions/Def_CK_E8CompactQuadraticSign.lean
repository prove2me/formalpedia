-- Prove2me | Definitions.Def_CK_E8CompactQuadraticSign
-- name    : CK_E8CompactQuadraticSign
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:26:46.615906+00:00
-- url     : https://prove2.me/theorems/cfde5bd3-67cd-4de6-8ca9-2705a4c7d280
-- title:
--   Courtade–Kumar proof module `E8CompactQuadraticSign` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8CompactQuadraticSign` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8CompactQuadraticSign` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8CompactQuadraticSign (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8CompactQuadraticSign.lean)

import Definitions.Def_CK_E8RatioFactor

-- ===== source module E8CompactQuadraticSign =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8TAxisStableScalar
open Certificates.E8HistoricalLogConvexityBridge

noncomputable def tailLower (k : ℝ) : ℝ := (2 * k - 1) / (2 * k + 1)

/-- The only quadratic variable is the entropy quotient. -/
theorem compactFactor_complete_square (k t d : ℝ) :
    compactFactor k t d =
      6 * t * (d - (1 + 2 * (t / (2 * k - t)) - 3 / k) / 3) ^ 2 +
      (6 / k - 4 - 6 * (1 - t) * (t / (2 * k - t)) +
        t * (4 / 3 + 4 / 3 * (t / (2 * k - t)) +
          16 / 3 * (t / (2 * k - t)) ^ 2 -
          (4 + 2 * (t / (2 * k - t))) / k - 3 / k ^ 2)) := by
  simp only [compactFactor]
  ring

/-- Exact positive-denominator formula for the tail comparison. -/
theorem entropyQuotient_sub_tailLower {a : ℝ} (ha : 0 < a) :
    entropyQuotient a - tailLower (ell a) =
      4 * ((z a) ^ 2 * (2 * ell a ^ 2 - ell a * z a - 1) +
        (z a - l1 a) * (ell a * z a ^ 2 + ell a + z a)) /
      ((2 * ell a + 1) * (1 - z a) * (1 + z a) * h a) := by
  have h1 := (one_add_z_pos a).ne'
  have h2 : 1 - z a ≠ 0 := (sub_pos.mpr (z_lt_one ha)).ne'
  have h3 : ell a * 2 + 1 ≠ 0 := by linarith [ell_pos ha]
  have h4 := (h_pos ha).ne'
  have h3' : 1 + a * 2 + l1 a * 2 ≠ 0 := by
    have hp := ell_pos ha
    simp only [ell] at hp
    linarith
  simp only [entropyQuotient, tailLower, r]
  field_simp [h1, h2, h3, h4]
  field_simp [h3]
  simp only [h, ell]
  field_simp [h1, h3']
  ring

/-- A sharp first-order lower bound, using only `log (1+z) ≤ z`. -/
theorem tailLower_le_entropyQuotient {a : ℝ} (ha : 0 < a) (hk : 1 ≤ ell a) :
    tailLower (ell a) ≤ entropyQuotient a := by
  have hz0 := (z_pos a).le
  have hz1 := (z_lt_one ha).le
  have hlog : l1 a ≤ z a := by
    have hh := Real.log_le_sub_one_of_pos (one_add_z_pos a)
    simpa only [l1, add_sub_cancel_left] using hh
  have hquad : 0 ≤ 2 * ell a ^ 2 - ell a * z a - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hk),
      mul_nonneg (ell_pos ha).le (sub_nonneg.mpr hz1)]
  have hnum : 0 ≤ 4 * ((z a) ^ 2 * (2 * ell a ^ 2 - ell a * z a - 1) +
      (z a - l1 a) * (ell a * z a ^ 2 + ell a + z a)) := by
    positivity
  have hden : 0 < (2 * ell a + 1) * (1 - z a) * (1 + z a) * h a := by
    have he := ell_pos ha
    have hz := sub_pos.mpr (z_lt_one ha)
    have ho := one_add_z_pos a
    have hh := h_pos ha
    positivity
  have hh := div_nonneg hnum hden.le
  rw [← entropyQuotient_sub_tailLower ha] at hh
  linarith

/-- Once `k ≥ 3`, the compact factor is increasing above the tail lower bound. -/
theorem compactFactor_tailLower_le {k t d : ℝ} (hk : 3 ≤ k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd : tailLower k ≤ d) :
    compactFactor k t (tailLower k) ≤ compactFactor k t d := by
  have hk0 : 0 < k := by linarith
  have hden : 0 < 2 * k - t := by linarith
  have hwp : 0 ≤ t / (2 * k - t) := div_nonneg ht0 hden.le
  have hw : t / (2 * k - t) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hl : 2 / 3 ≤ tailLower k := by
    unfold tailLower
    apply (le_div_iff₀ (by linarith : 0 < 2 * k + 1)).mpr
    linarith
  have hi : 0 ≤ 3 / k := by positivity
  have hbr : 0 ≤ 6 * (d + tailLower k) -
      4 * (1 + 2 * (t / (2 * k - t)) - 3 / k) := by linarith
  have hid : compactFactor k t d - compactFactor k t (tailLower k) =
      t * (d - tailLower k) * (6 * (d + tailLower k) -
        4 * (1 + 2 * (t / (2 * k - t)) - 3 / k)) := by
    simp only [compactFactor]
    ring
  have hh : 0 ≤ compactFactor k t d - compactFactor k t (tailLower k) := by
    rw [hid]
    exact mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr hd)) hbr
  linarith

def tailP0 (k : ℝ) : ℝ := 16 * k ^ 4 - 48 * k ^ 3 + 48 * k ^ 2 - 4 * k + 3
def tailP1 (k : ℝ) : ℝ :=
  -64 * k ^ 6 + 80 * k ^ 5 - 24 * k ^ 4 - 12 * k ^ 3 - 130 * k ^ 2 + 6 * k - 9
def tailP2 (k : ℝ) : ℝ := -48 * k ^ 5 + 128 * k ^ 4 + 116 * k ^ 3 + 104 * k ^ 2 + 9
def tailP3 (k : ℝ) : ℝ := -40 * k ^ 4 - 32 * k ^ 3 - 22 * k ^ 2 - 2 * k - 3

/-- The comparison factor has just four coefficients in the small tail variable. -/
theorem compactFactor_tailLower_eq {k t : ℝ} (hk : 3 ≤ k) (ht : t ≤ 1) :
    compactFactor k t (tailLower k) =
      (tailP0 k + (1 - t) * tailP1 k + (1 - t) ^ 2 * tailP2 k +
        (1 - t) ^ 3 * tailP3 k) /
      (k ^ 2 * (2 * k - t) ^ 2 * (2 * k + 1) ^ 2) := by
  have hk0 : k ≠ 0 := by linarith
  have hkt : k * 2 - t ≠ 0 := by linarith
  have hk1 : k * 2 + 1 ≠ 0 := by linarith
  simp only [compactFactor, tailLower, tailP0, tailP1, tailP2, tailP3]
  field_simp [hk0, hkt, hk1]
  ring

theorem tailP0_lower {k : ℝ} (hk : 3 ≤ k) : 4 * k ^ 4 ≤ tailP0 k := by
  have hp : 0 ≤ k - 3 := by linarith
  have heq : tailP0 k - 4 * k ^ 4 =
      12 * (k - 3) ^ 4 + 96 * (k - 3) ^ 3 + 264 * (k - 3) ^ 2 +
        284 * (k - 3) + 99 := by unfold tailP0; ring
  have hh : 0 ≤ tailP0 k - 4 * k ^ 4 := by rw [heq]; positivity
  linarith

theorem tailP1_lower {k : ℝ} (hk : 3 ≤ k) : -70 * k ^ 6 ≤ tailP1 k := by
  have hp : 0 ≤ k - 3 := by linarith
  have heq : tailP1 k + 70 * k ^ 6 =
      6 * (k - 3) ^ 6 + 188 * (k - 3) ^ 5 + 1986 * (k - 3) ^ 4 +
        10140 * (k - 3) ^ 3 + 27356 * (k - 3) ^ 2 + 37458 * (k - 3) +
        20385 := by unfold tailP1; ring
  have hh : 0 ≤ tailP1 k + 70 * k ^ 6 := by rw [heq]; positivity
  linarith

theorem tailP2_lower {k : ℝ} (hk : 3 ≤ k) : -16 * k ^ 6 ≤ tailP2 k := by
  have hp : 0 ≤ k - 3 := by linarith
  have hk0 : 0 ≤ k := by linarith
  have heq : tailP2 k + 16 * k ^ 6 =
      16 * k ^ 5 * (k - 3) + 128 * k ^ 4 + 116 * k ^ 3 + 104 * k ^ 2 + 9 := by
    unfold tailP2
    ring
  have hh : 0 ≤ tailP2 k + 16 * k ^ 6 := by rw [heq]; positivity
  linarith

theorem tailP3_lower {k : ℝ} (hk : 3 ≤ k) : -6 * k ^ 6 ≤ tailP3 k := by
  have hp : 0 ≤ k - 3 := by linarith
  have heq : tailP3 k + 6 * k ^ 6 =
      6 * (k - 3) ^ 6 + 108 * (k - 3) ^ 5 + 770 * (k - 3) ^ 4 +
        2728 * (k - 3) ^ 3 + 4820 * (k - 3) ^ 2 + 3430 * (k - 3) + 63 := by
    unfold tailP3
    ring
  have hh : 0 ≤ tailP3 k + 6 * k ^ 6 := by rw [heq]; positivity
  linarith

/-- A compact rational sufficient condition for the entire unbounded tail. -/
theorem compactFactor_nonneg_of_tail_bounds {k t d : ℝ} (hk : 3 ≤ k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd : tailLower k ≤ d)
    (hsmall : (1 - t) * k ^ 2 ≤ 1 / 25) : 0 ≤ compactFactor k t d := by
  apply le_trans _ (compactFactor_tailLower_le hk ht0 ht1 hd)
  rw [compactFactor_tailLower_eq hk ht1]
  apply div_nonneg _ (by positivity)
  let q := 1 - t
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hq3 : q ^ 3 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hq2 hq0]
  have hp0 := tailP0_lower hk
  have hp1 := mul_le_mul_of_nonneg_left (tailP1_lower hk) hq0
  have hp2 := mul_le_mul_of_nonneg_left (tailP2_lower hk) (sq_nonneg q)
  have hp3 := mul_le_mul_of_nonneg_left (tailP3_lower hk) (pow_nonneg hq0 3)
  have hq26 := mul_le_mul_of_nonneg_right hq2 (pow_nonneg (by linarith : 0 ≤ k) 6)
  have hq36 := mul_le_mul_of_nonneg_right hq3 (pow_nonneg (by linarith : 0 ≤ k) 6)
  have hs := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (by linarith : 0 ≤ k) 4)
  change q * k ^ 2 * k ^ 4 ≤ (1 / 25 : ℝ) * k ^ 4 at hs
  change 0 ≤ tailP0 k + q * tailP1 k + q ^ 2 * tailP2 k + q ^ 3 * tailP3 k
  nlinarith [pow_nonneg (by linarith : 0 ≤ k) 4]

#print axioms tailLower_le_entropyQuotient
#print axioms compactFactor_tailLower_le
#print axioms compactFactor_nonneg_of_tail_bounds

theorem ell_basic_bounds {a : ℝ} (ha : 1 ≤ a) : a ≤ ell a ∧ ell a ≤ 2 * a := by
  have ha0 : 0 < a := by linarith
  have hz0 := z_pos a
  have hz1 := z_lt_one ha0
  have hl0 : 0 ≤ l1 a := Real.log_nonneg (by linarith)
  have hl1 : l1 a ≤ z a := by
    have hh := Real.log_le_sub_one_of_pos (one_add_z_pos a)
    simpa only [l1, add_sub_cancel_left] using hh
  dsimp [ell]
  constructor <;> linarith

theorem ell_le_add_one {a : ℝ} (ha : 0 < a) : ell a ≤ a + 1 := by
  have hl : l1 a ≤ z a := by
    have hh := Real.log_le_sub_one_of_pos (one_add_z_pos a)
    simpa only [l1, add_sub_cancel_left] using hh
  have hz := z_lt_one ha
  dsimp [ell]
  linarith

/-- A degree-seven exponential lower sum starts the analytic tail at four. -/
theorem exp_lower_of_four {a : ℝ} (ha : 4 ≤ a) : 10 * (a + 1) ≤ Real.exp a := by
  have ha0 : 0 ≤ a := by linarith
  have hp : 0 ≤ a - 4 := by linarith
  have ht := Real.sum_le_exp_of_nonneg ha0 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have heq : 1 + a + a ^ 2 / 2 + a ^ 3 / 6 + a ^ 4 / 24 + a ^ 5 / 120 +
      a ^ 6 / 720 + a ^ 7 / 5040 - 10 * (a + 1) =
      (a - 4) ^ 7 / 5040 + (a - 4) ^ 6 / 144 + (a - 4) ^ 5 * (13 / 120) +
        (a - 4) ^ 4 * (71 / 72) + (a - 4) ^ 3 * (103 / 18) +
        (a - 4) ^ 2 * (643 / 30) + (a - 4) * (347 / 9) + 569 / 315 := by ring
  have hh : 0 ≤ 1 + a + a ^ 2 / 2 + a ^ 3 / 6 + a ^ 4 / 24 + a ^ 5 / 120 +
      a ^ 6 / 720 + a ^ 7 / 5040 - 10 * (a + 1) := by rw [heq]; positivity
  linarith

/-- A coarse analytic exponential estimate is enough after `a = 12`. -/
theorem exp_double_lower_of_twelve {a : ℝ} (ha : 12 ≤ a) :
    400 * a ^ 2 ≤ Real.exp (2 * a) := by
  have ha0 : 0 ≤ a := by linarith
  have hs : 120 ≤ a ^ 2 := by nlinarith
  have hp := mul_nonneg ha0 (sub_nonneg.mpr hs)
  have ht := Real.pow_div_factorial_le_exp a ha0 3
  norm_num at ht
  have hlin : 20 * a ≤ Real.exp a := by nlinarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 20 * a) hlin
  rw [show 2 * a = a + a by ring, Real.exp_add]
  nlinarith

theorem stable_small_tail_of_twelve {a : ℝ} (ha : 12 ≤ a) :
    (1 - r a ^ 2) * ell a ^ 2 ≤ 1 / 25 := by
  have ha0 : 0 < a := by linarith
  have hb := ell_basic_bounds (by linarith : 1 ≤ a)
  have hk0 := (ell_pos ha0).le
  have hksq : ell a ^ 2 ≤ 4 * a ^ 2 := by nlinarith
  have hz0 := (z_pos a).le
  have hzexp : z a * Real.exp (2 * a) = 1 := by
    rw [z, ← Real.exp_add]
    norm_num
  have hexp := mul_le_mul_of_nonneg_left (exp_double_lower_of_twelve ha) hz0
  rw [hzexp] at hexp
  have hq : q a ≤ 4 * z a := by
    dsimp [q]
    apply (div_le_iff₀ (pow_pos (one_add_z_pos a) 2)).mpr
    nlinarith [mul_nonneg hz0 (sq_nonneg (z a))]
  have hmul := mul_le_mul hq hksq (sq_nonneg (ell a)) (by positivity : 0 ≤ 4 * z a)
  rw [one_sub_r_sq]
  nlinarith

/-- Unconditional sign on the whole unbounded tail. -/
theorem stableL_nonneg_of_twelve {a : ℝ} (ha : 12 ≤ a) : 0 ≤ stableL a := by
  have ha0 : 0 < a := by linarith
  have hk : 3 ≤ ell a := by
    have hh := (ell_basic_bounds (by linarith : 1 ≤ a)).1
    linarith
  rw [stableL_eq_compactFactor ha0]
  exact compactFactor_nonneg_of_tail_bounds hk (sq_nonneg _)
    (by nlinarith [r_pos ha0, r_lt_one a])
    (tailLower_le_entropyQuotient ha0 (by linarith))
    (stable_small_tail_of_twelve ha)

theorem tailCertificate_twelve : TailCertificate 12 :=
  tailCertificate_of_L_nonnegative (by norm_num) (fun _ ha => stableL_nonneg_of_twelve ha)

/-- Only a bounded scalar certificate remains after the analytic tail. -/
theorem largeSStructure_of_compactFactor_below_twelve
    (hcompact : ∀ a : ℝ, 0 < a → a < 12 →
      0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a)) : E8LargeSStructure := by
  apply largeSStructure_of_stableL_nonnegative
  intro a ha
  by_cases ht : a < 12
  · rw [stableL_eq_compactFactor ha]
    exact hcompact a ha ht
  · exact stableL_nonneg_of_twelve (le_of_not_gt ht)

#print axioms stable_small_tail_of_twelve
#print axioms stableL_nonneg_of_twelve
#print axioms tailCertificate_twelve
#print axioms largeSStructure_of_compactFactor_below_twelve

theorem stable_small_tail_of_four {a : ℝ} (ha : 4 ≤ a) :
    (1 - r a ^ 2) * ell a ^ 2 ≤ 1 / 25 := by
  have ha0 : 0 < a := by linarith
  have hk := ell_le_add_one ha0
  have hk0 := (ell_pos ha0).le
  have hksq : ell a ^ 2 ≤ (a + 1) ^ 2 := by nlinarith
  have hz0 := (z_pos a).le
  have hzexp : z a * Real.exp (2 * a) = 1 := by
    rw [z, ← Real.exp_add]
    norm_num
  have he : 100 * (a + 1) ^ 2 ≤ Real.exp (2 * a) := by
    have hsq := mul_self_le_mul_self
      (by positivity : 0 ≤ 10 * (a + 1)) (exp_lower_of_four ha)
    rw [show 2 * a = a + a by ring, Real.exp_add]
    nlinarith
  have hexp := mul_le_mul_of_nonneg_left he hz0
  rw [hzexp] at hexp
  have hq : q a ≤ 4 * z a := by
    dsimp [q]
    apply (div_le_iff₀ (pow_pos (one_add_z_pos a) 2)).mpr
    nlinarith [mul_nonneg hz0 (sq_nonneg (z a))]
  have hmul := mul_le_mul hq hksq (sq_nonneg (ell a)) (by positivity : 0 ≤ 4 * z a)
  rw [one_sub_r_sq]
  nlinarith

/-- The full tail sign starts at `a = 4`; no interval certificate is needed. -/
theorem stableL_nonneg_of_four {a : ℝ} (ha : 4 ≤ a) : 0 ≤ stableL a := by
  have ha0 : 0 < a := by linarith
  have hk : 3 ≤ ell a := by
    have hh := (ell_basic_bounds (by linarith : 1 ≤ a)).1
    linarith
  rw [stableL_eq_compactFactor ha0]
  exact compactFactor_nonneg_of_tail_bounds hk (sq_nonneg _)
    (by nlinarith [r_pos ha0, r_lt_one a])
    (tailLower_le_entropyQuotient ha0 (by linarith))
    (stable_small_tail_of_four ha)

theorem tailCertificate_four : TailCertificate 4 :=
  tailCertificate_of_L_nonnegative (by norm_num) (fun _ ha => stableL_nonneg_of_four ha)

theorem largeSStructure_of_compactFactor_below_four
    (hcompact : ∀ a : ℝ, 0 < a → a < 4 →
      0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a)) : E8LargeSStructure := by
  apply largeSStructure_of_stableL_nonnegative
  intro a ha
  by_cases ht : a < 4
  · rw [stableL_eq_compactFactor ha]
    exact hcompact a ha ht
  · exact stableL_nonneg_of_four (le_of_not_gt ht)

/-- Exact bounded replacement for the full-axis monotonicity question. -/
theorem ratio_monotone_iff_compactFactor_below_four :
    MonotoneOn ratio (Ioi 0) ↔ ∀ a : ℝ, 0 < a → a < 4 →
      0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a) := by
  constructor
  · intro hm a ha _
    exact ratio_monotone_iff_compactFactor_nonneg.mp hm a ha
  · intro hc
    apply ratio_monotone_iff_stableL_nonneg.mpr
    intro a ha
    by_cases ht : a < 4
    · rw [stableL_eq_compactFactor ha]
      exact hc a ha ht
    · exact stableL_nonneg_of_four (le_of_not_gt ht)

#print axioms exp_lower_of_four
#print axioms stable_small_tail_of_four
#print axioms stableL_nonneg_of_four
#print axioms tailCertificate_four
#print axioms largeSStructure_of_compactFactor_below_four
#print axioms ratio_monotone_iff_compactFactor_below_four

end GeneralCK.E8RatioMonotonicity

end


