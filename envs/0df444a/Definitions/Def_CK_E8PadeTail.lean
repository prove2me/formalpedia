-- Prove2me | Definitions.Def_CK_E8PadeTail
-- name    : CK_E8PadeTail
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:22:30.344281+00:00
-- url     : https://prove2.me/theorems/af477635-147d-4e9d-9ac1-e827e501c07b
-- title:
--   Courtade–Kumar proof module `E8PadeTail` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `E8PadeTail` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `E8PadeTail` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module E8PadeTail (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/E8PadeTail.lean)

import Definitions.Def_CK_E8PadeAnalyticHelpers

-- ===== source module E8PadeTail =====
section

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8TAxisStableScalar
open Certificates.E8HistoricalLogConvexityBridge

set_option maxHeartbeats 4000000

noncomputable def padeH (k u : ℝ) : ℝ :=
  4 * k * (1 + u) + (1 - u) * (2 + u)

noncomputable def padeG (k u : ℝ) : ℝ :=
  2 * k * (1 + u) ^ 2 - (1 - u) ^ 2

noncomputable def padeLower (k u : ℝ) : ℝ :=
  (1 + u) ^ 2 * (4 * k - u - 2) / ((1 - u) * padeH k u)

noncomputable def padeNumerator (k u : ℝ) : ℝ :=
  1 * ((3) * u ^ 10 + (-12) * u ^ 9 + (72) * u ^ 7 + (-126) * u ^ 6 + (252) * u ^ 4 + (-360) * u ^ 3 + (243) * u ^ 2 + (-84) * u + (12) * 1) +
  k * ((-16) * u ^ 10 + (-32) * u ^ 9 + (240) * u ^ 8 + (-72) * u ^ 7 + (-816) * u ^ 6 + (1032) * u ^ 5 + (192) * u ^ 4 + (-1080) * u ^ 3 + (672) * u ^ 2 + (-104) * u + (-16) * 1) +
  k ^ 2 * ((52) * u ^ 10 + (296) * u ^ 9 + (-64) * u ^ 8 + (-1624) * u ^ 7 + (536) * u ^ 6 + (2504) * u ^ 5 + (-1408) * u ^ 4 + (-808) * u ^ 3 + (692) * u ^ 2 + (-368) * u + (192) * 1) +
  k ^ 3 * ((-64) * u ^ 10 + (-912) * u ^ 9 + (-2400) * u ^ 8 + (688) * u ^ 7 + (4800) * u ^ 6 + (-528) * u ^ 5 + (-2336) * u ^ 4 + (2640) * u ^ 3 + (192) * u ^ 2 + (-1888) * u + (-192) * 1) +
  k ^ 4 * ((32) * u ^ 10 + (832) * u ^ 9 + (5568) * u ^ 8 + (11200) * u ^ 7 + (5312) * u ^ 6 + (-1344) * u ^ 5 + (9472) * u ^ 4 + (16448) * u ^ 3 + (7200) * u ^ 2 + (512) * u + (64) * 1) +
  k ^ 5 * ((-256) * u ^ 9 + (-3072) * u ^ 8 + (-12544) * u ^ 7 + (-22528) * u ^ 6 + (-17152) * u ^ 5 + (-1024) * u ^ 4 + (5376) * u ^ 3 + (2048) * u ^ 2) +
  k ^ 6 * ((512) * u ^ 8 + (3072) * u ^ 7 + (7680) * u ^ 6 + (10240) * u ^ 5 + (7680) * u ^ 4 + (3072) * u ^ 3 + (512) * u ^ 2)

noncomputable def padeCert0 (u : ℝ) : ℝ :=
  287501516223162 * u ^ 10 * 1 +
  77946056785716 * u ^ 9 * (1 - 20 * u) +
  8341658001288 * u ^ 8 * (1 - 20 * u) ^ 2 +
  604097335548 * u ^ 7 * (1 - 20 * u) ^ 3 +
  68650602156 * u ^ 6 * (1 - 20 * u) ^ 4 +
  8529928668 * u ^ 5 * (1 - 20 * u) ^ 5 +
  677296584 * u ^ 4 * (1 - 20 * u) ^ 6 +
  32319396 * u ^ 3 * (1 - 20 * u) ^ 7 +
  916650 * u ^ 2 * (1 - 20 * u) ^ 8 +
  14352 * u * (1 - 20 * u) ^ 9 +
  96 * 1 * (1 - 20 * u) ^ 10

noncomputable def padeCert1 (u : ℝ) : ℝ :=
  1452985022623390 * u ^ 10 * 1 +
  538835451044206 * u ^ 9 * (1 - 20 * u) +
  87327711743532 * u ^ 8 * (1 - 20 * u) ^ 2 +
  8182748402034 * u ^ 7 * (1 - 20 * u) ^ 3 +
  501838000092 * u ^ 6 * (1 - 20 * u) ^ 4 +
  22340752338 * u ^ 5 * (1 - 20 * u) ^ 5 +
  808952076 * u ^ 4 * (1 - 20 * u) ^ 6 +
  25121166 * u ^ 3 * (1 - 20 * u) ^ 7 +
  606606 * u ^ 2 * (1 - 20 * u) ^ 8 +
  9280 * u * (1 - 20 * u) ^ 9 +
  64 * 1 * (1 - 20 * u) ^ 10

noncomputable def padeCert2 (u : ℝ) : ℝ :=
  1782985829448369 * u ^ 10 * 1 +
  738403744996336 * u ^ 9 * (1 - 20 * u) +
  136721678755556 * u ^ 8 * (1 - 20 * u) ^ 2 +
  14945719509208 * u ^ 7 * (1 - 20 * u) ^ 3 +
  1073625384782 * u ^ 6 * (1 - 20 * u) ^ 4 +
  53406238936 * u ^ 5 * (1 - 20 * u) ^ 5 +
  1886621348 * u ^ 4 * (1 - 20 * u) ^ 6 +
  47485000 * u ^ 3 * (1 - 20 * u) ^ 7 +
  827849 * u ^ 2 * (1 - 20 * u) ^ 8 +
  9112 * u * (1 - 20 * u) ^ 9 +
  48 * 1 * (1 - 20 * u) ^ 10

noncomputable def padeCert3 (u : ℝ) : ℝ :=
  791700559866216 * u ^ 10 * 1 +
  341149962901230 * u ^ 9 * (1 - 20 * u) +
  66027989284716 * u ^ 8 * (1 - 20 * u) ^ 2 +
  7572264345046 * u ^ 7 * (1 - 20 * u) ^ 3 +
  571332186624 * u ^ 6 * (1 - 20 * u) ^ 4 +
  29742487326 * u ^ 5 * (1 - 20 * u) ^ 5 +
  1087088372 * u ^ 4 * (1 - 20 * u) ^ 6 +
  27705546 * u ^ 3 * (1 - 20 * u) ^ 7 +
  474144 * u ^ 2 * (1 - 20 * u) ^ 8 +
  4948 * u * (1 - 20 * u) ^ 9 +
  24 * 1 * (1 - 20 * u) ^ 10

noncomputable def padeCert4 (u : ℝ) : ℝ :=
  135011897113842 * u ^ 10 * 1 +
  58167107863452 * u ^ 9 * (1 - 20 * u) +
  11258762890788 * u ^ 8 * (1 - 20 * u) ^ 2 +
  1291461103060 * u ^ 7 * (1 - 20 * u) ^ 3 +
  97457465572 * u ^ 6 * (1 - 20 * u) ^ 4 +
  5072446116 * u ^ 5 * (1 - 20 * u) ^ 5 +
  185212232 * u ^ 4 * (1 - 20 * u) ^ 6 +
  4709228 * u ^ 3 * (1 - 20 * u) ^ 7 +
  80250 * u ^ 2 * (1 - 20 * u) ^ 8 +
  832 * u * (1 - 20 * u) ^ 9 +
  4 * 1 * (1 - 20 * u) ^ 10

noncomputable def padeCert5 (u : ℝ) : ℝ :=
  6789689555040 * u ^ 10 * 1 +
  2635035960312 * u ^ 9 * (1 - 20 * u) +
  447384642768 * u ^ 8 * (1 - 20 * u) ^ 2 +
  43402772952 * u ^ 7 * (1 - 20 * u) ^ 3 +
  2631563856 * u ^ 6 * (1 - 20 * u) ^ 4 +
  102110504 * u ^ 5 * (1 - 20 * u) ^ 5 +
  2476208 * u ^ 4 * (1 - 20 * u) ^ 6 +
  34312 * u ^ 3 * (1 - 20 * u) ^ 7 +
  208 * u ^ 2 * (1 - 20 * u) ^ 8

noncomputable def padeCert6 (u : ℝ) : ℝ :=
  274451587200 * u ^ 10 * 1 +
  105859897920 * u ^ 9 * (1 - 20 * u) +
  17862690888 * u ^ 8 * (1 - 20 * u) ^ 2 +
  1722249648 * u ^ 7 * (1 - 20 * u) ^ 3 +
  103776120 * u ^ 6 * (1 - 20 * u) ^ 4 +
  4001760 * u ^ 5 * (1 - 20 * u) ^ 5 +
  96440 * u ^ 4 * (1 - 20 * u) ^ 6 +
  1328 * u ^ 3 * (1 - 20 * u) ^ 7 +
  8 * u ^ 2 * (1 - 20 * u) ^ 8

theorem padeNumerator_certificate (k u : ℝ) :
    padeNumerator k u =
      (1 * padeCert0 u +
        (2 * k - 3) * padeCert1 u +
        (2 * k - 3) ^ 2 * padeCert2 u +
        (2 * k - 3) ^ 3 * padeCert3 u +
        (2 * k - 3) ^ 4 * padeCert4 u +
        (2 * k - 3) ^ 5 * padeCert5 u +
        (2 * k - 3) ^ 6 * padeCert6 u) / 1 := by
  simp only [padeNumerator, padeCert0, padeCert1, padeCert2, padeCert3, padeCert4, padeCert5, padeCert6]
  ring

theorem padeNumerator_nonneg {k u : ℝ} (hk : 3 / 2 ≤ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 20) : 0 ≤ padeNumerator k u := by
  have hkp : 0 ≤ 2 * k - 3 := by linarith
  have hup : 0 ≤ 1 - 20 * u := by linarith
  rw [padeNumerator_certificate]
  simp only [padeCert0, padeCert1, padeCert2, padeCert3, padeCert4, padeCert5, padeCert6]
  positivity

#print axioms padeNumerator_nonneg

theorem padeH_pos {k u : ℝ} (hk : 3 / 2 ≤ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 20) : 0 < padeH k u := by
  have hk0 : 0 < k := by linarith
  have hu : 0 < 1 - u := by linarith
  unfold padeH
  positivity

theorem padeG_pos {k u : ℝ} (hk : 3 / 2 ≤ k)
    (hu0 : 0 ≤ u) : 0 < padeG k u := by
  have hk0 : 0 < 2 * k - 1 := by linarith
  have hid : padeG k u = (2 * k - 1) * (1 + u) ^ 2 + 4 * u := by
    unfold padeG
    ring
  rw [hid]
  positivity

theorem compactFactor_padeLower_eq {k u : ℝ} (hk : 3 / 2 ≤ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 20) :
    compactFactor k (((1 - u) / (1 + u)) ^ 2) (padeLower k u) =
      padeNumerator k u / (k ^ 2 * (1 + u) ^ 2 * padeH k u ^ 2 * padeG k u ^ 2) := by
  have hk0 : k ≠ 0 := by linarith
  have huP : 1 + u ≠ 0 := by linarith
  have huM : 1 - u ≠ 0 := by linarith
  have hH := (padeH_pos hk hu0 hu1).ne'
  have hG := (padeG_pos hk hu0).ne'
  have hG' : k * (1 + u) ^ 2 * 2 - (1 - u) ^ 2 ≠ 0 := by
    convert hG using 1
    unfold padeG
    ring
  have hw : (((1 - u) / (1 + u)) ^ 2) /
      (2 * k - ((1 - u) / (1 + u)) ^ 2) = (1 - u) ^ 2 / padeG k u := by
    unfold padeG
    field_simp [huP, hG']
  simp only [compactFactor, hw, padeLower]
  field_simp [hk0, huP, huM, hH, hG]
  simp only [padeH, padeG, padeNumerator]
  ring

theorem compactFactor_padeLower_nonneg {k u : ℝ} (hk : 3 / 2 ≤ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 20) :
    0 ≤ compactFactor k (((1 - u) / (1 + u)) ^ 2) (padeLower k u) := by
  rw [compactFactor_padeLower_eq hk hu0 hu1]
  exact div_nonneg (padeNumerator_nonneg hk hu0 hu1) (by positivity)

theorem half_le_padeLower {k u : ℝ} (hk : 3 / 2 ≤ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 20) : 1 / 2 ≤ padeLower k u := by
  have huM : 0 < 1 - u := by linarith
  unfold padeLower
  apply (le_div_iff₀ (mul_pos huM (padeH_pos hk hu0 hu1))).mpr
  simp only [padeH]
  have hp : 0 ≤ k - 3 / 2 := by linarith
  have hp2 := mul_nonneg hp (sq_nonneg u)
  have hp1 := mul_nonneg hp hu0
  have hu3 := mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ 1 - u)
  nlinarith

theorem compactFactor_mono_above_half {k t d₀ d : ℝ} (hk : 3 / 2 ≤ k)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd₀ : 1 / 2 ≤ d₀) (hd : d₀ ≤ d) :
    compactFactor k t d₀ ≤ compactFactor k t d := by
  have hk0 : 0 < k := by linarith
  have hden : 0 < 2 * k - t := by linarith
  have hw : t / (2 * k - t) ≤ 3 / (2 * k) := by
    apply (div_le_div_iff₀ hden (by positivity : 0 < 2 * k)).mpr
    nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr ht1)]
  have heq : 2 * (3 / (2 * k)) = 3 / k := by field_simp
  have hbr : 0 ≤ 6 * (d + d₀) -
      4 * (1 + 2 * (t / (2 * k - t)) - 3 / k) := by linarith
  have hid : compactFactor k t d - compactFactor k t d₀ =
      t * (d - d₀) * (6 * (d + d₀) -
        4 * (1 + 2 * (t / (2 * k - t)) - 3 / k)) := by
    simp only [compactFactor]
    ring
  have hh : 0 ≤ compactFactor k t d - compactFactor k t d₀ := by
    rw [hid]
    exact mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr hd)) hbr
  linarith

#print axioms compactFactor_padeLower_nonneg
#print axioms half_le_padeLower
#print axioms compactFactor_mono_above_half

theorem entropyQuotient_sub_padeLower {a : ℝ} (ha : 0 < a)
    (hk : 3 / 2 ≤ ell a) (hz : z a ≤ 1 / 20) :
    entropyQuotient a - padeLower (ell a) (z a) =
      8 * ell a * (1 + z a) *
        (z a * (2 + z a) / (2 * (1 + z a)) - l1 a) /
      ((1 - z a) * h a * padeH (ell a) (z a)) := by
  have h1 := (one_add_z_pos a).ne'
  have h2 : 1 - z a ≠ 0 := (sub_pos.mpr (z_lt_one ha)).ne'
  have h4 := (h_pos ha).ne'
  have hH := (padeH_pos hk (z_pos a).le hz).ne'
  simp only [entropyQuotient, padeLower, r]
  field_simp [h1, h2, h4, hH]
  simp only [padeH, h, ell]
  field_simp [h1]
  ring

theorem padeLower_le_entropyQuotient_of_log_bound {a : ℝ} (ha : 0 < a)
    (hk : 3 / 2 ≤ ell a) (hz : z a ≤ 1 / 20)
    (hlog : l1 a ≤ z a * (2 + z a) / (2 * (1 + z a))) :
    padeLower (ell a) (z a) ≤ entropyQuotient a := by
  have he := (ell_pos ha).le
  have hzP := one_add_z_pos a
  have hzM := sub_pos.mpr (z_lt_one ha)
  have hh := h_pos ha
  have hH := padeH_pos hk (z_pos a).le hz
  have hnum : 0 ≤ 8 * ell a * (1 + z a) *
      (z a * (2 + z a) / (2 * (1 + z a)) - l1 a) := by positivity
  have hden : 0 ≤ (1 - z a) * h a * padeH (ell a) (z a) := by positivity
  have hdiff := div_nonneg hnum hden
  rw [← entropyQuotient_sub_padeLower ha hk hz] at hdiff
  linarith

theorem stableL_nonneg_of_pade_bounds {a : ℝ} (ha : 0 < a)
    (hk : 3 / 2 ≤ ell a) (hz : z a ≤ 1 / 20)
    (hlog : l1 a ≤ z a * (2 + z a) / (2 * (1 + z a))) : 0 ≤ stableL a := by
  rw [stableL_eq_compactFactor ha]
  have hpoly := compactFactor_padeLower_nonneg hk (z_pos a).le hz
  change 0 ≤ compactFactor (ell a) (r a ^ 2) (padeLower (ell a) (z a)) at hpoly
  exact hpoly.trans (compactFactor_mono_above_half hk (sq_nonneg _)
    (by nlinarith [r_pos ha, r_lt_one a])
    (half_le_padeLower hk (z_pos a).le hz)
    (padeLower_le_entropyQuotient_of_log_bound ha hk hz hlog))

#print axioms entropyQuotient_sub_padeLower
#print axioms padeLower_le_entropyQuotient_of_log_bound
#print axioms stableL_nonneg_of_pade_bounds

/-- Unconditional Padé tail: all positive parameters at least `3/2`. -/
theorem stableL_nonneg_of_three_halves {a : ℝ} (ha : 3 / 2 ≤ a) : 0 ≤ stableL a := by
  have ha0 : 0 < a := by linarith
  have hk : 3 / 2 ≤ ell a := by
    have hh := (ell_basic_bounds (by linarith : 1 ≤ a)).1
    linarith
  apply stableL_nonneg_of_pade_bounds ha0 hk (z_le_one_twentieth_of_three_halves ha)
  exact log_one_add_le_pade (z_pos a).le

theorem tailCertificate_three_halves : TailCertificate (3 / 2) :=
  tailCertificate_of_L_nonnegative (by norm_num)
    (fun _ ha => stableL_nonneg_of_three_halves ha)

theorem ratio_monotone_iff_compactFactor_below_three_halves :
    MonotoneOn ratio (Ioi 0) ↔ ∀ a : ℝ, 0 < a → a < 3 / 2 →
      0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a) := by
  constructor
  · intro hm a ha _
    exact ratio_monotone_iff_compactFactor_nonneg.mp hm a ha
  · intro hc
    apply ratio_monotone_iff_stableL_nonneg.mpr
    intro a ha
    by_cases ht : a < 3 / 2
    · rw [stableL_eq_compactFactor ha]
      exact hc a ha ht
    · exact stableL_nonneg_of_three_halves (le_of_not_gt ht)

theorem largeSStructure_of_compactFactor_below_three_halves
    (hcompact : ∀ a : ℝ, 0 < a → a < 3 / 2 →
      0 ≤ compactFactor (ell a) (r a ^ 2) (entropyQuotient a)) : E8LargeSStructure :=
  largeSStructure_of_ratio_monotone
    (ratio_monotone_iff_compactFactor_below_three_halves.mpr hcompact)

#print axioms stableL_nonneg_of_three_halves
#print axioms tailCertificate_three_halves
#print axioms ratio_monotone_iff_compactFactor_below_three_halves
#print axioms largeSStructure_of_compactFactor_below_three_halves

end GeneralCK.E8RatioMonotonicity

end


