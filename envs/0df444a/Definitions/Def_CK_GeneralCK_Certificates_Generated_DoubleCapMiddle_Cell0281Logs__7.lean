-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0281Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0281Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:35:01.08841+00:00
-- url     : https://prove2.me/theorems/de4c8d3e-94cd-4721-967a-a610d1ddc267
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0281Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0282Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0281Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0282Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0283Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0284Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0285Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0286Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0287Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0281Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0282Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0283Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0284Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0285Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0286Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0287Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0281Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0282Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0283Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0284Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0285Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0286Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0287Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0281Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0282Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0283Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0284Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0285Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0286Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0287Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0281Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0281
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (228597401 / 1000000000) ≤ -Real.log (1024 / 1287) ∧
    -Real.log (1024 / 1287) ≤ (114298701 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2311)) (n := 12)
    (lo := (228597401 / 1000000000)) (hi := (114298701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287 / 1024) = 1/(1024 / 1287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (228597401 / 1000000000) (114298701 / 500000000) (Real.log (1287 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1287 / 1024) = -Real.log (1024 / 1287) := by
    rw [show ((1287 / 1024) : ℝ) = ((1024 / 1287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (296838447 / 1000000000) ≤ -Real.log (761 / 1024) ∧
    -Real.log (761 / 1024) ≤ (18552403 / 62500000) := by
  have h := checkLog_sound (w := (263 / 1785)) (n := 12)
    (lo := (296838447 / 1000000000)) (hi := (18552403 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 761) = 1/(761 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18552403 / 62500000) (-296838447 / 1000000000) (Real.log (761 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (57032773 / 250000000) ≤ -Real.log (160 / 201) ∧
    -Real.log (160 / 201) ≤ (228131093 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 361)) (n := 12)
    (lo := (57032773 / 250000000)) (hi := (228131093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201 / 160) = 1/(160 / 201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (57032773 / 250000000) (228131093 / 1000000000) (Real.log (201 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201 / 160) = -Real.log (160 / 201) := by
    rw [show ((201 / 160) : ℝ) = ((160 / 201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (148025161 / 500000000) ≤ -Real.log (119 / 160) ∧
    -Real.log (119 / 160) ≤ (296050323 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 279)) (n := 12)
    (lo := (148025161 / 500000000)) (hi := (296050323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 119) = 1/(119 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-296050323 / 1000000000) (-148025161 / 500000000) (Real.log (119 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103634601 / 250000000) ≤ -Real.log (512 / 775) ∧
    -Real.log (512 / 775) ≤ (82907681 / 200000000) := by
  have h := checkLog_sound (w := (263 / 1287)) (n := 12)
    (lo := (103634601 / 250000000)) (hi := (82907681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775 / 512) = 1/(512 / 775) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103634601 / 250000000) (82907681 / 200000000) (Real.log (775 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (775 / 512) = -Real.log (512 / 775) := by
    rw [show ((775 / 512) : ℝ) = ((512 / 775) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (45054483 / 62500000) ≤ -Real.log (249 / 512) ∧
    -Real.log (249 / 512) ≤ (72087173 / 100000000) := by
  have h := checkLog_sound (w := (7 / 505)) (n := 12)
    (lo := (6931137 / 250000000)) (hi := (27724549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 249) = 1/(249 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-72087173 / 100000000) (-45054483 / 62500000) (Real.log (249 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (312518333 / 1000000000) ≤ -Real.log (1000000 / 1366863) ∧
    -Real.log (1000000 / 1366863) ≤ (156259167 / 500000000) := by
  have h := checkLog_sound (w := (366863 / 2366863)) (n := 12)
    (lo := (312518333 / 1000000000)) (hi := (156259167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366863 / 1000000) = 1/(1000000 / 1366863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (312518333 / 1000000000) (156259167 / 500000000) (Real.log (1366863 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1366863 / 1000000) = -Real.log (1000000 / 1366863) := by
    rw [show ((1366863 / 1000000) : ℝ) = ((1000000 / 1366863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9141369 / 20000000) ≤ -Real.log (633137 / 1000000) ∧
    -Real.log (633137 / 1000000) ≤ (457068451 / 1000000000) := by
  have h := checkLog_sound (w := (366863 / 1633137)) (n := 12)
    (lo := (9141369 / 20000000)) (hi := (457068451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633137) = 1/(633137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-457068451 / 1000000000) (-9141369 / 20000000) (Real.log (633137 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156574753 / 500000000) ≤ -Real.log (500000 / 683863) ∧
    -Real.log (500000 / 683863) ≤ (313149507 / 1000000000) := by
  have h := checkLog_sound (w := (183863 / 1183863)) (n := 12)
    (lo := (156574753 / 500000000)) (hi := (313149507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683863 / 500000) = 1/(500000 / 683863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156574753 / 500000000) (313149507 / 1000000000) (Real.log (683863 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (683863 / 500000) = -Real.log (500000 / 683863) := by
    rw [show ((683863 / 500000) : ℝ) = ((500000 / 683863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (229216217 / 500000000) ≤ -Real.log (316137 / 500000) ∧
    -Real.log (316137 / 500000) ≤ (91686487 / 200000000) := by
  have h := checkLog_sound (w := (183863 / 816137)) (n := 12)
    (lo := (229216217 / 500000000)) (hi := (91686487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 316137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 316137) = 1/(316137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91686487 / 200000000) (-229216217 / 500000000) (Real.log (316137 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (238577433 / 1000000000) ≤ -Real.log (500000 / 634721) ∧
    -Real.log (500000 / 634721) ≤ (119288717 / 500000000) := by
  have h := checkLog_sound (w := (134721 / 1134721)) (n := 12)
    (lo := (238577433 / 1000000000)) (hi := (119288717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634721 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634721 / 500000) = 1/(500000 / 634721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (238577433 / 1000000000) (119288717 / 500000000) (Real.log (634721 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (634721 / 500000) = -Real.log (500000 / 634721) := by
    rw [show ((634721 / 500000) : ℝ) = ((500000 / 634721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (313946653 / 1000000000) ≤ -Real.log (365279 / 500000) ∧
    -Real.log (365279 / 500000) ≤ (156973327 / 500000000) := by
  have h := checkLog_sound (w := (134721 / 865279)) (n := 12)
    (lo := (313946653 / 1000000000)) (hi := (156973327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365279) = 1/(365279 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-156973327 / 500000000) (-313946653 / 1000000000) (Real.log (365279 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59779027 / 250000000) ≤ -Real.log (500000 / 635063) ∧
    -Real.log (500000 / 635063) ≤ (239116109 / 1000000000) := by
  have h := checkLog_sound (w := (135063 / 1135063)) (n := 12)
    (lo := (59779027 / 250000000)) (hi := (239116109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635063 / 500000) = 1/(500000 / 635063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59779027 / 250000000) (239116109 / 1000000000) (Real.log (635063 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (635063 / 500000) = -Real.log (500000 / 635063) := by
    rw [show ((635063 / 500000) : ℝ) = ((500000 / 635063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (157441681 / 500000000) ≤ -Real.log (364937 / 500000) ∧
    -Real.log (364937 / 500000) ≤ (314883363 / 1000000000) := by
  have h := checkLog_sound (w := (135063 / 864937)) (n := 12)
    (lo := (157441681 / 500000000)) (hi := (314883363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364937) = 1/(364937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-314883363 / 1000000000) (-157441681 / 500000000) (Real.log (364937 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (769586783 / 1000000000) ≤ -Real.log (500000000000 / 1079436993889) ∧
    -Real.log (500000000000 / 1079436993889) ≤ (153917357 / 200000000) := by
  have h := checkLog_sound (w := (79436993889 / 2079436993889)) (n := 12)
    (lo := (76439603 / 1000000000)) (hi := (19109901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079436993889 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1079436993889 / 1000000000000) = 1/(500000000000 / 1079436993889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (769586783 / 1000000000) (153917357 / 200000000) (Real.log (1079436993889 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1079436993889 / 500000000000) = -Real.log (500000000000 / 1079436993889) := by
    rw [show ((1079436993889 / 500000000000) : ℝ) = ((500000000000 / 1079436993889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38579097 / 50000000) ≤ -Real.log (125000000000 / 270398197617) ∧
    -Real.log (125000000000 / 270398197617) ≤ (385790971 / 500000000) := by
  have h := checkLog_sound (w := (20398197617 / 520398197617)) (n := 12)
    (lo := (1960869 / 25000000)) (hi := (78434761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270398197617 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270398197617 / 250000000000) = 1/(125000000000 / 270398197617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38579097 / 50000000) (385790971 / 500000000) (Real.log (270398197617 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (270398197617 / 125000000000) = -Real.log (125000000000 / 270398197617) := by
    rw [show ((270398197617 / 125000000000) : ℝ) = ((125000000000 / 270398197617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (552524087 / 1000000000) ≤ -Real.log (488281250 / 848453821) ∧
    -Real.log (488281250 / 848453821) ≤ (69065511 / 125000000) := by
  have h := checkLog_sound (w := (360172571 / 1336735071)) (n := 12)
    (lo := (552524087 / 1000000000)) (hi := (69065511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848453821 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848453821 / 488281250) = 1/(488281250 / 848453821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (552524087 / 1000000000) (69065511 / 125000000) (Real.log (848453821 / 488281250)) := by
  have h := reflection_log_19_neg
  have he : Real.log (848453821 / 488281250) = -Real.log (488281250 / 848453821) := by
    rw [show ((848453821 / 488281250) : ℝ) = ((488281250 / 848453821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (55399947 / 100000000) ≤ -Real.log (250000000000 / 435049748313) ∧
    -Real.log (250000000000 / 435049748313) ≤ (553999471 / 1000000000) := by
  have h := checkLog_sound (w := (185049748313 / 685049748313)) (n := 12)
    (lo := (55399947 / 100000000)) (hi := (553999471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((435049748313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(435049748313 / 250000000000) = 1/(250000000000 / 435049748313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (55399947 / 100000000) (553999471 / 1000000000) (Real.log (435049748313 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (435049748313 / 250000000000) = -Real.log (250000000000 / 435049748313) := by
    rw [show ((435049748313 / 250000000000) : ℝ) = ((250000000000 / 435049748313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0281

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0282Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0282
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (57032773 / 250000000) ≤ -Real.log (160 / 201) ∧
    -Real.log (160 / 201) ≤ (228131093 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 361)) (n := 12)
    (lo := (57032773 / 250000000)) (hi := (228131093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201 / 160) = 1/(160 / 201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (57032773 / 250000000) (228131093 / 1000000000) (Real.log (201 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201 / 160) = -Real.log (160 / 201) := by
    rw [show ((201 / 160) : ℝ) = ((160 / 201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (148025161 / 500000000) ≤ -Real.log (119 / 160) ∧
    -Real.log (119 / 160) ≤ (296050323 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 279)) (n := 12)
    (lo := (148025161 / 500000000)) (hi := (296050323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 119) = 1/(119 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-296050323 / 1000000000) (-148025161 / 500000000) (Real.log (119 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (445113 / 1953125) ≤ -Real.log (10240 / 12861) ∧
    -Real.log (10240 / 12861) ≤ (227897857 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 23101)) (n := 12)
    (lo := (445113 / 1953125)) (hi := (227897857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12861 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12861 / 10240) = 1/(10240 / 12861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (445113 / 1953125) (227897857 / 1000000000) (Real.log (12861 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12861 / 10240) = -Real.log (10240 / 12861) := by
    rw [show ((12861 / 10240) : ℝ) = ((10240 / 12861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73914123 / 250000000) ≤ -Real.log (7619 / 10240) ∧
    -Real.log (7619 / 10240) ≤ (295656493 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 17859)) (n := 12)
    (lo := (73914123 / 250000000)) (hi := (295656493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7619) = 1/(7619 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-295656493 / 1000000000) (-73914123 / 250000000) (Real.log (7619 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (413376439 / 1000000000) ≤ -Real.log (5120 / 7741) ∧
    -Real.log (5120 / 7741) ≤ (10334411 / 25000000) := by
  have h := checkLog_sound (w := (2621 / 12861)) (n := 12)
    (lo := (413376439 / 1000000000)) (hi := (10334411 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7741 / 5120) = 1/(5120 / 7741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (413376439 / 1000000000) (10334411 / 25000000) (Real.log (7741 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7741 / 5120) = -Real.log (5120 / 7741) := by
    rw [show ((7741 / 5120) : ℝ) = ((5120 / 7741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (358631893 / 500000000) ≤ -Real.log (2499 / 5120) ∧
    -Real.log (2499 / 5120) ≤ (179315947 / 250000000) := by
  have h := checkLog_sound (w := (61 / 5059)) (n := 12)
    (lo := (12058303 / 500000000)) (hi := (24116607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2499) = 1/(2499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-179315947 / 250000000) (-358631893 / 500000000) (Real.log (2499 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156101481 / 500000000) ≤ -Real.log (31250 / 42701) ∧
    -Real.log (31250 / 42701) ≤ (312202963 / 1000000000) := by
  have h := checkLog_sound (w := (11451 / 73951)) (n := 12)
    (lo := (156101481 / 500000000)) (hi := (312202963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42701 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42701 / 31250) = 1/(31250 / 42701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156101481 / 500000000) (312202963 / 1000000000) (Real.log (42701 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (42701 / 31250) = -Real.log (31250 / 42701) := by
    rw [show ((42701 / 31250) : ℝ) = ((31250 / 42701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57048493 / 125000000) ≤ -Real.log (19799 / 31250) ∧
    -Real.log (19799 / 31250) ≤ (91277589 / 200000000) := by
  have h := checkLog_sound (w := (11451 / 51049)) (n := 12)
    (lo := (57048493 / 125000000)) (hi := (91277589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 19799) = 1/(19799 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91277589 / 200000000) (-57048493 / 125000000) (Real.log (19799 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (39064883 / 125000000) ≤ -Real.log (62500 / 85429) ∧
    -Real.log (62500 / 85429) ≤ (62503813 / 200000000) := by
  have h := checkLog_sound (w := (22929 / 147929)) (n := 12)
    (lo := (39064883 / 125000000)) (hi := (62503813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85429 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85429 / 62500) = 1/(62500 / 85429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (39064883 / 125000000) (62503813 / 200000000) (Real.log (85429 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (85429 / 62500) = -Real.log (62500 / 85429) := by
    rw [show ((85429 / 62500) : ℝ) = ((62500 / 85429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (457070029 / 1000000000) ≤ -Real.log (39571 / 62500) ∧
    -Real.log (39571 / 62500) ≤ (45707003 / 100000000) := by
  have h := checkLog_sound (w := (22929 / 102071)) (n := 12)
    (lo := (457070029 / 1000000000)) (hi := (45707003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 39571) = 1/(39571 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-45707003 / 100000000) (-457070029 / 1000000000) (Real.log (39571 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9532351 / 40000000) ≤ -Real.log (1000000 / 1269101) ∧
    -Real.log (1000000 / 1269101) ≤ (29788597 / 125000000) := by
  have h := checkLog_sound (w := (269101 / 2269101)) (n := 12)
    (lo := (9532351 / 40000000)) (hi := (29788597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269101 / 1000000) = 1/(1000000 / 1269101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9532351 / 40000000) (29788597 / 125000000) (Real.log (1269101 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1269101 / 1000000) = -Real.log (1000000 / 1269101) := by
    rw [show ((1269101 / 1000000) : ℝ) = ((1000000 / 1269101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (62695999 / 200000000) ≤ -Real.log (730899 / 1000000) ∧
    -Real.log (730899 / 1000000) ≤ (78369999 / 250000000) := by
  have h := checkLog_sound (w := (269101 / 1730899)) (n := 12)
    (lo := (62695999 / 200000000)) (hi := (78369999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730899) = 1/(730899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78369999 / 250000000) (-62695999 / 200000000) (Real.log (730899 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (238578221 / 1000000000) ≤ -Real.log (1000000 / 1269443) ∧
    -Real.log (1000000 / 1269443) ≤ (119289111 / 500000000) := by
  have h := checkLog_sound (w := (269443 / 2269443)) (n := 12)
    (lo := (238578221 / 1000000000)) (hi := (119289111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269443 / 1000000) = 1/(1000000 / 1269443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (238578221 / 1000000000) (119289111 / 500000000) (Real.log (1269443 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1269443 / 1000000) = -Real.log (1000000 / 1269443) := by
    rw [show ((1269443 / 1000000) : ℝ) = ((1000000 / 1269443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (156974011 / 500000000) ≤ -Real.log (730557 / 1000000) ∧
    -Real.log (730557 / 1000000) ≤ (313948023 / 1000000000) := by
  have h := checkLog_sound (w := (269443 / 1730557)) (n := 12)
    (lo := (156974011 / 500000000)) (hi := (313948023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730557) = 1/(730557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-313948023 / 1000000000) (-156974011 / 500000000) (Real.log (730557 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (768590907 / 1000000000) ≤ -Real.log (250000000000 / 539181271781) ∧
    -Real.log (250000000000 / 539181271781) ≤ (768590909 / 1000000000) := by
  have h := checkLog_sound (w := (39181271781 / 1039181271781)) (n := 12)
    (lo := (75443727 / 1000000000)) (hi := (4715233 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539181271781 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(539181271781 / 500000000000) = 1/(250000000000 / 539181271781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (768590907 / 1000000000) (768590909 / 1000000000) (Real.log (539181271781 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (539181271781 / 250000000000) = -Real.log (250000000000 / 539181271781) := by
    rw [show ((539181271781 / 250000000000) : ℝ) = ((250000000000 / 539181271781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (384794547 / 500000000) ≤ -Real.log (100000000000 / 215887897703) ∧
    -Real.log (100000000000 / 215887897703) ≤ (96198637 / 125000000) := by
  have h := checkLog_sound (w := (15887897703 / 415887897703)) (n := 12)
    (lo := (38220957 / 500000000)) (hi := (15288383 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215887897703 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(215887897703 / 200000000000) = 1/(100000000000 / 215887897703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (384794547 / 500000000) (96198637 / 125000000) (Real.log (215887897703 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (215887897703 / 100000000000) = -Real.log (100000000000 / 215887897703) := by
    rw [show ((215887897703 / 100000000000) : ℝ) = ((100000000000 / 215887897703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (551788771 / 1000000000) ≤ -Real.log (250000000000 / 434089046503) ∧
    -Real.log (250000000000 / 434089046503) ≤ (137947193 / 250000000) := by
  have h := checkLog_sound (w := (184089046503 / 684089046503)) (n := 12)
    (lo := (551788771 / 1000000000)) (hi := (137947193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434089046503 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434089046503 / 250000000000) = 1/(250000000000 / 434089046503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (551788771 / 1000000000) (137947193 / 250000000) (Real.log (434089046503 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (434089046503 / 250000000000) = -Real.log (250000000000 / 434089046503) := by
    rw [show ((434089046503 / 250000000000) : ℝ) = ((250000000000 / 434089046503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (552526243 / 1000000000) ≤ -Real.log (500000000000 / 868818586367) ∧
    -Real.log (500000000000 / 868818586367) ≤ (138131561 / 250000000) := by
  have h := checkLog_sound (w := (368818586367 / 1368818586367)) (n := 12)
    (lo := (552526243 / 1000000000)) (hi := (138131561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868818586367 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868818586367 / 500000000000) = 1/(500000000000 / 868818586367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (552526243 / 1000000000) (138131561 / 250000000) (Real.log (868818586367 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (868818586367 / 500000000000) = -Real.log (500000000000 / 868818586367) := by
    rw [show ((868818586367 / 500000000000) : ℝ) = ((500000000000 / 868818586367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0282

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0283Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0283
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (445113 / 1953125) ≤ -Real.log (10240 / 12861) ∧
    -Real.log (10240 / 12861) ≤ (227897857 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 23101)) (n := 12)
    (lo := (445113 / 1953125)) (hi := (227897857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12861 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12861 / 10240) = 1/(10240 / 12861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (445113 / 1953125) (227897857 / 1000000000) (Real.log (12861 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12861 / 10240) = -Real.log (10240 / 12861) := by
    rw [show ((12861 / 10240) : ℝ) = ((10240 / 12861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73914123 / 250000000) ≤ -Real.log (7619 / 10240) ∧
    -Real.log (7619 / 10240) ≤ (295656493 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 17859)) (n := 12)
    (lo := (73914123 / 250000000)) (hi := (295656493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7619) = 1/(7619 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-295656493 / 1000000000) (-73914123 / 250000000) (Real.log (7619 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113832283 / 500000000) ≤ -Real.log (5120 / 6429) ∧
    -Real.log (5120 / 6429) ≤ (227664567 / 1000000000) := by
  have h := checkLog_sound (w := (1309 / 11549)) (n := 12)
    (lo := (113832283 / 500000000)) (hi := (227664567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6429 / 5120) = 1/(5120 / 6429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113832283 / 500000000) (227664567 / 1000000000) (Real.log (6429 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6429 / 5120) = -Real.log (5120 / 6429) := by
    rw [show ((6429 / 5120) : ℝ) = ((5120 / 6429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (295262817 / 1000000000) ≤ -Real.log (3811 / 5120) ∧
    -Real.log (3811 / 5120) ≤ (147631409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 8931)) (n := 12)
    (lo := (295262817 / 1000000000)) (hi := (147631409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3811) = 1/(3811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-147631409 / 500000000) (-295262817 / 1000000000) (Real.log (3811 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (413376439 / 1000000000) ≤ -Real.log (5120 / 7741) ∧
    -Real.log (5120 / 7741) ≤ (10334411 / 25000000) := by
  have h := checkLog_sound (w := (2621 / 12861)) (n := 12)
    (lo := (413376439 / 1000000000)) (hi := (10334411 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7741 / 5120) = 1/(5120 / 7741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (413376439 / 1000000000) (10334411 / 25000000) (Real.log (7741 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7741 / 5120) = -Real.log (5120 / 7741) := by
    rw [show ((7741 / 5120) : ℝ) = ((5120 / 7741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (358631893 / 500000000) ≤ -Real.log (2499 / 5120) ∧
    -Real.log (2499 / 5120) ≤ (179315947 / 250000000) := by
  have h := checkLog_sound (w := (61 / 5059)) (n := 12)
    (lo := (12058303 / 500000000)) (hi := (24116607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2499) = 1/(2499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-179315947 / 250000000) (-358631893 / 500000000) (Real.log (2499 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (412988817 / 1000000000) ≤ -Real.log (2560 / 3869) ∧
    -Real.log (2560 / 3869) ≤ (206494409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 6429)) (n := 12)
    (lo := (412988817 / 1000000000)) (hi := (206494409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3869 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3869 / 2560) = 1/(2560 / 3869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (412988817 / 1000000000) (206494409 / 500000000) (Real.log (3869 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3869 / 2560) = -Real.log (2560 / 3869) := by
    rw [show ((3869 / 2560) : ℝ) = ((2560 / 3869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (358032013 / 500000000) ≤ -Real.log (1251 / 2560) ∧
    -Real.log (1251 / 2560) ≤ (179016007 / 250000000) := by
  have h := checkLog_sound (w := (29 / 2531)) (n := 12)
    (lo := (11458423 / 500000000)) (hi := (22916847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1251) = 1/(1251 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-179016007 / 250000000) (-358032013 / 500000000) (Real.log (1251 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (311887493 / 1000000000) ≤ -Real.log (1000000 / 1366001) ∧
    -Real.log (1000000 / 1366001) ≤ (155943747 / 500000000) := by
  have h := checkLog_sound (w := (366001 / 2366001)) (n := 12)
    (lo := (311887493 / 1000000000)) (hi := (155943747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366001 / 1000000) = 1/(1000000 / 1366001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (311887493 / 1000000000) (155943747 / 500000000) (Real.log (1366001 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1366001 / 1000000) = -Real.log (1000000 / 1366001) := by
    rw [show ((1366001 / 1000000) : ℝ) = ((1000000 / 1366001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (455707901 / 1000000000) ≤ -Real.log (633999 / 1000000) ∧
    -Real.log (633999 / 1000000) ≤ (227853951 / 500000000) := by
  have h := checkLog_sound (w := (366001 / 1633999)) (n := 12)
    (lo := (455707901 / 1000000000)) (hi := (227853951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633999) = 1/(633999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227853951 / 500000000) (-455707901 / 1000000000) (Real.log (633999 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156101847 / 500000000) ≤ -Real.log (1000000 / 1366433) ∧
    -Real.log (1000000 / 1366433) ≤ (62440739 / 200000000) := by
  have h := checkLog_sound (w := (366433 / 2366433)) (n := 12)
    (lo := (156101847 / 500000000)) (hi := (62440739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366433 / 1000000) = 1/(1000000 / 1366433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156101847 / 500000000) (62440739 / 200000000) (Real.log (1366433 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1366433 / 1000000) = -Real.log (1000000 / 1366433) := by
    rw [show ((1366433 / 1000000) : ℝ) = ((1000000 / 1366433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (456389523 / 1000000000) ≤ -Real.log (633567 / 1000000) ∧
    -Real.log (633567 / 1000000) ≤ (114097381 / 250000000) := by
  have h := checkLog_sound (w := (366433 / 1633567)) (n := 12)
    (lo := (456389523 / 1000000000)) (hi := (114097381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633567) = 1/(633567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-114097381 / 250000000) (-456389523 / 1000000000) (Real.log (633567 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (238040833 / 1000000000) ≤ -Real.log (1000000 / 1268761) ∧
    -Real.log (1000000 / 1268761) ≤ (119020417 / 500000000) := by
  have h := checkLog_sound (w := (268761 / 2268761)) (n := 12)
    (lo := (238040833 / 1000000000)) (hi := (119020417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268761 / 1000000) = 1/(1000000 / 1268761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (238040833 / 1000000000) (119020417 / 500000000) (Real.log (1268761 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1268761 / 1000000) = -Real.log (1000000 / 1268761) := by
    rw [show ((1268761 / 1000000) : ℝ) = ((1000000 / 1268761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (313014923 / 1000000000) ≤ -Real.log (731239 / 1000000) ∧
    -Real.log (731239 / 1000000) ≤ (78253731 / 250000000) := by
  have h := checkLog_sound (w := (268761 / 1731239)) (n := 12)
    (lo := (313014923 / 1000000000)) (hi := (78253731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731239) = 1/(731239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78253731 / 250000000) (-313014923 / 1000000000) (Real.log (731239 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (238309563 / 1000000000) ≤ -Real.log (500000 / 634551) ∧
    -Real.log (500000 / 634551) ≤ (59577391 / 250000000) := by
  have h := checkLog_sound (w := (134551 / 1134551)) (n := 12)
    (lo := (238309563 / 1000000000)) (hi := (59577391 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634551 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634551 / 500000) = 1/(500000 / 634551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (238309563 / 1000000000) (59577391 / 250000000) (Real.log (634551 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (634551 / 500000) = -Real.log (500000 / 634551) := by
    rw [show ((634551 / 500000) : ℝ) = ((500000 / 634551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (313481363 / 1000000000) ≤ -Real.log (365449 / 500000) ∧
    -Real.log (365449 / 500000) ≤ (78370341 / 250000000) := by
  have h := checkLog_sound (w := (134551 / 865449)) (n := 12)
    (lo := (313481363 / 1000000000)) (hi := (78370341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365449) = 1/(365449 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78370341 / 250000000) (-313481363 / 1000000000) (Real.log (365449 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (383797697 / 500000000) ≤ -Real.log (125000000000 / 269322388521) ∧
    -Real.log (125000000000 / 269322388521) ≤ (191898849 / 250000000) := by
  have h := checkLog_sound (w := (19322388521 / 519322388521)) (n := 12)
    (lo := (37224107 / 500000000)) (hi := (14889643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269322388521 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269322388521 / 250000000000) = 1/(125000000000 / 269322388521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (383797697 / 500000000) (191898849 / 250000000) (Real.log (269322388521 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (269322388521 / 125000000000) = -Real.log (125000000000 / 269322388521) := by
    rw [show ((269322388521 / 125000000000) : ℝ) = ((125000000000 / 269322388521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (768593217 / 1000000000) ≤ -Real.log (125000000000 / 269591258699) ∧
    -Real.log (125000000000 / 269591258699) ≤ (768593219 / 1000000000) := by
  have h := checkLog_sound (w := (19591258699 / 519591258699)) (n := 12)
    (lo := (75446037 / 1000000000)) (hi := (37723019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269591258699 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269591258699 / 250000000000) = 1/(125000000000 / 269591258699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (768593217 / 1000000000) (768593219 / 1000000000) (Real.log (269591258699 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (269591258699 / 125000000000) = -Real.log (125000000000 / 269591258699) := by
    rw [show ((269591258699 / 125000000000) : ℝ) = ((125000000000 / 269591258699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (551055757 / 1000000000) ≤ -Real.log (125000000000 / 216885484773) ∧
    -Real.log (125000000000 / 216885484773) ≤ (275527879 / 500000000) := by
  have h := checkLog_sound (w := (91885484773 / 341885484773)) (n := 12)
    (lo := (551055757 / 1000000000)) (hi := (275527879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216885484773 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216885484773 / 125000000000) = 1/(125000000000 / 216885484773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (551055757 / 1000000000) (275527879 / 500000000) (Real.log (216885484773 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (216885484773 / 125000000000) = -Real.log (125000000000 / 216885484773) := by
    rw [show ((216885484773 / 125000000000) : ℝ) = ((125000000000 / 216885484773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (551790927 / 1000000000) ≤ -Real.log (12500000000 / 21704499123) ∧
    -Real.log (12500000000 / 21704499123) ≤ (34486933 / 62500000) := by
  have h := checkLog_sound (w := (9204499123 / 34204499123)) (n := 12)
    (lo := (551790927 / 1000000000)) (hi := (34486933 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21704499123 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21704499123 / 12500000000) = 1/(12500000000 / 21704499123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (551790927 / 1000000000) (34486933 / 62500000) (Real.log (21704499123 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21704499123 / 12500000000) = -Real.log (12500000000 / 21704499123) := by
    rw [show ((21704499123 / 12500000000) : ℝ) = ((12500000000 / 21704499123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0283

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0284Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0284
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (113832283 / 500000000) ≤ -Real.log (5120 / 6429) ∧
    -Real.log (5120 / 6429) ≤ (227664567 / 1000000000) := by
  have h := checkLog_sound (w := (1309 / 11549)) (n := 12)
    (lo := (113832283 / 500000000)) (hi := (227664567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6429 / 5120) = 1/(5120 / 6429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113832283 / 500000000) (227664567 / 1000000000) (Real.log (6429 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6429 / 5120) = -Real.log (5120 / 6429) := by
    rw [show ((6429 / 5120) : ℝ) = ((5120 / 6429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (295262817 / 1000000000) ≤ -Real.log (3811 / 5120) ∧
    -Real.log (3811 / 5120) ≤ (147631409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 8931)) (n := 12)
    (lo := (295262817 / 1000000000)) (hi := (147631409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3811) = 1/(3811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-147631409 / 500000000) (-295262817 / 1000000000) (Real.log (3811 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227431221 / 1000000000) ≤ -Real.log (2048 / 2571) ∧
    -Real.log (2048 / 2571) ≤ (113715611 / 500000000) := by
  have h := checkLog_sound (w := (523 / 4619)) (n := 12)
    (lo := (227431221 / 1000000000)) (hi := (113715611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2048) = 1/(2048 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227431221 / 1000000000) (113715611 / 500000000) (Real.log (2571 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2571 / 2048) = -Real.log (2048 / 2571) := by
    rw [show ((2571 / 2048) : ℝ) = ((2048 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (294869297 / 1000000000) ≤ -Real.log (1525 / 2048) ∧
    -Real.log (1525 / 2048) ≤ (147434649 / 500000000) := by
  have h := checkLog_sound (w := (523 / 3573)) (n := 12)
    (lo := (294869297 / 1000000000)) (hi := (147434649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1525) = 1/(1525 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-147434649 / 500000000) (-294869297 / 1000000000) (Real.log (1525 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (412988817 / 1000000000) ≤ -Real.log (2560 / 3869) ∧
    -Real.log (2560 / 3869) ≤ (206494409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 6429)) (n := 12)
    (lo := (412988817 / 1000000000)) (hi := (206494409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3869 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3869 / 2560) = 1/(2560 / 3869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (412988817 / 1000000000) (206494409 / 500000000) (Real.log (3869 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3869 / 2560) = -Real.log (2560 / 3869) := by
    rw [show ((3869 / 2560) : ℝ) = ((2560 / 3869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (358032013 / 500000000) ≤ -Real.log (1251 / 2560) ∧
    -Real.log (1251 / 2560) ≤ (179016007 / 250000000) := by
  have h := checkLog_sound (w := (29 / 2531)) (n := 12)
    (lo := (11458423 / 500000000)) (hi := (22916847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1251) = 1/(1251 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-179016007 / 250000000) (-358032013 / 500000000) (Real.log (1251 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (103150261 / 250000000) ≤ -Real.log (1024 / 1547) ∧
    -Real.log (1024 / 1547) ≤ (82520209 / 200000000) := by
  have h := checkLog_sound (w := (523 / 2571)) (n := 12)
    (lo := (103150261 / 250000000)) (hi := (82520209 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547 / 1024) = 1/(1024 / 1547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (103150261 / 250000000) (82520209 / 200000000) (Real.log (1547 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1547 / 1024) = -Real.log (1024 / 1547) := by
    rw [show ((1547 / 1024) : ℝ) = ((1024 / 1547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (714865703 / 1000000000) ≤ -Real.log (501 / 1024) ∧
    -Real.log (501 / 1024) ≤ (142973141 / 200000000) := by
  have h := checkLog_sound (w := (11 / 1013)) (n := 12)
    (lo := (21718523 / 1000000000)) (hi := (5429631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 501) = 1/(501 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-142973141 / 200000000) (-714865703 / 1000000000) (Real.log (501 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (311571923 / 1000000000) ≤ -Real.log (100000 / 136557) ∧
    -Real.log (100000 / 136557) ≤ (77892981 / 250000000) := by
  have h := checkLog_sound (w := (36557 / 236557)) (n := 12)
    (lo := (311571923 / 1000000000)) (hi := (77892981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136557 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136557 / 100000) = 1/(100000 / 136557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (311571923 / 1000000000) (77892981 / 250000000) (Real.log (136557 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (136557 / 100000) = -Real.log (100000 / 136557) := by
    rw [show ((136557 / 100000) : ℝ) = ((100000 / 136557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (455028321 / 1000000000) ≤ -Real.log (63443 / 100000) ∧
    -Real.log (63443 / 100000) ≤ (227514161 / 500000000) := by
  have h := checkLog_sound (w := (36557 / 163443)) (n := 12)
    (lo := (455028321 / 1000000000)) (hi := (227514161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 63443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 63443) = 1/(63443 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227514161 / 500000000) (-455028321 / 1000000000) (Real.log (63443 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (12475529 / 40000000) ≤ -Real.log (500000 / 683001) ∧
    -Real.log (500000 / 683001) ≤ (155944113 / 500000000) := by
  have h := checkLog_sound (w := (183001 / 1183001)) (n := 12)
    (lo := (12475529 / 40000000)) (hi := (155944113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683001 / 500000) = 1/(500000 / 683001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (12475529 / 40000000) (155944113 / 500000000) (Real.log (683001 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (683001 / 500000) = -Real.log (500000 / 683001) := by
    rw [show ((683001 / 500000) : ℝ) = ((500000 / 683001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (455709479 / 1000000000) ≤ -Real.log (316999 / 500000) ∧
    -Real.log (316999 / 500000) ≤ (11392737 / 25000000) := by
  have h := checkLog_sound (w := (183001 / 816999)) (n := 12)
    (lo := (455709479 / 1000000000)) (hi := (11392737 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 316999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 316999) = 1/(316999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11392737 / 25000000) (-455709479 / 1000000000) (Real.log (316999 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (237772031 / 1000000000) ≤ -Real.log (50000 / 63421) ∧
    -Real.log (50000 / 63421) ≤ (928797 / 3906250) := by
  have h := checkLog_sound (w := (13421 / 113421)) (n := 12)
    (lo := (237772031 / 1000000000)) (hi := (928797 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63421 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63421 / 50000) = 1/(50000 / 63421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (237772031 / 1000000000) (928797 / 3906250) (Real.log (63421 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63421 / 50000) = -Real.log (50000 / 63421) := by
    rw [show ((63421 / 50000) : ℝ) = ((50000 / 63421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3125487 / 10000000) ≤ -Real.log (36579 / 50000) ∧
    -Real.log (36579 / 50000) ≤ (312548701 / 1000000000) := by
  have h := checkLog_sound (w := (13421 / 86579)) (n := 12)
    (lo := (3125487 / 10000000)) (hi := (312548701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36579) = 1/(36579 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-312548701 / 1000000000) (-3125487 / 10000000) (Real.log (36579 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (238041621 / 1000000000) ≤ -Real.log (500000 / 634381) ∧
    -Real.log (500000 / 634381) ≤ (119020811 / 500000000) := by
  have h := checkLog_sound (w := (134381 / 1134381)) (n := 12)
    (lo := (238041621 / 1000000000)) (hi := (119020811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634381 / 500000) = 1/(500000 / 634381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (238041621 / 1000000000) (119020811 / 500000000) (Real.log (634381 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (634381 / 500000) = -Real.log (500000 / 634381) := by
    rw [show ((634381 / 500000) : ℝ) = ((500000 / 634381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31301629 / 100000000) ≤ -Real.log (365619 / 500000) ∧
    -Real.log (365619 / 500000) ≤ (313016291 / 1000000000) := by
  have h := checkLog_sound (w := (134381 / 865619)) (n := 12)
    (lo := (31301629 / 100000000)) (hi := (313016291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365619) = 1/(365619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-313016291 / 1000000000) (-31301629 / 100000000) (Real.log (365619 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (191650061 / 250000000) ≤ -Real.log (125000000000 / 269054505619) ∧
    -Real.log (125000000000 / 269054505619) ≤ (383300123 / 500000000) := by
  have h := checkLog_sound (w := (19054505619 / 519054505619)) (n := 12)
    (lo := (9181633 / 125000000)) (hi := (14690613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269054505619 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269054505619 / 250000000000) = 1/(125000000000 / 269054505619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (191650061 / 250000000) (383300123 / 500000000) (Real.log (269054505619 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (269054505619 / 125000000000) = -Real.log (125000000000 / 269054505619) := by
    rw [show ((269054505619 / 125000000000) : ℝ) = ((125000000000 / 269054505619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (767597703 / 1000000000) ≤ -Real.log (500000000000 / 1077292041931) ∧
    -Real.log (500000000000 / 1077292041931) ≤ (153519541 / 200000000) := by
  have h := checkLog_sound (w := (77292041931 / 2077292041931)) (n := 12)
    (lo := (74450523 / 1000000000)) (hi := (18612631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077292041931 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1077292041931 / 1000000000000) = 1/(500000000000 / 1077292041931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (767597703 / 1000000000) (153519541 / 200000000) (Real.log (1077292041931 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1077292041931 / 500000000000) = -Real.log (500000000000 / 1077292041931) := by
    rw [show ((1077292041931 / 500000000000) : ℝ) = ((500000000000 / 1077292041931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (550320731 / 1000000000) ≤ -Real.log (500000000000 / 866904508051) ∧
    -Real.log (500000000000 / 866904508051) ≤ (137580183 / 250000000) := by
  have h := checkLog_sound (w := (366904508051 / 1366904508051)) (n := 12)
    (lo := (550320731 / 1000000000)) (hi := (137580183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866904508051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866904508051 / 500000000000) = 1/(500000000000 / 866904508051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (550320731 / 1000000000) (137580183 / 250000000) (Real.log (866904508051 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (866904508051 / 500000000000) = -Real.log (500000000000 / 866904508051) := by
    rw [show ((866904508051 / 500000000000) : ℝ) = ((500000000000 / 866904508051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (68882239 / 125000000) ≤ -Real.log (250000000000 / 433771904633) ∧
    -Real.log (250000000000 / 433771904633) ≤ (551057913 / 1000000000) := by
  have h := checkLog_sound (w := (183771904633 / 683771904633)) (n := 12)
    (lo := (68882239 / 125000000)) (hi := (551057913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433771904633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433771904633 / 250000000000) = 1/(250000000000 / 433771904633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (68882239 / 125000000) (551057913 / 1000000000) (Real.log (433771904633 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (433771904633 / 250000000000) = -Real.log (250000000000 / 433771904633) := by
    rw [show ((433771904633 / 250000000000) : ℝ) = ((250000000000 / 433771904633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0284

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0285Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0285
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (227431221 / 1000000000) ≤ -Real.log (2048 / 2571) ∧
    -Real.log (2048 / 2571) ≤ (113715611 / 500000000) := by
  have h := checkLog_sound (w := (523 / 4619)) (n := 12)
    (lo := (227431221 / 1000000000)) (hi := (113715611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2048) = 1/(2048 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227431221 / 1000000000) (113715611 / 500000000) (Real.log (2571 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2571 / 2048) = -Real.log (2048 / 2571) := by
    rw [show ((2571 / 2048) : ℝ) = ((2048 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (294869297 / 1000000000) ≤ -Real.log (1525 / 2048) ∧
    -Real.log (1525 / 2048) ≤ (147434649 / 500000000) := by
  have h := checkLog_sound (w := (523 / 3573)) (n := 12)
    (lo := (294869297 / 1000000000)) (hi := (147434649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1525) = 1/(1525 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-147434649 / 500000000) (-294869297 / 1000000000) (Real.log (1525 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227197821 / 1000000000) ≤ -Real.log (2560 / 3213) ∧
    -Real.log (2560 / 3213) ≤ (113598911 / 500000000) := by
  have h := checkLog_sound (w := (653 / 5773)) (n := 12)
    (lo := (227197821 / 1000000000)) (hi := (113598911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3213 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3213 / 2560) = 1/(2560 / 3213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227197821 / 1000000000) (113598911 / 500000000) (Real.log (3213 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3213 / 2560) = -Real.log (2560 / 3213) := by
    rw [show ((3213 / 2560) : ℝ) = ((2560 / 3213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (294475931 / 1000000000) ≤ -Real.log (1907 / 2560) ∧
    -Real.log (1907 / 2560) ≤ (73618983 / 250000000) := by
  have h := checkLog_sound (w := (653 / 4467)) (n := 12)
    (lo := (294475931 / 1000000000)) (hi := (73618983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1907) = 1/(1907 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-73618983 / 250000000) (-294475931 / 1000000000) (Real.log (1907 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103150261 / 250000000) ≤ -Real.log (1024 / 1547) ∧
    -Real.log (1024 / 1547) ≤ (82520209 / 200000000) := by
  have h := checkLog_sound (w := (523 / 2571)) (n := 12)
    (lo := (103150261 / 250000000)) (hi := (82520209 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547 / 1024) = 1/(1024 / 1547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103150261 / 250000000) (82520209 / 200000000) (Real.log (1547 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1547 / 1024) = -Real.log (1024 / 1547) := by
    rw [show ((1547 / 1024) : ℝ) = ((1024 / 1547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (714865703 / 1000000000) ≤ -Real.log (501 / 1024) ∧
    -Real.log (501 / 1024) ≤ (142973141 / 200000000) := by
  have h := checkLog_sound (w := (11 / 1013)) (n := 12)
    (lo := (21718523 / 1000000000)) (hi := (5429631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 501) = 1/(501 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-142973141 / 200000000) (-714865703 / 1000000000) (Real.log (501 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (206106561 / 500000000) ≤ -Real.log (1280 / 1933) ∧
    -Real.log (1280 / 1933) ≤ (412213123 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 3213)) (n := 12)
    (lo := (206106561 / 500000000)) (hi := (412213123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933 / 1280) = 1/(1280 / 1933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (206106561 / 500000000) (412213123 / 1000000000) (Real.log (1933 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1933 / 1280) = -Real.log (1280 / 1933) := by
    rw [show ((1933 / 1280) : ℝ) = ((1280 / 1933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142733763 / 200000000) ≤ -Real.log (627 / 1280) ∧
    -Real.log (627 / 1280) ≤ (713668817 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 1267)) (n := 12)
    (lo := (4104327 / 200000000)) (hi := (5130409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 627) = 1/(627 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-713668817 / 1000000000) (-142733763 / 200000000) (Real.log (627 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155628127 / 500000000) ≤ -Real.log (1000000 / 1365139) ∧
    -Real.log (1000000 / 1365139) ≤ (62251251 / 200000000) := by
  have h := checkLog_sound (w := (365139 / 2365139)) (n := 12)
    (lo := (155628127 / 500000000)) (hi := (62251251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365139 / 1000000) = 1/(1000000 / 1365139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155628127 / 500000000) (62251251 / 200000000) (Real.log (1365139 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1365139 / 1000000) = -Real.log (1000000 / 1365139) := by
    rw [show ((1365139 / 1000000) : ℝ) = ((1000000 / 1365139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (454349201 / 1000000000) ≤ -Real.log (634861 / 1000000) ∧
    -Real.log (634861 / 1000000) ≤ (227174601 / 500000000) := by
  have h := checkLog_sound (w := (365139 / 1634861)) (n := 12)
    (lo := (454349201 / 1000000000)) (hi := (227174601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634861) = 1/(634861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227174601 / 500000000) (-454349201 / 1000000000) (Real.log (634861 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (19473291 / 62500000) ≤ -Real.log (1000000 / 1365571) ∧
    -Real.log (1000000 / 1365571) ≤ (311572657 / 1000000000) := by
  have h := checkLog_sound (w := (365571 / 2365571)) (n := 12)
    (lo := (19473291 / 62500000)) (hi := (311572657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365571 / 1000000) = 1/(1000000 / 1365571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (19473291 / 62500000) (311572657 / 1000000000) (Real.log (1365571 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1365571 / 1000000) = -Real.log (1000000 / 1365571) := by
    rw [show ((1365571 / 1000000) : ℝ) = ((1000000 / 1365571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (455029897 / 1000000000) ≤ -Real.log (634429 / 1000000) ∧
    -Real.log (634429 / 1000000) ≤ (227514949 / 500000000) := by
  have h := checkLog_sound (w := (365571 / 1634429)) (n := 12)
    (lo := (455029897 / 1000000000)) (hi := (227514949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634429) = 1/(634429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-227514949 / 500000000) (-455029897 / 1000000000) (Real.log (634429 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (59375789 / 250000000) ≤ -Real.log (1000000 / 1268079) ∧
    -Real.log (1000000 / 1268079) ≤ (237503157 / 1000000000) := by
  have h := checkLog_sound (w := (268079 / 2268079)) (n := 12)
    (lo := (59375789 / 250000000)) (hi := (237503157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268079 / 1000000) = 1/(1000000 / 1268079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (59375789 / 250000000) (237503157 / 1000000000) (Real.log (1268079 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1268079 / 1000000) = -Real.log (1000000 / 1268079) := by
    rw [show ((1268079 / 1000000) : ℝ) = ((1000000 / 1268079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (156041347 / 500000000) ≤ -Real.log (731921 / 1000000) ∧
    -Real.log (731921 / 1000000) ≤ (62416539 / 200000000) := by
  have h := checkLog_sound (w := (268079 / 1731921)) (n := 12)
    (lo := (156041347 / 500000000)) (hi := (62416539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731921) = 1/(731921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62416539 / 200000000) (-156041347 / 500000000) (Real.log (731921 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (237772819 / 1000000000) ≤ -Real.log (1000000 / 1268421) ∧
    -Real.log (1000000 / 1268421) ≤ (11888641 / 50000000) := by
  have h := checkLog_sound (w := (268421 / 2268421)) (n := 12)
    (lo := (237772819 / 1000000000)) (hi := (11888641 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268421 / 1000000) = 1/(1000000 / 1268421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (237772819 / 1000000000) (11888641 / 50000000) (Real.log (1268421 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1268421 / 1000000) = -Real.log (1000000 / 1268421) := by
    rw [show ((1268421 / 1000000) : ℝ) = ((1000000 / 1268421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (312550067 / 1000000000) ≤ -Real.log (731579 / 1000000) ∧
    -Real.log (731579 / 1000000) ≤ (78137517 / 250000000) := by
  have h := checkLog_sound (w := (268421 / 1731579)) (n := 12)
    (lo := (312550067 / 1000000000)) (hi := (78137517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731579) = 1/(731579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78137517 / 250000000) (-312550067 / 1000000000) (Real.log (731579 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (47850341 / 62500000) ≤ -Real.log (50000000000 / 107514794577) ∧
    -Real.log (50000000000 / 107514794577) ≤ (382802729 / 500000000) := by
  have h := checkLog_sound (w := (7514794577 / 207514794577)) (n := 12)
    (lo := (18114569 / 250000000)) (hi := (72458277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107514794577 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(107514794577 / 100000000000) = 1/(50000000000 / 107514794577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (47850341 / 62500000) (382802729 / 500000000) (Real.log (107514794577 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (107514794577 / 50000000000) = -Real.log (50000000000 / 107514794577) := by
    rw [show ((107514794577 / 50000000000) : ℝ) = ((50000000000 / 107514794577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (95825319 / 125000000) ≤ -Real.log (100000000000 / 215244101389) ∧
    -Real.log (100000000000 / 215244101389) ≤ (383301277 / 500000000) := by
  have h := checkLog_sound (w := (15244101389 / 415244101389)) (n := 12)
    (lo := (18363843 / 250000000)) (hi := (73455373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215244101389 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(215244101389 / 200000000000) = 1/(100000000000 / 215244101389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (95825319 / 125000000) (383301277 / 500000000) (Real.log (215244101389 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (215244101389 / 100000000000) = -Real.log (100000000000 / 215244101389) := by
    rw [show ((215244101389 / 100000000000) : ℝ) = ((100000000000 / 215244101389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (549585851 / 1000000000) ≤ -Real.log (125000000000 / 216566917741) ∧
    -Real.log (125000000000 / 216566917741) ≤ (137396463 / 250000000) := by
  have h := checkLog_sound (w := (91566917741 / 341566917741)) (n := 12)
    (lo := (549585851 / 1000000000)) (hi := (137396463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216566917741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216566917741 / 125000000000) = 1/(125000000000 / 216566917741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (549585851 / 1000000000) (137396463 / 250000000) (Real.log (216566917741 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (216566917741 / 125000000000) = -Real.log (125000000000 / 216566917741) := by
    rw [show ((216566917741 / 125000000000) : ℝ) = ((125000000000 / 216566917741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (275161443 / 500000000) ≤ -Real.log (250000000000 / 433453188241) ∧
    -Real.log (250000000000 / 433453188241) ≤ (550322887 / 1000000000) := by
  have h := checkLog_sound (w := (183453188241 / 683453188241)) (n := 12)
    (lo := (275161443 / 500000000)) (hi := (550322887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433453188241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433453188241 / 250000000000) = 1/(250000000000 / 433453188241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (275161443 / 500000000) (550322887 / 1000000000) (Real.log (433453188241 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (433453188241 / 250000000000) = -Real.log (250000000000 / 433453188241) := by
    rw [show ((433453188241 / 250000000000) : ℝ) = ((250000000000 / 433453188241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0285

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0286Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0286
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (227197821 / 1000000000) ≤ -Real.log (2560 / 3213) ∧
    -Real.log (2560 / 3213) ≤ (113598911 / 500000000) := by
  have h := checkLog_sound (w := (653 / 5773)) (n := 12)
    (lo := (227197821 / 1000000000)) (hi := (113598911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3213 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3213 / 2560) = 1/(2560 / 3213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227197821 / 1000000000) (113598911 / 500000000) (Real.log (3213 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3213 / 2560) = -Real.log (2560 / 3213) := by
    rw [show ((3213 / 2560) : ℝ) = ((2560 / 3213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (294475931 / 1000000000) ≤ -Real.log (1907 / 2560) ∧
    -Real.log (1907 / 2560) ≤ (73618983 / 250000000) := by
  have h := checkLog_sound (w := (653 / 4467)) (n := 12)
    (lo := (294475931 / 1000000000)) (hi := (73618983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1907) = 1/(1907 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-73618983 / 250000000) (-294475931 / 1000000000) (Real.log (1907 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226964367 / 1000000000) ≤ -Real.log (10240 / 12849) ∧
    -Real.log (10240 / 12849) ≤ (14185273 / 62500000) := by
  have h := checkLog_sound (w := (2609 / 23089)) (n := 12)
    (lo := (226964367 / 1000000000)) (hi := (14185273 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12849 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12849 / 10240) = 1/(10240 / 12849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226964367 / 1000000000) (14185273 / 62500000) (Real.log (12849 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12849 / 10240) = -Real.log (10240 / 12849) := by
    rw [show ((12849 / 10240) : ℝ) = ((10240 / 12849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (294082721 / 1000000000) ≤ -Real.log (7631 / 10240) ∧
    -Real.log (7631 / 10240) ≤ (147041361 / 500000000) := by
  have h := checkLog_sound (w := (2609 / 17871)) (n := 12)
    (lo := (294082721 / 1000000000)) (hi := (147041361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7631) = 1/(7631 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-147041361 / 500000000) (-294082721 / 1000000000) (Real.log (7631 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (206106561 / 500000000) ≤ -Real.log (1280 / 1933) ∧
    -Real.log (1280 / 1933) ≤ (412213123 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 3213)) (n := 12)
    (lo := (206106561 / 500000000)) (hi := (412213123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933 / 1280) = 1/(1280 / 1933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (206106561 / 500000000) (412213123 / 1000000000) (Real.log (1933 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1933 / 1280) = -Real.log (1280 / 1933) := by
    rw [show ((1933 / 1280) : ℝ) = ((1280 / 1933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142733763 / 200000000) ≤ -Real.log (627 / 1280) ∧
    -Real.log (627 / 1280) ≤ (713668817 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 1267)) (n := 12)
    (lo := (4104327 / 200000000)) (hi := (5130409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 627) = 1/(627 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-713668817 / 1000000000) (-142733763 / 200000000) (Real.log (627 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (411825049 / 1000000000) ≤ -Real.log (5120 / 7729) ∧
    -Real.log (5120 / 7729) ≤ (8236501 / 20000000) := by
  have h := checkLog_sound (w := (2609 / 12849)) (n := 12)
    (lo := (411825049 / 1000000000)) (hi := (8236501 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7729 / 5120) = 1/(5120 / 7729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (411825049 / 1000000000) (8236501 / 20000000) (Real.log (7729 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7729 / 5120) = -Real.log (5120 / 7729) := by
    rw [show ((7729 / 5120) : ℝ) = ((5120 / 7729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (356236679 / 500000000) ≤ -Real.log (2511 / 5120) ∧
    -Real.log (2511 / 5120) ≤ (8905917 / 12500000) := by
  have h := checkLog_sound (w := (49 / 5071)) (n := 12)
    (lo := (9663089 / 500000000)) (hi := (19326179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2511) = 1/(2511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-8905917 / 12500000) (-356236679 / 500000000) (Real.log (2511 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155470243 / 500000000) ≤ -Real.log (250000 / 341177) ∧
    -Real.log (250000 / 341177) ≤ (310940487 / 1000000000) := by
  have h := checkLog_sound (w := (91177 / 591177)) (n := 12)
    (lo := (155470243 / 500000000)) (hi := (310940487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341177 / 250000) = 1/(250000 / 341177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155470243 / 500000000) (310940487 / 1000000000) (Real.log (341177 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (341177 / 250000) = -Real.log (250000 / 341177) := by
    rw [show ((341177 / 250000) : ℝ) = ((250000 / 341177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (453670543 / 1000000000) ≤ -Real.log (158823 / 250000) ∧
    -Real.log (158823 / 250000) ≤ (28354409 / 62500000) := by
  have h := checkLog_sound (w := (91177 / 408823)) (n := 12)
    (lo := (453670543 / 1000000000)) (hi := (28354409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 158823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 158823) = 1/(158823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28354409 / 62500000) (-453670543 / 1000000000) (Real.log (158823 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (311256987 / 1000000000) ≤ -Real.log (50000 / 68257) ∧
    -Real.log (50000 / 68257) ≤ (77814247 / 250000000) := by
  have h := checkLog_sound (w := (18257 / 118257)) (n := 12)
    (lo := (311256987 / 1000000000)) (hi := (77814247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68257 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68257 / 50000) = 1/(50000 / 68257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (311256987 / 1000000000) (77814247 / 250000000) (Real.log (68257 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (68257 / 50000) = -Real.log (50000 / 68257) := by
    rw [show ((68257 / 50000) : ℝ) = ((50000 / 68257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56793847 / 125000000) ≤ -Real.log (31743 / 50000) ∧
    -Real.log (31743 / 50000) ≤ (454350777 / 1000000000) := by
  have h := checkLog_sound (w := (18257 / 81743)) (n := 12)
    (lo := (56793847 / 125000000)) (hi := (454350777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 31743) = 1/(31743 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-454350777 / 1000000000) (-56793847 / 125000000) (Real.log (31743 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (118617499 / 500000000) ≤ -Real.log (1000000 / 1267739) ∧
    -Real.log (1000000 / 1267739) ≤ (237234999 / 1000000000) := by
  have h := checkLog_sound (w := (267739 / 2267739)) (n := 12)
    (lo := (118617499 / 500000000)) (hi := (237234999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267739 / 1000000) = 1/(1000000 / 1267739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (118617499 / 500000000) (237234999 / 1000000000) (Real.log (1267739 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1267739 / 1000000) = -Real.log (1000000 / 1267739) := by
    rw [show ((1267739 / 1000000) : ℝ) = ((1000000 / 1267739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (311618271 / 1000000000) ≤ -Real.log (732261 / 1000000) ∧
    -Real.log (732261 / 1000000) ≤ (9738071 / 31250000) := by
  have h := checkLog_sound (w := (267739 / 1732261)) (n := 12)
    (lo := (311618271 / 1000000000)) (hi := (9738071 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732261) = 1/(732261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-9738071 / 31250000) (-311618271 / 1000000000) (Real.log (732261 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (47500789 / 200000000) ≤ -Real.log (12500 / 15851) ∧
    -Real.log (12500 / 15851) ≤ (118751973 / 500000000) := by
  have h := checkLog_sound (w := (3351 / 28351)) (n := 12)
    (lo := (47500789 / 200000000)) (hi := (118751973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15851 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15851 / 12500) = 1/(12500 / 15851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (47500789 / 200000000) (118751973 / 500000000) (Real.log (15851 / 12500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (15851 / 12500) = -Real.log (12500 / 15851) := by
    rw [show ((15851 / 12500) : ℝ) = ((12500 / 15851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15604203 / 50000000) ≤ -Real.log (9149 / 12500) ∧
    -Real.log (9149 / 12500) ≤ (312084061 / 1000000000) := by
  have h := checkLog_sound (w := (3351 / 21649)) (n := 12)
    (lo := (15604203 / 50000000)) (hi := (312084061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9149) = 1/(9149 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-312084061 / 1000000000) (-15604203 / 50000000) (Real.log (9149 / 12500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (764611029 / 1000000000) ≤ -Real.log (100000000000 / 214815864201) ∧
    -Real.log (100000000000 / 214815864201) ≤ (764611031 / 1000000000) := by
  have h := checkLog_sound (w := (14815864201 / 414815864201)) (n := 12)
    (lo := (71463849 / 1000000000)) (hi := (1429277 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((214815864201 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(214815864201 / 200000000000) = 1/(100000000000 / 214815864201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (764611029 / 1000000000) (764611031 / 1000000000) (Real.log (214815864201 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (214815864201 / 100000000000) = -Real.log (100000000000 / 214815864201) := by
    rw [show ((214815864201 / 100000000000) : ℝ) = ((100000000000 / 214815864201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (765607763 / 1000000000) ≤ -Real.log (250000000000 / 537575213433) ∧
    -Real.log (250000000000 / 537575213433) ≤ (153121553 / 200000000) := by
  have h := checkLog_sound (w := (37575213433 / 1037575213433)) (n := 12)
    (lo := (72460583 / 1000000000)) (hi := (9057573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537575213433 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537575213433 / 500000000000) = 1/(250000000000 / 537575213433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (765607763 / 1000000000) (153121553 / 200000000) (Real.log (537575213433 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (537575213433 / 250000000000) = -Real.log (250000000000 / 537575213433) := by
    rw [show ((537575213433 / 250000000000) : ℝ) = ((250000000000 / 537575213433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54885327 / 100000000) ≤ -Real.log (250000000000 / 432816645977) ∧
    -Real.log (250000000000 / 432816645977) ≤ (548853271 / 1000000000) := by
  have h := checkLog_sound (w := (182816645977 / 682816645977)) (n := 12)
    (lo := (54885327 / 100000000)) (hi := (548853271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432816645977 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432816645977 / 250000000000) = 1/(250000000000 / 432816645977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (54885327 / 100000000) (548853271 / 1000000000) (Real.log (432816645977 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (432816645977 / 250000000000) = -Real.log (250000000000 / 432816645977) := by
    rw [show ((432816645977 / 250000000000) : ℝ) = ((250000000000 / 432816645977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (274794003 / 500000000) ≤ -Real.log (100000000000 / 173253907531) ∧
    -Real.log (100000000000 / 173253907531) ≤ (549588007 / 1000000000) := by
  have h := checkLog_sound (w := (73253907531 / 273253907531)) (n := 12)
    (lo := (274794003 / 500000000)) (hi := (549588007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173253907531 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173253907531 / 100000000000) = 1/(100000000000 / 173253907531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (274794003 / 500000000) (549588007 / 1000000000) (Real.log (173253907531 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (173253907531 / 100000000000) = -Real.log (100000000000 / 173253907531) := by
    rw [show ((173253907531 / 100000000000) : ℝ) = ((100000000000 / 173253907531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0286

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0287Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0287
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (226964367 / 1000000000) ≤ -Real.log (10240 / 12849) ∧
    -Real.log (10240 / 12849) ≤ (14185273 / 62500000) := by
  have h := checkLog_sound (w := (2609 / 23089)) (n := 12)
    (lo := (226964367 / 1000000000)) (hi := (14185273 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12849 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12849 / 10240) = 1/(10240 / 12849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226964367 / 1000000000) (14185273 / 62500000) (Real.log (12849 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12849 / 10240) = -Real.log (10240 / 12849) := by
    rw [show ((12849 / 10240) : ℝ) = ((10240 / 12849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (294082721 / 1000000000) ≤ -Real.log (7631 / 10240) ∧
    -Real.log (7631 / 10240) ≤ (147041361 / 500000000) := by
  have h := checkLog_sound (w := (2609 / 17871)) (n := 12)
    (lo := (294082721 / 1000000000)) (hi := (147041361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7631) = 1/(7631 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-147041361 / 500000000) (-294082721 / 1000000000) (Real.log (7631 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226730859 / 1000000000) ≤ -Real.log (5120 / 6423) ∧
    -Real.log (5120 / 6423) ≤ (11336543 / 50000000) := by
  have h := checkLog_sound (w := (1303 / 11543)) (n := 12)
    (lo := (226730859 / 1000000000)) (hi := (11336543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6423 / 5120) = 1/(5120 / 6423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226730859 / 1000000000) (11336543 / 50000000) (Real.log (6423 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6423 / 5120) = -Real.log (5120 / 6423) := by
    rw [show ((6423 / 5120) : ℝ) = ((5120 / 6423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58737933 / 200000000) ≤ -Real.log (3817 / 5120) ∧
    -Real.log (3817 / 5120) ≤ (146844833 / 500000000) := by
  have h := checkLog_sound (w := (1303 / 8937)) (n := 12)
    (lo := (58737933 / 200000000)) (hi := (146844833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3817) = 1/(3817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-146844833 / 500000000) (-58737933 / 200000000) (Real.log (3817 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (411825049 / 1000000000) ≤ -Real.log (5120 / 7729) ∧
    -Real.log (5120 / 7729) ≤ (8236501 / 20000000) := by
  have h := checkLog_sound (w := (2609 / 12849)) (n := 12)
    (lo := (411825049 / 1000000000)) (hi := (8236501 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7729 / 5120) = 1/(5120 / 7729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (411825049 / 1000000000) (8236501 / 20000000) (Real.log (7729 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7729 / 5120) = -Real.log (5120 / 7729) := by
    rw [show ((7729 / 5120) : ℝ) = ((5120 / 7729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (356236679 / 500000000) ≤ -Real.log (2511 / 5120) ∧
    -Real.log (2511 / 5120) ≤ (8905917 / 12500000) := by
  have h := checkLog_sound (w := (49 / 5071)) (n := 12)
    (lo := (9663089 / 500000000)) (hi := (19326179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2511) = 1/(2511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-8905917 / 12500000) (-356236679 / 500000000) (Real.log (2511 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16457473 / 40000000) ≤ -Real.log (2560 / 3863) ∧
    -Real.log (2560 / 3863) ≤ (205718413 / 500000000) := by
  have h := checkLog_sound (w := (1303 / 6423)) (n := 12)
    (lo := (16457473 / 40000000)) (hi := (205718413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3863 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3863 / 2560) = 1/(2560 / 3863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16457473 / 40000000) (205718413 / 500000000) (Real.log (3863 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3863 / 2560) = -Real.log (2560 / 3863) := by
    rw [show ((3863 / 2560) : ℝ) = ((2560 / 3863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (22227479 / 31250000) ≤ -Real.log (1257 / 2560) ∧
    -Real.log (1257 / 2560) ≤ (71127933 / 100000000) := by
  have h := checkLog_sound (w := (23 / 2537)) (n := 12)
    (lo := (4533037 / 250000000)) (hi := (18132149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1257) = 1/(1257 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71127933 / 100000000) (-22227479 / 31250000) (Real.log (1257 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6212507 / 20000000) ≤ -Real.log (500000 / 682139) ∧
    -Real.log (500000 / 682139) ≤ (310625351 / 1000000000) := by
  have h := checkLog_sound (w := (182139 / 1182139)) (n := 12)
    (lo := (6212507 / 20000000)) (hi := (310625351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682139 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682139 / 500000) = 1/(500000 / 682139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6212507 / 20000000) (310625351 / 1000000000) (Real.log (682139 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (682139 / 500000) = -Real.log (500000 / 682139) := by
    rw [show ((682139 / 500000) : ℝ) = ((500000 / 682139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (226496959 / 500000000) ≤ -Real.log (317861 / 500000) ∧
    -Real.log (317861 / 500000) ≤ (452993919 / 1000000000) := by
  have h := checkLog_sound (w := (182139 / 817861)) (n := 12)
    (lo := (226496959 / 500000000)) (hi := (452993919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 317861) = 1/(317861 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-452993919 / 1000000000) (-226496959 / 500000000) (Real.log (317861 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (310941951 / 1000000000) ≤ -Real.log (100000 / 136471) ∧
    -Real.log (100000 / 136471) ≤ (1214617 / 3906250) := by
  have h := checkLog_sound (w := (36471 / 236471)) (n := 12)
    (lo := (310941951 / 1000000000)) (hi := (1214617 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136471 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136471 / 100000) = 1/(100000 / 136471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (310941951 / 1000000000) (1214617 / 3906250) (Real.log (136471 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (136471 / 100000) = -Real.log (100000 / 136471) := by
    rw [show ((136471 / 100000) : ℝ) = ((100000 / 136471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (453673691 / 1000000000) ≤ -Real.log (63529 / 100000) ∧
    -Real.log (63529 / 100000) ≤ (113418423 / 250000000) := by
  have h := checkLog_sound (w := (36471 / 163529)) (n := 12)
    (lo := (453673691 / 1000000000)) (hi := (113418423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 63529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 63529) = 1/(63529 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-113418423 / 250000000) (-453673691 / 1000000000) (Real.log (63529 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (14810423 / 62500000) ≤ -Real.log (1000000 / 1267399) ∧
    -Real.log (1000000 / 1267399) ≤ (236966769 / 1000000000) := by
  have h := checkLog_sound (w := (267399 / 2267399)) (n := 12)
    (lo := (14810423 / 62500000)) (hi := (236966769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267399 / 1000000) = 1/(1000000 / 1267399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (14810423 / 62500000) (236966769 / 1000000000) (Real.log (1267399 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1267399 / 1000000) = -Real.log (1000000 / 1267399) := by
    rw [show ((1267399 / 1000000) : ℝ) = ((1000000 / 1267399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (311154063 / 1000000000) ≤ -Real.log (732601 / 1000000) ∧
    -Real.log (732601 / 1000000) ≤ (19447129 / 62500000) := by
  have h := checkLog_sound (w := (267399 / 1732601)) (n := 12)
    (lo := (311154063 / 1000000000)) (hi := (19447129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732601) = 1/(732601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-19447129 / 62500000) (-311154063 / 1000000000) (Real.log (732601 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (237235787 / 1000000000) ≤ -Real.log (50000 / 63387) ∧
    -Real.log (50000 / 63387) ≤ (59308947 / 250000000) := by
  have h := checkLog_sound (w := (13387 / 113387)) (n := 12)
    (lo := (237235787 / 1000000000)) (hi := (59308947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63387 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63387 / 50000) = 1/(50000 / 63387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (237235787 / 1000000000) (59308947 / 250000000) (Real.log (63387 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63387 / 50000) = -Real.log (50000 / 63387) := by
    rw [show ((63387 / 50000) : ℝ) = ((50000 / 63387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (77904909 / 250000000) ≤ -Real.log (36613 / 50000) ∧
    -Real.log (36613 / 50000) ≤ (311619637 / 1000000000) := by
  have h := checkLog_sound (w := (13387 / 86613)) (n := 12)
    (lo := (77904909 / 250000000)) (hi := (311619637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36613) = 1/(36613 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-311619637 / 1000000000) (-77904909 / 250000000) (Real.log (36613 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (190904817 / 250000000) ≤ -Real.log (500000000000 / 1073014619597) ∧
    -Real.log (500000000000 / 1073014619597) ≤ (76361927 / 100000000) := by
  have h := checkLog_sound (w := (73014619597 / 2073014619597)) (n := 12)
    (lo := (8809011 / 125000000)) (hi := (70472089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073014619597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1073014619597 / 1000000000000) = 1/(500000000000 / 1073014619597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (190904817 / 250000000) (76361927 / 100000000) (Real.log (1073014619597 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1073014619597 / 500000000000) = -Real.log (500000000000 / 1073014619597) := by
    rw [show ((1073014619597 / 500000000000) : ℝ) = ((500000000000 / 1073014619597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (382307821 / 500000000) ≤ -Real.log (500000000000 / 1074084276473) ∧
    -Real.log (500000000000 / 1074084276473) ≤ (191153911 / 250000000) := by
  have h := checkLog_sound (w := (74084276473 / 2074084276473)) (n := 12)
    (lo := (35734231 / 500000000)) (hi := (71468463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074084276473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074084276473 / 1000000000000) = 1/(500000000000 / 1074084276473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (382307821 / 500000000) (191153911 / 250000000) (Real.log (1074084276473 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1074084276473 / 500000000000) = -Real.log (500000000000 / 1074084276473) := by
    rw [show ((1074084276473 / 500000000000) : ℝ) = ((500000000000 / 1074084276473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2141097 / 3906250) ≤ -Real.log (20000000000 / 34599980071) ∧
    -Real.log (20000000000 / 34599980071) ≤ (548120833 / 1000000000) := by
  have h := checkLog_sound (w := (14599980071 / 54599980071)) (n := 12)
    (lo := (2141097 / 3906250)) (hi := (548120833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34599980071 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34599980071 / 20000000000) = 1/(20000000000 / 34599980071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2141097 / 3906250) (548120833 / 1000000000) (Real.log (34599980071 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (34599980071 / 20000000000) = -Real.log (20000000000 / 34599980071) := by
    rw [show ((34599980071 / 20000000000) : ℝ) = ((20000000000 / 34599980071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4287933 / 7812500) ≤ -Real.log (31250000000 / 54102197307) ∧
    -Real.log (31250000000 / 54102197307) ≤ (21954217 / 40000000) := by
  have h := checkLog_sound (w := (22852197307 / 85352197307)) (n := 12)
    (lo := (4287933 / 7812500)) (hi := (21954217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54102197307 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54102197307 / 31250000000) = 1/(31250000000 / 54102197307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4287933 / 7812500) (21954217 / 40000000) (Real.log (54102197307 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (54102197307 / 31250000000) = -Real.log (31250000000 / 54102197307) := by
    rw [show ((54102197307 / 31250000000) : ℝ) = ((31250000000 / 54102197307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0287

end


