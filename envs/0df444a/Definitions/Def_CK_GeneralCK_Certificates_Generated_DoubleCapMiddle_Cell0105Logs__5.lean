-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0105Logs__5
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0105Logs__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:16:21.991712+00:00
-- url     : https://prove2.me/theorems/f12fcb88-f04e-4948-bd55-5a6d9dfad9ef
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0105Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0106Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0105Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0106Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0107Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0108Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0109Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0105Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0106Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0107Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0108Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0109Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0105Logs (+4 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0106Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0107Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0108Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0109Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0105Logs (+4 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0106Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0107Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0108Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0109Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0105Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0105
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

theorem reflection_log_1_neg : (32919133 / 100000000) ≤ -Real.log (1280 / 1779) ∧
    -Real.log (1280 / 1779) ≤ (329191331 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 3059)) (n := 12)
    (lo := (32919133 / 100000000)) (hi := (329191331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779 / 1280) = 1/(1280 / 1779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32919133 / 100000000) (329191331 / 1000000000) (Real.log (1779 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1779 / 1280) = -Real.log (1280 / 1779) := by
    rw [show ((1779 / 1280) : ℝ) = ((1280 / 1779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (494040207 / 1000000000) ≤ -Real.log (781 / 1280) ∧
    -Real.log (781 / 1280) ≤ (30877513 / 62500000) := by
  have h := checkLog_sound (w := (499 / 2061)) (n := 12)
    (lo := (494040207 / 1000000000)) (hi := (30877513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 781) = 1/(781 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30877513 / 62500000) (-494040207 / 1000000000) (Real.log (781 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (82086951 / 250000000) ≤ -Real.log (512 / 711) ∧
    -Real.log (512 / 711) ≤ (65669561 / 200000000) := by
  have h := checkLog_sound (w := (199 / 1223)) (n := 12)
    (lo := (82086951 / 250000000)) (hi := (65669561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711 / 512) = 1/(512 / 711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (82086951 / 250000000) (65669561 / 200000000) (Real.log (711 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (711 / 512) = -Real.log (512 / 711) := by
    rw [show ((711 / 512) : ℝ) = ((512 / 711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246060717 / 500000000) ≤ -Real.log (313 / 512) ∧
    -Real.log (313 / 512) ≤ (98424287 / 200000000) := by
  have h := checkLog_sound (w := (199 / 825)) (n := 12)
    (lo := (246060717 / 500000000)) (hi := (98424287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 313) = 1/(313 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-98424287 / 200000000) (-246060717 / 500000000) (Real.log (313 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (576437787 / 1000000000) ≤ -Real.log (640 / 1139) ∧
    -Real.log (640 / 1139) ≤ (144109447 / 250000000) := by
  have h := checkLog_sound (w := (499 / 1779)) (n := 12)
    (lo := (576437787 / 1000000000)) (hi := (144109447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139 / 640) = 1/(640 / 1139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (576437787 / 1000000000) (144109447 / 250000000) (Real.log (1139 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1139 / 640) = -Real.log (640 / 1139) := by
    rw [show ((1139 / 640) : ℝ) = ((640 / 1139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (378177071 / 250000000) ≤ -Real.log (141 / 640) ∧
    -Real.log (141 / 640) ≤ (1512708287 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 141) = 1/(141 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1512708287 / 1000000000) (-378177071 / 250000000) (Real.log (141 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (287559987 / 500000000) ≤ -Real.log (256 / 455) ∧
    -Real.log (256 / 455) ≤ (23004799 / 40000000) := by
  have h := checkLog_sound (w := (199 / 711)) (n := 12)
    (lo := (287559987 / 500000000)) (hi := (23004799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455 / 256) = 1/(256 / 455) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (287559987 / 500000000) (23004799 / 40000000) (Real.log (455 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (455 / 256) = -Real.log (256 / 455) := by
    rw [show ((455 / 256) : ℝ) = ((256 / 455) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60085047 / 40000000) ≤ -Real.log (57 / 256) ∧
    -Real.log (57 / 256) ≤ (751063089 / 500000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 57) = 1/(57 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-751063089 / 500000000) (-60085047 / 40000000) (Real.log (57 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (450376649 / 1000000000) ≤ -Real.log (1000000 / 1568903) ∧
    -Real.log (1000000 / 1568903) ≤ (9007533 / 20000000) := by
  have h := checkLog_sound (w := (568903 / 2568903)) (n := 12)
    (lo := (450376649 / 1000000000)) (hi := (9007533 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1568903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1568903 / 1000000) = 1/(1000000 / 1568903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (450376649 / 1000000000) (9007533 / 20000000) (Real.log (1568903 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1568903 / 1000000) = -Real.log (1000000 / 1568903) := by
    rw [show ((1568903 / 1000000) : ℝ) = ((1000000 / 1568903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (168284431 / 200000000) ≤ -Real.log (431097 / 1000000) ∧
    -Real.log (431097 / 1000000) ≤ (841422157 / 1000000000) := by
  have h := checkLog_sound (w := (68903 / 931097)) (n := 12)
    (lo := (5930999 / 40000000)) (hi := (4633593 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 431097) = 1/(431097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-841422157 / 1000000000) (-168284431 / 200000000) (Real.log (431097 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (451578677 / 1000000000) ≤ -Real.log (100000 / 157079) ∧
    -Real.log (100000 / 157079) ≤ (225789339 / 500000000) := by
  have h := checkLog_sound (w := (57079 / 257079)) (n := 12)
    (lo := (451578677 / 1000000000)) (hi := (225789339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157079 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157079 / 100000) = 1/(100000 / 157079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (451578677 / 1000000000) (225789339 / 500000000) (Real.log (157079 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (157079 / 100000) = -Real.log (100000 / 157079) := by
    rw [show ((157079 / 100000) : ℝ) = ((100000 / 157079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (105726121 / 125000000) ≤ -Real.log (42921 / 100000) ∧
    -Real.log (42921 / 100000) ≤ (84580897 / 100000000) := by
  have h := checkLog_sound (w := (7079 / 92921)) (n := 12)
    (lo := (38165447 / 250000000)) (hi := (152661789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42921) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42921) = 1/(42921 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84580897 / 100000000) (-105726121 / 125000000) (Real.log (42921 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (365754301 / 1000000000) ≤ -Real.log (1000000 / 1441601) ∧
    -Real.log (1000000 / 1441601) ≤ (182877151 / 500000000) := by
  have h := checkLog_sound (w := (441601 / 2441601)) (n := 12)
    (lo := (365754301 / 1000000000)) (hi := (182877151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441601 / 1000000) = 1/(1000000 / 1441601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (365754301 / 1000000000) (182877151 / 500000000) (Real.log (1441601 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1441601 / 1000000) = -Real.log (1000000 / 1441601) := by
    rw [show ((1441601 / 1000000) : ℝ) = ((1000000 / 1441601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291340759 / 500000000) ≤ -Real.log (558399 / 1000000) ∧
    -Real.log (558399 / 1000000) ≤ (582681519 / 1000000000) := by
  have h := checkLog_sound (w := (441601 / 1558399)) (n := 12)
    (lo := (291340759 / 500000000)) (hi := (582681519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 558399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 558399) = 1/(558399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-582681519 / 1000000000) (-291340759 / 500000000) (Real.log (558399 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (366967493 / 1000000000) ≤ -Real.log (1000000 / 1443351) ∧
    -Real.log (1000000 / 1443351) ≤ (183483747 / 500000000) := by
  have h := checkLog_sound (w := (443351 / 2443351)) (n := 12)
    (lo := (366967493 / 1000000000)) (hi := (183483747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443351 / 1000000) = 1/(1000000 / 1443351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (366967493 / 1000000000) (183483747 / 500000000) (Real.log (1443351 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1443351 / 1000000) = -Real.log (1000000 / 1443351) := by
    rw [show ((1443351 / 1000000) : ℝ) = ((1000000 / 1443351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (585820399 / 1000000000) ≤ -Real.log (556649 / 1000000) ∧
    -Real.log (556649 / 1000000) ≤ (1464551 / 2500000) := by
  have h := checkLog_sound (w := (443351 / 1556649)) (n := 12)
    (lo := (585820399 / 1000000000)) (hi := (1464551 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 556649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 556649) = 1/(556649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1464551 / 2500000) (-585820399 / 1000000000) (Real.log (556649 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (322949701 / 250000000) ≤ -Real.log (500000000000 / 1819663555997) ∧
    -Real.log (500000000000 / 1819663555997) ≤ (645899403 / 500000000) := by
  have h := checkLog_sound (w := (819663555997 / 2819663555997)) (n := 12)
    (lo := (74831453 / 125000000)) (hi := (4789213 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1819663555997 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1819663555997 / 1000000000000) = 1/(500000000000 / 1819663555997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (322949701 / 250000000) (645899403 / 500000000) (Real.log (1819663555997 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1819663555997 / 500000000000) = -Real.log (500000000000 / 1819663555997) := by
    rw [show ((1819663555997 / 500000000000) : ℝ) = ((500000000000 / 1819663555997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (648693823 / 500000000) ≤ -Real.log (500000000000 / 1829861839193) ∧
    -Real.log (500000000000 / 1829861839193) ≤ (10135841 / 7812500) := by
  have h := checkLog_sound (w := (829861839193 / 2829861839193)) (n := 12)
    (lo := (302120233 / 500000000)) (hi := (604240467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1829861839193 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1829861839193 / 1000000000000) = 1/(500000000000 / 1829861839193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (648693823 / 500000000) (10135841 / 7812500) (Real.log (1829861839193 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1829861839193 / 500000000000) = -Real.log (500000000000 / 1829861839193) := by
    rw [show ((1829861839193 / 500000000000) : ℝ) = ((500000000000 / 1829861839193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (948435819 / 1000000000) ≤ -Real.log (500000000000 / 1290834152639) ∧
    -Real.log (500000000000 / 1290834152639) ≤ (948435821 / 1000000000) := by
  have h := checkLog_sound (w := (290834152639 / 2290834152639)) (n := 12)
    (lo := (255288639 / 1000000000)) (hi := (797777 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290834152639 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1290834152639 / 1000000000000) = 1/(500000000000 / 1290834152639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (948435819 / 1000000000) (948435821 / 1000000000) (Real.log (1290834152639 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1290834152639 / 500000000000) = -Real.log (500000000000 / 1290834152639) := by
    rw [show ((1290834152639 / 500000000000) : ℝ) = ((500000000000 / 1290834152639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (238196973 / 250000000) ≤ -Real.log (125000000000 / 324116049791) ∧
    -Real.log (125000000000 / 324116049791) ≤ (476393947 / 500000000) := by
  have h := checkLog_sound (w := (74116049791 / 574116049791)) (n := 12)
    (lo := (32455089 / 125000000)) (hi := (259640713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324116049791 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(324116049791 / 250000000000) = 1/(125000000000 / 324116049791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (238196973 / 250000000) (476393947 / 500000000) (Real.log (324116049791 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (324116049791 / 125000000000) = -Real.log (125000000000 / 324116049791) := by
    rw [show ((324116049791 / 125000000000) : ℝ) = ((125000000000 / 324116049791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0105

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0106Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0106
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

theorem reflection_log_1_neg : (82086951 / 250000000) ≤ -Real.log (512 / 711) ∧
    -Real.log (512 / 711) ≤ (65669561 / 200000000) := by
  have h := checkLog_sound (w := (199 / 1223)) (n := 12)
    (lo := (82086951 / 250000000)) (hi := (65669561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711 / 512) = 1/(512 / 711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (82086951 / 250000000) (65669561 / 200000000) (Real.log (711 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (711 / 512) = -Real.log (512 / 711) := by
    rw [show ((711 / 512) : ℝ) = ((512 / 711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246060717 / 500000000) ≤ -Real.log (313 / 512) ∧
    -Real.log (313 / 512) ≤ (98424287 / 200000000) := by
  have h := checkLog_sound (w := (199 / 825)) (n := 12)
    (lo := (246060717 / 500000000)) (hi := (98424287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 313) = 1/(313 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-98424287 / 200000000) (-246060717 / 500000000) (Real.log (313 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (163751783 / 500000000) ≤ -Real.log (80 / 111) ∧
    -Real.log (80 / 111) ≤ (327503567 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 191)) (n := 12)
    (lo := (163751783 / 500000000)) (hi := (327503567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 80) = 1/(80 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (163751783 / 500000000) (327503567 / 1000000000) (Real.log (111 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (111 / 80) = -Real.log (80 / 111) := by
    rw [show ((111 / 80) : ℝ) = ((80 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3829737 / 7812500) ≤ -Real.log (49 / 80) ∧
    -Real.log (49 / 80) ≤ (490206337 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 129)) (n := 12)
    (lo := (3829737 / 7812500)) (hi := (490206337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 49) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 49) = 1/(49 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-490206337 / 1000000000) (-3829737 / 7812500) (Real.log (49 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (287559987 / 500000000) ≤ -Real.log (256 / 455) ∧
    -Real.log (256 / 455) ≤ (23004799 / 40000000) := by
  have h := checkLog_sound (w := (199 / 711)) (n := 12)
    (lo := (287559987 / 500000000)) (hi := (23004799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455 / 256) = 1/(256 / 455) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (287559987 / 500000000) (23004799 / 40000000) (Real.log (455 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (455 / 256) = -Real.log (256 / 455) := by
    rw [show ((455 / 256) : ℝ) = ((256 / 455) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (60085047 / 40000000) ≤ -Real.log (57 / 256) ∧
    -Real.log (57 / 256) ≤ (751063089 / 500000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 57) = 1/(57 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-751063089 / 500000000) (-60085047 / 40000000) (Real.log (57 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (286900211 / 500000000) ≤ -Real.log (40 / 71) ∧
    -Real.log (40 / 71) ≤ (573800423 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 111)) (n := 12)
    (lo := (286900211 / 500000000)) (hi := (573800423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71 / 40) = 1/(40 / 71) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (286900211 / 500000000) (573800423 / 1000000000) (Real.log (71 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (71 / 40) = -Real.log (40 / 71) := by
    rw [show ((71 / 40) : ℝ) = ((40 / 71) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (11933239 / 8000000) ≤ -Real.log (9 / 40) ∧
    -Real.log (9 / 40) ≤ (745827439 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10 / 9) = 1/(9 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-745827439 / 500000000) (-11933239 / 8000000) (Real.log (9 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (224587863 / 500000000) ≤ -Real.log (50000 / 78351) ∧
    -Real.log (50000 / 78351) ≤ (449175727 / 1000000000) := by
  have h := checkLog_sound (w := (28351 / 128351)) (n := 12)
    (lo := (224587863 / 500000000)) (hi := (449175727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78351 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78351 / 50000) = 1/(50000 / 78351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (224587863 / 500000000) (449175727 / 1000000000) (Real.log (78351 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78351 / 50000) = -Real.log (50000 / 78351) := by
    rw [show ((78351 / 50000) : ℝ) = ((50000 / 78351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41853187 / 50000000) ≤ -Real.log (21649 / 50000) ∧
    -Real.log (21649 / 50000) ≤ (418531871 / 500000000) := by
  have h := checkLog_sound (w := (3351 / 46649)) (n := 12)
    (lo := (1798957 / 12500000)) (hi := (143916561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21649) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 21649) = 1/(21649 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-418531871 / 500000000) (-41853187 / 50000000) (Real.log (21649 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (450377923 / 1000000000) ≤ -Real.log (200000 / 313781) ∧
    -Real.log (200000 / 313781) ≤ (112594481 / 250000000) := by
  have h := checkLog_sound (w := (113781 / 513781)) (n := 12)
    (lo := (450377923 / 1000000000)) (hi := (112594481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313781 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313781 / 200000) = 1/(200000 / 313781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (450377923 / 1000000000) (112594481 / 250000000) (Real.log (313781 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (313781 / 200000) = -Real.log (200000 / 313781) := by
    rw [show ((313781 / 200000) : ℝ) = ((200000 / 313781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (420713397 / 500000000) ≤ -Real.log (86219 / 200000) ∧
    -Real.log (86219 / 200000) ≤ (210356699 / 250000000) := by
  have h := checkLog_sound (w := (13781 / 186219)) (n := 12)
    (lo := (74139807 / 500000000)) (hi := (29655923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 86219) = 1/(86219 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210356699 / 250000000) (-420713397 / 500000000) (Real.log (86219 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45568149 / 125000000) ≤ -Real.log (1000000 / 1439859) ∧
    -Real.log (1000000 / 1439859) ≤ (364545193 / 1000000000) := by
  have h := checkLog_sound (w := (439859 / 2439859)) (n := 12)
    (lo := (45568149 / 125000000)) (hi := (364545193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439859 / 1000000) = 1/(1000000 / 1439859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45568149 / 125000000) (364545193 / 1000000000) (Real.log (1439859 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1439859 / 1000000) = -Real.log (1000000 / 1439859) := by
    rw [show ((1439859 / 1000000) : ℝ) = ((1000000 / 1439859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (579566741 / 1000000000) ≤ -Real.log (560141 / 1000000) ∧
    -Real.log (560141 / 1000000) ≤ (289783371 / 500000000) := by
  have h := checkLog_sound (w := (439859 / 1560141)) (n := 12)
    (lo := (579566741 / 1000000000)) (hi := (289783371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 560141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 560141) = 1/(560141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-289783371 / 500000000) (-579566741 / 1000000000) (Real.log (560141 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73150999 / 200000000) ≤ -Real.log (500000 / 720801) ∧
    -Real.log (500000 / 720801) ≤ (91438749 / 250000000) := by
  have h := checkLog_sound (w := (220801 / 1220801)) (n := 12)
    (lo := (73150999 / 200000000)) (hi := (91438749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720801 / 500000) = 1/(500000 / 720801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73150999 / 200000000) (91438749 / 250000000) (Real.log (720801 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (720801 / 500000) = -Real.log (500000 / 720801) := by
    rw [show ((720801 / 500000) : ℝ) = ((500000 / 720801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (582683309 / 1000000000) ≤ -Real.log (279199 / 500000) ∧
    -Real.log (279199 / 500000) ≤ (58268331 / 100000000) := by
  have h := checkLog_sound (w := (220801 / 779199)) (n := 12)
    (lo := (582683309 / 1000000000)) (hi := (58268331 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 279199) = 1/(279199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-58268331 / 100000000) (-582683309 / 1000000000) (Real.log (279199 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1286239467 / 1000000000) ≤ -Real.log (500000000000 / 1809575500023) ∧
    -Real.log (500000000000 / 1809575500023) ≤ (1286239469 / 1000000000) := by
  have h := checkLog_sound (w := (809575500023 / 2809575500023)) (n := 12)
    (lo := (593092287 / 1000000000)) (hi := (9267067 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809575500023 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1809575500023 / 1000000000000) = 1/(500000000000 / 1809575500023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1286239467 / 1000000000) (1286239469 / 1000000000) (Real.log (1809575500023 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1809575500023 / 500000000000) = -Real.log (500000000000 / 1809575500023) := by
    rw [show ((1809575500023 / 500000000000) : ℝ) = ((500000000000 / 1809575500023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (645902359 / 500000000) ≤ -Real.log (250000000000 / 909837158863) ∧
    -Real.log (250000000000 / 909837158863) ≤ (16147559 / 12500000) := by
  have h := checkLog_sound (w := (409837158863 / 1409837158863)) (n := 12)
    (lo := (299328769 / 500000000)) (hi := (598657539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909837158863 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(909837158863 / 500000000000) = 1/(250000000000 / 909837158863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (645902359 / 500000000) (16147559 / 12500000) (Real.log (909837158863 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (909837158863 / 250000000000) = -Real.log (250000000000 / 909837158863) := by
    rw [show ((909837158863 / 250000000000) : ℝ) = ((250000000000 / 909837158863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (236027983 / 250000000) ≤ -Real.log (250000000000 / 642632390773) ∧
    -Real.log (250000000000 / 642632390773) ≤ (472055967 / 500000000) := by
  have h := checkLog_sound (w := (142632390773 / 1142632390773)) (n := 12)
    (lo := (15685297 / 62500000)) (hi := (250964753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642632390773 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(642632390773 / 500000000000) = 1/(250000000000 / 642632390773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (236027983 / 250000000) (472055967 / 500000000) (Real.log (642632390773 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (642632390773 / 250000000000) = -Real.log (250000000000 / 642632390773) := by
    rw [show ((642632390773 / 250000000000) : ℝ) = ((250000000000 / 642632390773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (948438303 / 1000000000) ≤ -Real.log (500000000000 / 1290837359733) ∧
    -Real.log (500000000000 / 1290837359733) ≤ (189687661 / 200000000) := by
  have h := checkLog_sound (w := (290837359733 / 2290837359733)) (n := 12)
    (lo := (255291123 / 1000000000)) (hi := (63822781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290837359733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1290837359733 / 1000000000000) = 1/(500000000000 / 1290837359733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (948438303 / 1000000000) (189687661 / 200000000) (Real.log (1290837359733 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1290837359733 / 500000000000) = -Real.log (500000000000 / 1290837359733) := by
    rw [show ((1290837359733 / 500000000000) : ℝ) = ((500000000000 / 1290837359733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0106

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0107Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0107
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

theorem reflection_log_1_neg : (163751783 / 500000000) ≤ -Real.log (80 / 111) ∧
    -Real.log (80 / 111) ≤ (327503567 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 191)) (n := 12)
    (lo := (163751783 / 500000000)) (hi := (327503567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 80) = 1/(80 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (163751783 / 500000000) (327503567 / 1000000000) (Real.log (111 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (111 / 80) = -Real.log (80 / 111) := by
    rw [show ((111 / 80) : ℝ) = ((80 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3829737 / 7812500) ≤ -Real.log (49 / 80) ∧
    -Real.log (49 / 80) ≤ (490206337 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 129)) (n := 12)
    (lo := (3829737 / 7812500)) (hi := (490206337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 49) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 49) = 1/(49 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-490206337 / 1000000000) (-3829737 / 7812500) (Real.log (49 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65331723 / 200000000) ≤ -Real.log (2560 / 3549) ∧
    -Real.log (2560 / 3549) ≤ (40832327 / 125000000) := by
  have h := checkLog_sound (w := (989 / 6109)) (n := 12)
    (lo := (65331723 / 200000000)) (hi := (40832327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3549 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3549 / 2560) = 1/(2560 / 3549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65331723 / 200000000) (40832327 / 125000000) (Real.log (3549 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3549 / 2560) = -Real.log (2560 / 3549) := by
    rw [show ((3549 / 2560) : ℝ) = ((2560 / 3549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (488294899 / 1000000000) ≤ -Real.log (1571 / 2560) ∧
    -Real.log (1571 / 2560) ≤ (4882949 / 10000000) := by
  have h := checkLog_sound (w := (989 / 4131)) (n := 12)
    (lo := (488294899 / 1000000000)) (hi := (4882949 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1571) = 1/(1571 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4882949 / 10000000) (-488294899 / 1000000000) (Real.log (1571 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (286900211 / 500000000) ≤ -Real.log (40 / 71) ∧
    -Real.log (40 / 71) ≤ (573800423 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 111)) (n := 12)
    (lo := (286900211 / 500000000)) (hi := (573800423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71 / 40) = 1/(40 / 71) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (286900211 / 500000000) (573800423 / 1000000000) (Real.log (71 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (71 / 40) = -Real.log (40 / 71) := by
    rw [show ((71 / 40) : ℝ) = ((40 / 71) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (11933239 / 8000000) ≤ -Real.log (9 / 40) ∧
    -Real.log (9 / 40) ≤ (745827439 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10 / 9) = 1/(9 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-745827439 / 500000000) (-11933239 / 8000000) (Real.log (9 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (572479127 / 1000000000) ≤ -Real.log (1280 / 2269) ∧
    -Real.log (1280 / 2269) ≤ (71559891 / 125000000) := by
  have h := checkLog_sound (w := (989 / 3549)) (n := 12)
    (lo := (572479127 / 1000000000)) (hi := (71559891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2269 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2269 / 1280) = 1/(1280 / 2269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (572479127 / 1000000000) (71559891 / 125000000) (Real.log (2269 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2269 / 1280) = -Real.log (1280 / 2269) := by
    rw [show ((2269 / 1280) : ℝ) = ((1280 / 2269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (185161511 / 125000000) ≤ -Real.log (291 / 1280) ∧
    -Real.log (291 / 1280) ≤ (1481292091 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 291) = 1/(291 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1481292091 / 1000000000) (-185161511 / 125000000) (Real.log (291 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (111993819 / 250000000) ≤ -Real.log (50000 / 78257) ∧
    -Real.log (50000 / 78257) ≤ (447975277 / 1000000000) := by
  have h := checkLog_sound (w := (28257 / 128257)) (n := 12)
    (lo := (111993819 / 250000000)) (hi := (447975277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78257 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78257 / 50000) = 1/(50000 / 78257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (111993819 / 250000000) (447975277 / 1000000000) (Real.log (78257 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78257 / 50000) = -Real.log (50000 / 78257) := by
    rw [show ((78257 / 50000) : ℝ) = ((50000 / 78257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (416365569 / 500000000) ≤ -Real.log (21743 / 50000) ∧
    -Real.log (21743 / 50000) ≤ (41636557 / 50000000) := by
  have h := checkLog_sound (w := (3257 / 46743)) (n := 12)
    (lo := (69791979 / 500000000)) (hi := (139583959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21743) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 21743) = 1/(21743 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-41636557 / 50000000) (-416365569 / 500000000) (Real.log (21743 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (112294091 / 250000000) ≤ -Real.log (1000000 / 1567021) ∧
    -Real.log (1000000 / 1567021) ≤ (89835273 / 200000000) := by
  have h := checkLog_sound (w := (567021 / 2567021)) (n := 12)
    (lo := (112294091 / 250000000)) (hi := (89835273 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1567021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1567021 / 1000000) = 1/(1000000 / 1567021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (112294091 / 250000000) (89835273 / 200000000) (Real.log (1567021 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1567021 / 1000000) = -Real.log (1000000 / 1567021) := by
    rw [show ((1567021 / 1000000) : ℝ) = ((1000000 / 1567021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16741321 / 20000000) ≤ -Real.log (432979 / 1000000) ∧
    -Real.log (432979 / 1000000) ≤ (209266513 / 250000000) := by
  have h := checkLog_sound (w := (67021 / 932979)) (n := 12)
    (lo := (14391887 / 100000000)) (hi := (143918871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 432979) = 1/(432979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-209266513 / 250000000) (-16741321 / 20000000) (Real.log (432979 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (72667619 / 200000000) ≤ -Real.log (500000 / 719061) ∧
    -Real.log (500000 / 719061) ≤ (22708631 / 62500000) := by
  have h := checkLog_sound (w := (219061 / 1219061)) (n := 12)
    (lo := (72667619 / 200000000)) (hi := (22708631 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719061 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719061 / 500000) = 1/(500000 / 719061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (72667619 / 200000000) (22708631 / 62500000) (Real.log (719061 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (719061 / 500000) = -Real.log (500000 / 719061) := by
    rw [show ((719061 / 500000) : ℝ) = ((500000 / 719061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (288235267 / 500000000) ≤ -Real.log (280939 / 500000) ∧
    -Real.log (280939 / 500000) ≤ (115294107 / 200000000) := by
  have h := checkLog_sound (w := (219061 / 780939)) (n := 12)
    (lo := (288235267 / 500000000)) (hi := (115294107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 280939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 280939) = 1/(280939 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-115294107 / 200000000) (-288235267 / 500000000) (Real.log (280939 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (182272943 / 500000000) ≤ -Real.log (50000 / 71993) ∧
    -Real.log (50000 / 71993) ≤ (364545887 / 1000000000) := by
  have h := checkLog_sound (w := (21993 / 121993)) (n := 12)
    (lo := (182272943 / 500000000)) (hi := (364545887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71993 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71993 / 50000) = 1/(50000 / 71993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (182272943 / 500000000) (364545887 / 1000000000) (Real.log (71993 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (71993 / 50000) = -Real.log (50000 / 71993) := by
    rw [show ((71993 / 50000) : ℝ) = ((50000 / 71993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (289784263 / 500000000) ≤ -Real.log (28007 / 50000) ∧
    -Real.log (28007 / 50000) ≤ (579568527 / 1000000000) := by
  have h := checkLog_sound (w := (21993 / 78007)) (n := 12)
    (lo := (289784263 / 500000000)) (hi := (579568527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 28007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 28007) = 1/(28007 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-579568527 / 1000000000) (-289784263 / 500000000) (Real.log (28007 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (256141283 / 200000000) ≤ -Real.log (25000000000 / 89979533643) ∧
    -Real.log (25000000000 / 89979533643) ≤ (1280706417 / 1000000000) := by
  have h := checkLog_sound (w := (39979533643 / 139979533643)) (n := 12)
    (lo := (117511847 / 200000000)) (hi := (146889809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89979533643 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(89979533643 / 50000000000) = 1/(25000000000 / 89979533643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (256141283 / 200000000) (1280706417 / 1000000000) (Real.log (89979533643 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (89979533643 / 25000000000) = -Real.log (25000000000 / 89979533643) := by
    rw [show ((89979533643 / 25000000000) : ℝ) = ((25000000000 / 89979533643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (257248483 / 200000000) ≤ -Real.log (20000000000 / 72383233367) ∧
    -Real.log (20000000000 / 72383233367) ≤ (1286242417 / 1000000000) := by
  have h := checkLog_sound (w := (32383233367 / 112383233367)) (n := 12)
    (lo := (118619047 / 200000000)) (hi := (148273809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72383233367 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(72383233367 / 40000000000) = 1/(20000000000 / 72383233367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (257248483 / 200000000) (1286242417 / 1000000000) (Real.log (72383233367 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (72383233367 / 20000000000) = -Real.log (20000000000 / 72383233367) := by
    rw [show ((72383233367 / 20000000000) : ℝ) = ((20000000000 / 72383233367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (939808629 / 1000000000) ≤ -Real.log (62500000000 / 159968222639) ∧
    -Real.log (62500000000 / 159968222639) ≤ (939808631 / 1000000000) := by
  have h := checkLog_sound (w := (34968222639 / 284968222639)) (n := 12)
    (lo := (246661449 / 1000000000)) (hi := (4933229 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159968222639 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(159968222639 / 125000000000) = 1/(62500000000 / 159968222639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (939808629 / 1000000000) (939808631 / 1000000000) (Real.log (159968222639 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (159968222639 / 62500000000) = -Real.log (62500000000 / 159968222639) := by
    rw [show ((159968222639 / 62500000000) : ℝ) = ((62500000000 / 159968222639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (236028603 / 250000000) ≤ -Real.log (500000000000 / 1285267968723) ∧
    -Real.log (500000000000 / 1285267968723) ≤ (472057207 / 500000000) := by
  have h := checkLog_sound (w := (285267968723 / 2285267968723)) (n := 12)
    (lo := (3921363 / 15625000)) (hi := (250967233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285267968723 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1285267968723 / 1000000000000) = 1/(500000000000 / 1285267968723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (236028603 / 250000000) (472057207 / 500000000) (Real.log (1285267968723 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1285267968723 / 500000000000) = -Real.log (500000000000 / 1285267968723) := by
    rw [show ((1285267968723 / 500000000000) : ℝ) = ((500000000000 / 1285267968723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0107

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0108Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0108
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

theorem reflection_log_1_neg : (65331723 / 200000000) ≤ -Real.log (2560 / 3549) ∧
    -Real.log (2560 / 3549) ≤ (40832327 / 125000000) := by
  have h := checkLog_sound (w := (989 / 6109)) (n := 12)
    (lo := (65331723 / 200000000)) (hi := (40832327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3549 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3549 / 2560) = 1/(2560 / 3549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65331723 / 200000000) (40832327 / 125000000) (Real.log (3549 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3549 / 2560) = -Real.log (2560 / 3549) := by
    rw [show ((3549 / 2560) : ℝ) = ((2560 / 3549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (488294899 / 1000000000) ≤ -Real.log (1571 / 2560) ∧
    -Real.log (1571 / 2560) ≤ (4882949 / 10000000) := by
  have h := checkLog_sound (w := (989 / 4131)) (n := 12)
    (lo := (488294899 / 1000000000)) (hi := (4882949 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1571) = 1/(1571 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4882949 / 10000000) (-488294899 / 1000000000) (Real.log (1571 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325812949 / 1000000000) ≤ -Real.log (1280 / 1773) ∧
    -Real.log (1280 / 1773) ≤ (6516259 / 20000000) := by
  have h := checkLog_sound (w := (493 / 3053)) (n := 12)
    (lo := (325812949 / 1000000000)) (hi := (6516259 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773 / 1280) = 1/(1280 / 1773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325812949 / 1000000000) (6516259 / 20000000) (Real.log (1773 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1773 / 1280) = -Real.log (1280 / 1773) := by
    rw [show ((1773 / 1280) : ℝ) = ((1280 / 1773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121596777 / 250000000) ≤ -Real.log (787 / 1280) ∧
    -Real.log (787 / 1280) ≤ (486387109 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2067)) (n := 12)
    (lo := (121596777 / 250000000)) (hi := (486387109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 787) = 1/(787 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-486387109 / 1000000000) (-121596777 / 250000000) (Real.log (787 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (572479127 / 1000000000) ≤ -Real.log (1280 / 2269) ∧
    -Real.log (1280 / 2269) ≤ (71559891 / 125000000) := by
  have h := checkLog_sound (w := (989 / 3549)) (n := 12)
    (lo := (572479127 / 1000000000)) (hi := (71559891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2269 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2269 / 1280) = 1/(1280 / 2269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (572479127 / 1000000000) (71559891 / 125000000) (Real.log (2269 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2269 / 1280) = -Real.log (1280 / 2269) := by
    rw [show ((2269 / 1280) : ℝ) = ((1280 / 2269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (185161511 / 125000000) ≤ -Real.log (291 / 1280) ∧
    -Real.log (291 / 1280) ≤ (1481292091 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 291) = 1/(291 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1481292091 / 1000000000) (-185161511 / 125000000) (Real.log (291 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (142789021 / 250000000) ≤ -Real.log (640 / 1133) ∧
    -Real.log (640 / 1133) ≤ (114231217 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1773)) (n := 12)
    (lo := (142789021 / 250000000)) (hi := (114231217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133 / 640) = 1/(640 / 1133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (142789021 / 250000000) (114231217 / 200000000) (Real.log (1133 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1133 / 640) = -Real.log (640 / 1133) := by
    rw [show ((1133 / 640) : ℝ) = ((640 / 1133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (367758897 / 250000000) ≤ -Real.log (147 / 640) ∧
    -Real.log (147 / 640) ≤ (1471035591 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 147) = 1/(147 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1471035591 / 1000000000) (-367758897 / 250000000) (Real.log (147 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (446774663 / 1000000000) ≤ -Real.log (500000 / 781631) ∧
    -Real.log (500000 / 781631) ≤ (55846833 / 125000000) := by
  have h := checkLog_sound (w := (281631 / 1281631)) (n := 12)
    (lo := (446774663 / 1000000000)) (hi := (55846833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781631 / 500000) = 1/(500000 / 781631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (446774663 / 1000000000) (55846833 / 125000000) (Real.log (781631 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (781631 / 500000) = -Real.log (500000 / 781631) := by
    rw [show ((781631 / 500000) : ℝ) = ((500000 / 781631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (165684361 / 200000000) ≤ -Real.log (218369 / 500000) ∧
    -Real.log (218369 / 500000) ≤ (828421807 / 1000000000) := by
  have h := checkLog_sound (w := (31631 / 468369)) (n := 12)
    (lo := (1082197 / 8000000)) (hi := (67637313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 218369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 218369) = 1/(218369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-828421807 / 1000000000) (-165684361 / 200000000) (Real.log (218369 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (89595183 / 200000000) ≤ -Real.log (1000000 / 1565141) ∧
    -Real.log (1000000 / 1565141) ≤ (111993979 / 250000000) := by
  have h := checkLog_sound (w := (565141 / 2565141)) (n := 12)
    (lo := (89595183 / 200000000)) (hi := (111993979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1565141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1565141 / 1000000) = 1/(1000000 / 1565141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (89595183 / 200000000) (111993979 / 250000000) (Real.log (1565141 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1565141 / 1000000) = -Real.log (1000000 / 1565141) := by
    rw [show ((1565141 / 1000000) : ℝ) = ((1000000 / 1565141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (832733437 / 1000000000) ≤ -Real.log (434859 / 1000000) ∧
    -Real.log (434859 / 1000000) ≤ (832733439 / 1000000000) := by
  have h := checkLog_sound (w := (65141 / 934859)) (n := 12)
    (lo := (139586257 / 1000000000)) (hi := (69793129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434859) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 434859) = 1/(434859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-832733439 / 1000000000) (-832733437 / 1000000000) (Real.log (434859 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (362133021 / 1000000000) ≤ -Real.log (100000 / 143639) ∧
    -Real.log (100000 / 143639) ≤ (181066511 / 500000000) := by
  have h := checkLog_sound (w := (43639 / 243639)) (n := 12)
    (lo := (362133021 / 1000000000)) (hi := (181066511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143639 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143639 / 100000) = 1/(100000 / 143639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (362133021 / 1000000000) (181066511 / 500000000) (Real.log (143639 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (143639 / 100000) = -Real.log (100000 / 143639) := by
    rw [show ((143639 / 100000) : ℝ) = ((100000 / 143639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (143348189 / 250000000) ≤ -Real.log (56361 / 100000) ∧
    -Real.log (56361 / 100000) ≤ (573392757 / 1000000000) := by
  have h := checkLog_sound (w := (43639 / 156361)) (n := 12)
    (lo := (143348189 / 250000000)) (hi := (573392757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 56361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 56361) = 1/(56361 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-573392757 / 1000000000) (-143348189 / 250000000) (Real.log (56361 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (363338791 / 1000000000) ≤ -Real.log (1000000 / 1438123) ∧
    -Real.log (1000000 / 1438123) ≤ (45417349 / 125000000) := by
  have h := checkLog_sound (w := (438123 / 2438123)) (n := 12)
    (lo := (363338791 / 1000000000)) (hi := (45417349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1438123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1438123 / 1000000) = 1/(1000000 / 1438123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (363338791 / 1000000000) (45417349 / 125000000) (Real.log (1438123 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1438123 / 1000000) = -Real.log (1000000 / 1438123) := by
    rw [show ((1438123 / 1000000) : ℝ) = ((1000000 / 1438123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (288236157 / 500000000) ≤ -Real.log (561877 / 1000000) ∧
    -Real.log (561877 / 1000000) ≤ (115294463 / 200000000) := by
  have h := checkLog_sound (w := (438123 / 1561877)) (n := 12)
    (lo := (288236157 / 500000000)) (hi := (115294463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 561877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 561877) = 1/(561877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-115294463 / 200000000) (-288236157 / 500000000) (Real.log (561877 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1275196469 / 1000000000) ≤ -Real.log (500000000000 / 1789702292907) ∧
    -Real.log (500000000000 / 1789702292907) ≤ (1275196471 / 1000000000) := by
  have h := checkLog_sound (w := (789702292907 / 2789702292907)) (n := 12)
    (lo := (582049289 / 1000000000)) (hi := (58204929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789702292907 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1789702292907 / 1000000000000) = 1/(500000000000 / 1789702292907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1275196469 / 1000000000) (1275196471 / 1000000000) (Real.log (1789702292907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1789702292907 / 500000000000) = -Real.log (500000000000 / 1789702292907) := by
    rw [show ((1789702292907 / 500000000000) : ℝ) = ((500000000000 / 1789702292907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1280709353 / 1000000000) ≤ -Real.log (50000000000 / 179959596099) ∧
    -Real.log (50000000000 / 179959596099) ≤ (256141871 / 200000000) := by
  have h := checkLog_sound (w := (79959596099 / 279959596099)) (n := 12)
    (lo := (587562173 / 1000000000)) (hi := (293781087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179959596099 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(179959596099 / 100000000000) = 1/(50000000000 / 179959596099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1280709353 / 1000000000) (256141871 / 200000000) (Real.log (179959596099 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179959596099 / 50000000000) = -Real.log (50000000000 / 179959596099) := by
    rw [show ((179959596099 / 50000000000) : ℝ) = ((50000000000 / 179959596099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (58470361 / 62500000) ≤ -Real.log (500000000000 / 1274276538741) ∧
    -Real.log (500000000000 / 1274276538741) ≤ (467762889 / 500000000) := by
  have h := checkLog_sound (w := (274276538741 / 2274276538741)) (n := 12)
    (lo := (60594649 / 250000000)) (hi := (242378597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274276538741 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1274276538741 / 1000000000000) = 1/(500000000000 / 1274276538741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (58470361 / 62500000) (467762889 / 500000000) (Real.log (1274276538741 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1274276538741 / 500000000000) = -Real.log (500000000000 / 1274276538741) := by
    rw [show ((1274276538741 / 500000000000) : ℝ) = ((500000000000 / 1274276538741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (29369097 / 31250000) ≤ -Real.log (250000000000 / 639874474307) ∧
    -Real.log (250000000000 / 639874474307) ≤ (469905553 / 500000000) := by
  have h := checkLog_sound (w := (139874474307 / 1139874474307)) (n := 12)
    (lo := (61665981 / 250000000)) (hi := (9866557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639874474307 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(639874474307 / 500000000000) = 1/(250000000000 / 639874474307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (29369097 / 31250000) (469905553 / 500000000) (Real.log (639874474307 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (639874474307 / 250000000000) = -Real.log (250000000000 / 639874474307) := by
    rw [show ((639874474307 / 250000000000) : ℝ) = ((250000000000 / 639874474307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0108

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0109Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0109
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

theorem reflection_log_1_neg : (325812949 / 1000000000) ≤ -Real.log (1280 / 1773) ∧
    -Real.log (1280 / 1773) ≤ (6516259 / 20000000) := by
  have h := checkLog_sound (w := (493 / 3053)) (n := 12)
    (lo := (325812949 / 1000000000)) (hi := (6516259 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1773 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1773 / 1280) = 1/(1280 / 1773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325812949 / 1000000000) (6516259 / 20000000) (Real.log (1773 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1773 / 1280) = -Real.log (1280 / 1773) := by
    rw [show ((1773 / 1280) : ℝ) = ((1280 / 1773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121596777 / 250000000) ≤ -Real.log (787 / 1280) ∧
    -Real.log (787 / 1280) ≤ (486387109 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 2067)) (n := 12)
    (lo := (121596777 / 250000000)) (hi := (486387109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 787) = 1/(787 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-486387109 / 1000000000) (-121596777 / 250000000) (Real.log (787 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324966567 / 1000000000) ≤ -Real.log (2560 / 3543) ∧
    -Real.log (2560 / 3543) ≤ (40620821 / 125000000) := by
  have h := checkLog_sound (w := (983 / 6103)) (n := 12)
    (lo := (324966567 / 1000000000)) (hi := (40620821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3543 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3543 / 2560) = 1/(2560 / 3543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324966567 / 1000000000) (40620821 / 125000000) (Real.log (3543 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3543 / 2560) = -Real.log (2560 / 3543) := by
    rw [show ((3543 / 2560) : ℝ) = ((2560 / 3543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (9689659 / 20000000) ≤ -Real.log (1577 / 2560) ∧
    -Real.log (1577 / 2560) ≤ (484482951 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 4137)) (n := 12)
    (lo := (9689659 / 20000000)) (hi := (484482951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1577) = 1/(1577 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-484482951 / 1000000000) (-9689659 / 20000000) (Real.log (1577 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (142789021 / 250000000) ≤ -Real.log (640 / 1133) ∧
    -Real.log (640 / 1133) ≤ (114231217 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1773)) (n := 12)
    (lo := (142789021 / 250000000)) (hi := (114231217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133 / 640) = 1/(640 / 1133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (142789021 / 250000000) (114231217 / 200000000) (Real.log (1133 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1133 / 640) = -Real.log (640 / 1133) := by
    rw [show ((1133 / 640) : ℝ) = ((640 / 1133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (367758897 / 250000000) ≤ -Real.log (147 / 640) ∧
    -Real.log (147 / 640) ≤ (1471035591 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 147) = 1/(147 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1471035591 / 1000000000) (-367758897 / 250000000) (Real.log (147 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71228911 / 125000000) ≤ -Real.log (1280 / 2263) ∧
    -Real.log (1280 / 2263) ≤ (569831289 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 3543)) (n := 12)
    (lo := (71228911 / 125000000)) (hi := (569831289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2263 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2263 / 1280) = 1/(1280 / 2263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71228911 / 125000000) (569831289 / 1000000000) (Real.log (2263 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2263 / 1280) = -Real.log (1280 / 2263) := by
    rw [show ((2263 / 1280) : ℝ) = ((1280 / 2263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (91305201 / 62500000) ≤ -Real.log (297 / 1280) ∧
    -Real.log (297 / 1280) ≤ (1460883219 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 617)) (n := 12)
    (lo := (9323607 / 125000000)) (hi := (74588857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 297) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 297) = 1/(297 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1460883219 / 1000000000) (-91305201 / 62500000) (Real.log (297 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1740523 / 3906250) ≤ -Real.log (500000 / 780693) ∧
    -Real.log (500000 / 780693) ≤ (445573889 / 1000000000) := by
  have h := checkLog_sound (w := (280693 / 1280693)) (n := 12)
    (lo := (1740523 / 3906250)) (hi := (445573889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780693 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780693 / 500000) = 1/(500000 / 780693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1740523 / 3906250) (445573889 / 1000000000) (Real.log (780693 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (780693 / 500000) = -Real.log (500000 / 780693) := by
    rw [show ((780693 / 500000) : ℝ) = ((500000 / 780693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (824135523 / 1000000000) ≤ -Real.log (219307 / 500000) ∧
    -Real.log (219307 / 500000) ≤ (32965421 / 40000000) := by
  have h := checkLog_sound (w := (30693 / 469307)) (n := 12)
    (lo := (130988343 / 1000000000)) (hi := (16373543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219307) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 219307) = 1/(219307 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32965421 / 40000000) (-824135523 / 1000000000) (Real.log (219307 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (446775303 / 1000000000) ≤ -Real.log (1000000 / 1563263) ∧
    -Real.log (1000000 / 1563263) ≤ (55846913 / 125000000) := by
  have h := checkLog_sound (w := (563263 / 2563263)) (n := 12)
    (lo := (446775303 / 1000000000)) (hi := (55846913 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1563263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1563263 / 1000000) = 1/(1000000 / 1563263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (446775303 / 1000000000) (55846913 / 125000000) (Real.log (1563263 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1563263 / 1000000) = -Real.log (1000000 / 1563263) := by
    rw [show ((1563263 / 1000000) : ℝ) = ((1000000 / 1563263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (165684819 / 200000000) ≤ -Real.log (436737 / 1000000) ∧
    -Real.log (436737 / 1000000) ≤ (828424097 / 1000000000) := by
  have h := checkLog_sound (w := (63263 / 936737)) (n := 12)
    (lo := (27055383 / 200000000)) (hi := (33819229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436737) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 436737) = 1/(436737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-828424097 / 1000000000) (-165684819 / 200000000) (Real.log (436737 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (180464989 / 500000000) ≤ -Real.log (1000000 / 1434663) ∧
    -Real.log (1000000 / 1434663) ≤ (360929979 / 1000000000) := by
  have h := checkLog_sound (w := (434663 / 2434663)) (n := 12)
    (lo := (180464989 / 500000000)) (hi := (360929979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1434663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1434663 / 1000000) = 1/(1000000 / 1434663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (180464989 / 500000000) (360929979 / 1000000000) (Real.log (1434663 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1434663 / 1000000) = -Real.log (1000000 / 1434663) := by
    rw [show ((1434663 / 1000000) : ℝ) = ((1000000 / 1434663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114066653 / 200000000) ≤ -Real.log (565337 / 1000000) ∧
    -Real.log (565337 / 1000000) ≤ (285166633 / 500000000) := by
  have h := checkLog_sound (w := (434663 / 1565337)) (n := 12)
    (lo := (114066653 / 200000000)) (hi := (285166633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 565337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 565337) = 1/(565337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-285166633 / 500000000) (-114066653 / 200000000) (Real.log (565337 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (362133717 / 1000000000) ≤ -Real.log (1000000 / 1436391) ∧
    -Real.log (1000000 / 1436391) ≤ (181066859 / 500000000) := by
  have h := checkLog_sound (w := (436391 / 2436391)) (n := 12)
    (lo := (362133717 / 1000000000)) (hi := (181066859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1436391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1436391 / 1000000) = 1/(1000000 / 1436391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (362133717 / 1000000000) (181066859 / 500000000) (Real.log (1436391 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1436391 / 1000000) = -Real.log (1000000 / 1436391) := by
    rw [show ((1436391 / 1000000) : ℝ) = ((1000000 / 1436391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (57339453 / 100000000) ≤ -Real.log (563609 / 1000000) ∧
    -Real.log (563609 / 1000000) ≤ (573394531 / 1000000000) := by
  have h := checkLog_sound (w := (436391 / 1563609)) (n := 12)
    (lo := (57339453 / 100000000)) (hi := (573394531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 563609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 563609) = 1/(563609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-573394531 / 1000000000) (-57339453 / 100000000) (Real.log (563609 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1269709411 / 1000000000) ≤ -Real.log (500000000000 / 1779908986033) ∧
    -Real.log (500000000000 / 1779908986033) ≤ (1269709413 / 1000000000) := by
  have h := checkLog_sound (w := (779908986033 / 2779908986033)) (n := 12)
    (lo := (576562231 / 1000000000)) (hi := (72070279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779908986033 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1779908986033 / 1000000000000) = 1/(500000000000 / 1779908986033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1269709411 / 1000000000) (1269709413 / 1000000000) (Real.log (1779908986033 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1779908986033 / 500000000000) = -Real.log (500000000000 / 1779908986033) := by
    rw [show ((1779908986033 / 500000000000) : ℝ) = ((500000000000 / 1779908986033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (637599699 / 500000000) ≤ -Real.log (500000000000 / 1789707535657) ∧
    -Real.log (500000000000 / 1789707535657) ≤ (6375997 / 5000000) := by
  have h := checkLog_sound (w := (789707535657 / 2789707535657)) (n := 12)
    (lo := (291026109 / 500000000)) (hi := (582052219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789707535657 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1789707535657 / 1000000000000) = 1/(500000000000 / 1789707535657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (637599699 / 500000000) (6375997 / 5000000) (Real.log (1789707535657 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1789707535657 / 500000000000) = -Real.log (500000000000 / 1789707535657) := by
    rw [show ((1789707535657 / 500000000000) : ℝ) = ((500000000000 / 1789707535657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (931263243 / 1000000000) ≤ -Real.log (62500000000 / 158607056499) ∧
    -Real.log (62500000000 / 158607056499) ≤ (186252649 / 200000000) := by
  have h := checkLog_sound (w := (33607056499 / 283607056499)) (n := 12)
    (lo := (238116063 / 1000000000)) (hi := (7441127 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158607056499 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158607056499 / 125000000000) = 1/(62500000000 / 158607056499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (931263243 / 1000000000) (186252649 / 200000000) (Real.log (158607056499 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (158607056499 / 62500000000) = -Real.log (62500000000 / 158607056499) := by
    rw [show ((158607056499 / 62500000000) : ℝ) = ((62500000000 / 158607056499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (935528247 / 1000000000) ≤ -Real.log (100000000000 / 254855937361) ∧
    -Real.log (100000000000 / 254855937361) ≤ (935528249 / 1000000000) := by
  have h := checkLog_sound (w := (54855937361 / 454855937361)) (n := 12)
    (lo := (242381067 / 1000000000)) (hi := (60595267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254855937361 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(254855937361 / 200000000000) = 1/(100000000000 / 254855937361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (935528247 / 1000000000) (935528249 / 1000000000) (Real.log (254855937361 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (254855937361 / 100000000000) = -Real.log (100000000000 / 254855937361) := by
    rw [show ((254855937361 / 100000000000) : ℝ) = ((100000000000 / 254855937361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0109

end


