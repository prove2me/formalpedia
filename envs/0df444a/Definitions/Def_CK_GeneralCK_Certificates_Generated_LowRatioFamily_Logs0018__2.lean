-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0018__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0018__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T11:41:50.11955+00:00
-- url     : https://prove2.me/theorems/0f27f0b6-91f1-4a1a-99eb-db43bcfc5e62
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0018 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0019)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0018 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0019)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0018 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0019)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0018 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0019) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0018 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0019).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0018 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1152_neg : (82818723 / 1000000000) ≤ -Real.log (460259 / 500000) ∧
    -Real.log (460259 / 500000) ≤ (20704681 / 250000000) := by
  have h := checkLog_sound (w := (39741 / 960259)) (n := 12)
    (lo := (82818723 / 1000000000)) (hi := (20704681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460259) = 1/(460259 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1152 : Bounds (-20704681 / 250000000) (-82818723 / 1000000000) (Real.log (460259 / 500000)) := by
  have h := reflection_log_1152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1153_neg : (76674889 / 1000000000) ≤ -Real.log (1000000 / 1079691) ∧
    -Real.log (1000000 / 1079691) ≤ (7667489 / 100000000) := by
  have h := checkLog_sound (w := (79691 / 2079691)) (n := 12)
    (lo := (76674889 / 1000000000)) (hi := (7667489 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079691 / 1000000) = 1/(1000000 / 1079691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1153 : Bounds (76674889 / 1000000000) (7667489 / 100000000) (Real.log (1079691 / 1000000)) := by
  have h := reflection_log_1153_neg
  have he : Real.log (1079691 / 1000000) = -Real.log (1000000 / 1079691) := by
    rw [show ((1079691 / 1000000) : ℝ) = ((1000000 / 1079691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1154_neg : (16609159 / 200000000) ≤ -Real.log (920309 / 1000000) ∧
    -Real.log (920309 / 1000000) ≤ (20761449 / 250000000) := by
  have h := checkLog_sound (w := (79691 / 1920309)) (n := 12)
    (lo := (16609159 / 200000000)) (hi := (20761449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920309) = 1/(920309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1154 : Bounds (-20761449 / 250000000) (-16609159 / 200000000) (Real.log (920309 / 1000000)) := by
  have h := reflection_log_1154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1155_neg : (3185453 / 500000000) ≤ -Real.log (993649344519 / 1000000000000) ∧
    -Real.log (993649344519 / 1000000000000) ≤ (6370907 / 1000000000) := by
  have h := checkLog_sound (w := (6350655481 / 1993649344519)) (n := 12)
    (lo := (3185453 / 500000000)) (hi := (6370907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993649344519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993649344519) = 1/(993649344519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1155 : Bounds (-6370907 / 1000000000) (-3185453 / 500000000) (Real.log (993649344519 / 1000000000000)) := by
  have h := reflection_log_1155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1156_neg : (6337427 / 1000000000) ≤ -Real.log (248420652919 / 250000000000) ∧
    -Real.log (248420652919 / 250000000000) ≤ (1584357 / 250000000) := by
  have h := checkLog_sound (w := (1579347081 / 498420652919)) (n := 12)
    (lo := (6337427 / 1000000000)) (hi := (1584357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248420652919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248420652919) = 1/(248420652919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1156 : Bounds (-1584357 / 250000000) (-6337427 / 1000000000) (Real.log (248420652919 / 250000000000)) := by
  have h := reflection_log_1156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1157_neg : (7965001 / 50000000) ≤ -Real.log (500000000000 / 586344862349) ∧
    -Real.log (500000000000 / 586344862349) ≤ (159300021 / 1000000000) := by
  have h := checkLog_sound (w := (86344862349 / 1086344862349)) (n := 12)
    (lo := (7965001 / 50000000)) (hi := (159300021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586344862349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586344862349 / 500000000000) = 1/(500000000000 / 586344862349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1157 : Bounds (7965001 / 50000000) (159300021 / 1000000000) (Real.log (586344862349 / 500000000000)) := by
  have h := reflection_log_1157_neg
  have he : Real.log (586344862349 / 500000000000) = -Real.log (500000000000 / 586344862349) := by
    rw [show ((586344862349 / 500000000000) : ℝ) = ((500000000000 / 586344862349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1158_neg : (39930171 / 250000000) ≤ -Real.log (250000000000 / 293295784351) ∧
    -Real.log (250000000000 / 293295784351) ≤ (31944137 / 200000000) := by
  have h := checkLog_sound (w := (43295784351 / 543295784351)) (n := 12)
    (lo := (39930171 / 250000000)) (hi := (31944137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293295784351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293295784351 / 250000000000) = 1/(250000000000 / 293295784351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1158 : Bounds (39930171 / 250000000) (31944137 / 200000000) (Real.log (293295784351 / 250000000000)) := by
  have h := reflection_log_1158_neg
  have he : Real.log (293295784351 / 250000000000) = -Real.log (250000000000 / 293295784351) := by
    rw [show ((293295784351 / 250000000000) : ℝ) = ((250000000000 / 293295784351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1159_neg : (319490179 / 1000000000) ≤ -Real.log (125000000000 / 172053231939) ∧
    -Real.log (125000000000 / 172053231939) ≤ (15974509 / 50000000) := by
  have h := checkLog_sound (w := (47053231939 / 297053231939)) (n := 12)
    (lo := (319490179 / 1000000000)) (hi := (15974509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172053231939 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172053231939 / 125000000000) = 1/(125000000000 / 172053231939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1159 : Bounds (319490179 / 1000000000) (15974509 / 50000000) (Real.log (172053231939 / 125000000000)) := by
  have h := reflection_log_1159_neg
  have he : Real.log (172053231939 / 125000000000) = -Real.log (125000000000 / 172053231939) := by
    rw [show ((172053231939 / 125000000000) : ℝ) = ((125000000000 / 172053231939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1160_neg : (31969533 / 100000000) ≤ -Real.log (500000000000 / 688354129531) ∧
    -Real.log (500000000000 / 688354129531) ≤ (319695331 / 1000000000) := by
  have h := checkLog_sound (w := (188354129531 / 1188354129531)) (n := 12)
    (lo := (31969533 / 100000000)) (hi := (319695331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688354129531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688354129531 / 500000000000) = 1/(500000000000 / 688354129531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1160 : Bounds (31969533 / 100000000) (319695331 / 1000000000) (Real.log (688354129531 / 500000000000)) := by
  have h := reflection_log_1160_neg
  have he : Real.log (688354129531 / 500000000000) = -Real.log (500000000000 / 688354129531) := by
    rw [show ((688354129531 / 500000000000) : ℝ) = ((500000000000 / 688354129531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1161_neg : (147212379 / 1000000000) ≤ -Real.log (5000 / 5793) ∧
    -Real.log (5000 / 5793) ≤ (7360619 / 50000000) := by
  have h := checkLog_sound (w := (793 / 10793)) (n := 12)
    (lo := (147212379 / 1000000000)) (hi := (7360619 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5793 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5793 / 5000) = 1/(5000 / 5793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1161 : Bounds (147212379 / 1000000000) (7360619 / 50000000) (Real.log (5793 / 5000)) := by
  have h := reflection_log_1161_neg
  have he : Real.log (5793 / 5000) = -Real.log (5000 / 5793) := by
    rw [show ((5793 / 5000) : ℝ) = ((5000 / 5793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1162_neg : (172688107 / 1000000000) ≤ -Real.log (4207 / 5000) ∧
    -Real.log (4207 / 5000) ≤ (43172027 / 250000000) := by
  have h := checkLog_sound (w := (793 / 9207)) (n := 12)
    (lo := (172688107 / 1000000000)) (hi := (43172027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4207) = 1/(4207 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1162 : Bounds (-43172027 / 250000000) (-172688107 / 1000000000) (Real.log (4207 / 5000)) := by
  have h := reflection_log_1162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1163_neg : (158587 / 1000000000) ≤ -Real.log (5000000 / 5000793) ∧
    -Real.log (5000000 / 5000793) ≤ (39647 / 250000000) := by
  have h := checkLog_sound (w := (793 / 10000793)) (n := 12)
    (lo := (158587 / 1000000000)) (hi := (39647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000793 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000793 / 5000000) = 1/(5000000 / 5000793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1163 : Bounds (158587 / 1000000000) (39647 / 250000000) (Real.log (5000793 / 5000000)) := by
  have h := reflection_log_1163_neg
  have he : Real.log (5000793 / 5000000) = -Real.log (5000000 / 5000793) := by
    rw [show ((5000793 / 5000000) : ℝ) = ((5000000 / 5000793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1164_neg : (39653 / 250000000) ≤ -Real.log (4999207 / 5000000) ∧
    -Real.log (4999207 / 5000000) ≤ (158613 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 9999207)) (n := 12)
    (lo := (39653 / 250000000)) (hi := (158613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999207) = 1/(4999207 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1164 : Bounds (-158613 / 1000000000) (-39653 / 250000000) (Real.log (4999207 / 5000000)) := by
  have h := reflection_log_1164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1165_neg : (76527613 / 1000000000) ≤ -Real.log (250000 / 269883) ∧
    -Real.log (250000 / 269883) ≤ (38263807 / 500000000) := by
  have h := checkLog_sound (w := (19883 / 519883)) (n := 12)
    (lo := (76527613 / 1000000000)) (hi := (38263807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269883 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269883 / 250000) = 1/(250000 / 269883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1165 : Bounds (76527613 / 1000000000) (38263807 / 500000000) (Real.log (269883 / 250000)) := by
  have h := reflection_log_1165_neg
  have he : Real.log (269883 / 250000) = -Real.log (250000 / 269883) := by
    rw [show ((269883 / 250000) : ℝ) = ((250000 / 269883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1166_neg : (41436521 / 500000000) ≤ -Real.log (230117 / 250000) ∧
    -Real.log (230117 / 250000) ≤ (82873043 / 1000000000) := by
  have h := checkLog_sound (w := (19883 / 480117)) (n := 12)
    (lo := (41436521 / 500000000)) (hi := (82873043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230117) = 1/(230117 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1166 : Bounds (-82873043 / 1000000000) (-41436521 / 500000000) (Real.log (230117 / 250000)) := by
  have h := reflection_log_1166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1167_neg : (76722123 / 1000000000) ≤ -Real.log (500000 / 539871) ∧
    -Real.log (500000 / 539871) ≤ (19180531 / 250000000) := by
  have h := checkLog_sound (w := (39871 / 1039871)) (n := 12)
    (lo := (76722123 / 1000000000)) (hi := (19180531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539871 / 500000) = 1/(500000 / 539871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1167 : Bounds (76722123 / 1000000000) (19180531 / 250000000) (Real.log (539871 / 500000)) := by
  have h := reflection_log_1167_neg
  have he : Real.log (539871 / 500000) = -Real.log (500000 / 539871) := by
    rw [show ((539871 / 500000) : ℝ) = ((500000 / 539871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1168_neg : (83101213 / 1000000000) ≤ -Real.log (460129 / 500000) ∧
    -Real.log (460129 / 500000) ≤ (41550607 / 500000000) := by
  have h := checkLog_sound (w := (39871 / 960129)) (n := 12)
    (lo := (83101213 / 1000000000)) (hi := (41550607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460129) = 1/(460129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1168 : Bounds (-41550607 / 500000000) (-83101213 / 1000000000) (Real.log (460129 / 500000)) := by
  have h := reflection_log_1168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1169_neg : (6379089 / 1000000000) ≤ -Real.log (248410303359 / 250000000000) ∧
    -Real.log (248410303359 / 250000000000) ≤ (637909 / 100000000) := by
  have h := checkLog_sound (w := (1589696641 / 498410303359)) (n := 12)
    (lo := (6379089 / 1000000000)) (hi := (637909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248410303359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248410303359) = 1/(248410303359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1169 : Bounds (-637909 / 100000000) (-6379089 / 1000000000) (Real.log (248410303359 / 250000000000)) := by
  have h := reflection_log_1169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1170_neg : (1586357 / 250000000) ≤ -Real.log (62104666311 / 62500000000) ∧
    -Real.log (62104666311 / 62500000000) ≤ (6345429 / 1000000000) := by
  have h := checkLog_sound (w := (395333689 / 124604666311)) (n := 12)
    (lo := (1586357 / 250000000)) (hi := (6345429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62104666311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62104666311) = 1/(62104666311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1170 : Bounds (-6345429 / 1000000000) (-1586357 / 250000000) (Real.log (62104666311 / 62500000000)) := by
  have h := reflection_log_1170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1171_neg : (9962541 / 62500000) ≤ -Real.log (125000000000 / 146600968203) ∧
    -Real.log (125000000000 / 146600968203) ≤ (159400657 / 1000000000) := by
  have h := checkLog_sound (w := (21600968203 / 271600968203)) (n := 12)
    (lo := (9962541 / 62500000)) (hi := (159400657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146600968203 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146600968203 / 125000000000) = 1/(125000000000 / 146600968203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1171 : Bounds (9962541 / 62500000) (159400657 / 1000000000) (Real.log (146600968203 / 125000000000)) := by
  have h := reflection_log_1171_neg
  have he : Real.log (146600968203 / 125000000000) = -Real.log (125000000000 / 146600968203) := by
    rw [show ((146600968203 / 125000000000) : ℝ) = ((125000000000 / 146600968203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1172_neg : (159823337 / 1000000000) ≤ -Real.log (250000000000 / 293325893391) ∧
    -Real.log (250000000000 / 293325893391) ≤ (79911669 / 500000000) := by
  have h := checkLog_sound (w := (43325893391 / 543325893391)) (n := 12)
    (lo := (159823337 / 1000000000)) (hi := (79911669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293325893391 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293325893391 / 250000000000) = 1/(250000000000 / 293325893391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1172 : Bounds (159823337 / 1000000000) (79911669 / 500000000) (Real.log (293325893391 / 250000000000)) := by
  have h := reflection_log_1172_neg
  have he : Real.log (293325893391 / 250000000000) = -Real.log (250000000000 / 293325893391) := by
    rw [show ((293325893391 / 250000000000) : ℝ) = ((250000000000 / 293325893391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1173_neg : (31969533 / 100000000) ≤ -Real.log (50000000000 / 68835412953) ∧
    -Real.log (50000000000 / 68835412953) ≤ (319695331 / 1000000000) := by
  have h := checkLog_sound (w := (18835412953 / 118835412953)) (n := 12)
    (lo := (31969533 / 100000000)) (hi := (319695331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68835412953 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68835412953 / 50000000000) = 1/(50000000000 / 68835412953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1173 : Bounds (31969533 / 100000000) (319695331 / 1000000000) (Real.log (68835412953 / 50000000000)) := by
  have h := reflection_log_1173_neg
  have he : Real.log (68835412953 / 50000000000) = -Real.log (50000000000 / 68835412953) := by
    rw [show ((68835412953 / 50000000000) : ℝ) = ((50000000000 / 68835412953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1174_neg : (319900487 / 1000000000) ≤ -Real.log (500000000000 / 688495364869) ∧
    -Real.log (500000000000 / 688495364869) ≤ (39987561 / 125000000) := by
  have h := checkLog_sound (w := (188495364869 / 1188495364869)) (n := 12)
    (lo := (319900487 / 1000000000)) (hi := (39987561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688495364869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688495364869 / 500000000000) = 1/(500000000000 / 688495364869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1174 : Bounds (319900487 / 1000000000) (39987561 / 125000000) (Real.log (688495364869 / 500000000000)) := by
  have h := reflection_log_1174_neg
  have he : Real.log (688495364869 / 500000000000) = -Real.log (500000000000 / 688495364869) := by
    rw [show ((688495364869 / 500000000000) : ℝ) = ((500000000000 / 688495364869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1175_neg : (147298687 / 1000000000) ≤ -Real.log (10000 / 11587) ∧
    -Real.log (10000 / 11587) ≤ (1150771 / 7812500) := by
  have h := checkLog_sound (w := (1587 / 21587)) (n := 12)
    (lo := (147298687 / 1000000000)) (hi := (1150771 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11587 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11587 / 10000) = 1/(10000 / 11587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1175 : Bounds (147298687 / 1000000000) (1150771 / 7812500) (Real.log (11587 / 10000)) := by
  have h := reflection_log_1175_neg
  have he : Real.log (11587 / 10000) = -Real.log (10000 / 11587) := by
    rw [show ((11587 / 10000) : ℝ) = ((10000 / 11587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1176_neg : (43201741 / 250000000) ≤ -Real.log (8413 / 10000) ∧
    -Real.log (8413 / 10000) ≤ (34561393 / 200000000) := by
  have h := checkLog_sound (w := (1587 / 18413)) (n := 12)
    (lo := (43201741 / 250000000)) (hi := (34561393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8413) = 1/(8413 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1176 : Bounds (-34561393 / 200000000) (-43201741 / 250000000) (Real.log (8413 / 10000)) := by
  have h := reflection_log_1176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1177_neg : (158687 / 1000000000) ≤ -Real.log (10000000 / 10001587) ∧
    -Real.log (10000000 / 10001587) ≤ (4959 / 31250000) := by
  have h := checkLog_sound (w := (1587 / 20001587)) (n := 12)
    (lo := (158687 / 1000000000)) (hi := (4959 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001587 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001587 / 10000000) = 1/(10000000 / 10001587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1177 : Bounds (158687 / 1000000000) (4959 / 31250000) (Real.log (10001587 / 10000000)) := by
  have h := reflection_log_1177_neg
  have he : Real.log (10001587 / 10000000) = -Real.log (10000000 / 10001587) := by
    rw [show ((10001587 / 10000000) : ℝ) = ((10000000 / 10001587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1178_neg : (19839 / 125000000) ≤ -Real.log (9998413 / 10000000) ∧
    -Real.log (9998413 / 10000000) ≤ (158713 / 1000000000) := by
  have h := checkLog_sound (w := (1587 / 19998413)) (n := 12)
    (lo := (19839 / 125000000)) (hi := (158713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998413) = 1/(9998413 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1178 : Bounds (-158713 / 1000000000) (-19839 / 125000000) (Real.log (9998413 / 10000000)) := by
  have h := reflection_log_1178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1179_neg : (15314971 / 200000000) ≤ -Real.log (1000000 / 1079583) ∧
    -Real.log (1000000 / 1079583) ≤ (9571857 / 125000000) := by
  have h := checkLog_sound (w := (79583 / 2079583)) (n := 12)
    (lo := (15314971 / 200000000)) (hi := (9571857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079583 / 1000000) = 1/(1000000 / 1079583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1179 : Bounds (15314971 / 200000000) (9571857 / 125000000) (Real.log (1079583 / 1000000)) := by
  have h := reflection_log_1179_neg
  have he : Real.log (1079583 / 1000000) = -Real.log (1000000 / 1079583) := by
    rw [show ((1079583 / 1000000) : ℝ) = ((1000000 / 1079583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1180_neg : (1658569 / 20000000) ≤ -Real.log (920417 / 1000000) ∧
    -Real.log (920417 / 1000000) ≤ (82928451 / 1000000000) := by
  have h := checkLog_sound (w := (79583 / 1920417)) (n := 12)
    (lo := (1658569 / 20000000)) (hi := (82928451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920417) = 1/(920417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1180 : Bounds (-82928451 / 1000000000) (-1658569 / 20000000) (Real.log (920417 / 1000000)) := by
  have h := reflection_log_1180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1181_neg : (19192339 / 250000000) ≤ -Real.log (1000000 / 1079793) ∧
    -Real.log (1000000 / 1079793) ≤ (76769357 / 1000000000) := by
  have h := checkLog_sound (w := (79793 / 2079793)) (n := 12)
    (lo := (19192339 / 250000000)) (hi := (76769357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079793 / 1000000) = 1/(1000000 / 1079793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1181 : Bounds (19192339 / 250000000) (76769357 / 1000000000) (Real.log (1079793 / 1000000)) := by
  have h := reflection_log_1181_neg
  have he : Real.log (1079793 / 1000000) = -Real.log (1000000 / 1079793) := by
    rw [show ((1079793 / 1000000) : ℝ) = ((1000000 / 1079793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1182_neg : (41578317 / 500000000) ≤ -Real.log (920207 / 1000000) ∧
    -Real.log (920207 / 1000000) ≤ (16631327 / 200000000) := by
  have h := checkLog_sound (w := (79793 / 1920207)) (n := 12)
    (lo := (41578317 / 500000000)) (hi := (16631327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920207) = 1/(920207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1182 : Bounds (-16631327 / 200000000) (-41578317 / 500000000) (Real.log (920207 / 1000000)) := by
  have h := reflection_log_1182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1183_neg : (3193639 / 500000000) ≤ -Real.log (993633077151 / 1000000000000) ∧
    -Real.log (993633077151 / 1000000000000) ≤ (6387279 / 1000000000) := by
  have h := checkLog_sound (w := (6366922849 / 1993633077151)) (n := 12)
    (lo := (3193639 / 500000000)) (hi := (6387279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993633077151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993633077151) = 1/(993633077151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1183 : Bounds (-6387279 / 1000000000) (-3193639 / 500000000) (Real.log (993633077151 / 1000000000000)) := by
  have h := reflection_log_1183_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1184_neg : (1270719 / 200000000) ≤ -Real.log (993666546111 / 1000000000000) ∧
    -Real.log (993666546111 / 1000000000000) ≤ (1588399 / 250000000) := by
  have h := checkLog_sound (w := (6333453889 / 1993666546111)) (n := 12)
    (lo := (1270719 / 200000000)) (hi := (1588399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993666546111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993666546111) = 1/(993666546111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1184 : Bounds (-1588399 / 250000000) (-1270719 / 200000000) (Real.log (993666546111 / 1000000000000)) := by
  have h := reflection_log_1184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1185_neg : (79751653 / 500000000) ≤ -Real.log (500000000000 / 586464070089) ∧
    -Real.log (500000000000 / 586464070089) ≤ (159503307 / 1000000000) := by
  have h := checkLog_sound (w := (86464070089 / 1086464070089)) (n := 12)
    (lo := (79751653 / 500000000)) (hi := (159503307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586464070089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586464070089 / 500000000000) = 1/(500000000000 / 586464070089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1185 : Bounds (79751653 / 500000000) (159503307 / 1000000000) (Real.log (586464070089 / 500000000000)) := by
  have h := reflection_log_1185_neg
  have he : Real.log (586464070089 / 500000000000) = -Real.log (500000000000 / 586464070089) := by
    rw [show ((586464070089 / 500000000000) : ℝ) = ((500000000000 / 586464070089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1186_neg : (15992599 / 100000000) ≤ -Real.log (500000000000 / 586712011537) ∧
    -Real.log (500000000000 / 586712011537) ≤ (159925991 / 1000000000) := by
  have h := checkLog_sound (w := (86712011537 / 1086712011537)) (n := 12)
    (lo := (15992599 / 100000000)) (hi := (159925991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586712011537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586712011537 / 500000000000) = 1/(500000000000 / 586712011537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1186 : Bounds (15992599 / 100000000) (159925991 / 1000000000) (Real.log (586712011537 / 500000000000)) := by
  have h := reflection_log_1186_neg
  have he : Real.log (586712011537 / 500000000000) = -Real.log (500000000000 / 586712011537) := by
    rw [show ((586712011537 / 500000000000) : ℝ) = ((500000000000 / 586712011537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1187_neg : (319900487 / 1000000000) ≤ -Real.log (125000000000 / 172123841217) ∧
    -Real.log (125000000000 / 172123841217) ≤ (39987561 / 125000000) := by
  have h := checkLog_sound (w := (47123841217 / 297123841217)) (n := 12)
    (lo := (319900487 / 1000000000)) (hi := (39987561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172123841217 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172123841217 / 125000000000) = 1/(125000000000 / 172123841217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1187 : Bounds (319900487 / 1000000000) (39987561 / 125000000) (Real.log (172123841217 / 125000000000)) := by
  have h := reflection_log_1187_neg
  have he : Real.log (172123841217 / 125000000000) = -Real.log (125000000000 / 172123841217) := by
    rw [show ((172123841217 / 125000000000) : ℝ) = ((125000000000 / 172123841217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1188_neg : (320105651 / 1000000000) ≤ -Real.log (250000000000 / 344318316891) ∧
    -Real.log (250000000000 / 344318316891) ≤ (80026413 / 250000000) := by
  have h := checkLog_sound (w := (94318316891 / 594318316891)) (n := 12)
    (lo := (320105651 / 1000000000)) (hi := (80026413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344318316891 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344318316891 / 250000000000) = 1/(250000000000 / 344318316891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1188 : Bounds (320105651 / 1000000000) (80026413 / 250000000) (Real.log (344318316891 / 250000000000)) := by
  have h := reflection_log_1188_neg
  have he : Real.log (344318316891 / 250000000000) = -Real.log (250000000000 / 344318316891) := by
    rw [show ((344318316891 / 250000000000) : ℝ) = ((250000000000 / 344318316891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1189_neg : (73692493 / 500000000) ≤ -Real.log (2500 / 2897) ∧
    -Real.log (2500 / 2897) ≤ (147384987 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 5397)) (n := 12)
    (lo := (73692493 / 500000000)) (hi := (147384987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2897 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2897 / 2500) = 1/(2500 / 2897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1189 : Bounds (73692493 / 500000000) (147384987 / 1000000000) (Real.log (2897 / 2500)) := by
  have h := reflection_log_1189_neg
  have he : Real.log (2897 / 2500) = -Real.log (2500 / 2897) := by
    rw [show ((2897 / 2500) : ℝ) = ((2500 / 2897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1190_neg : (34585167 / 200000000) ≤ -Real.log (2103 / 2500) ∧
    -Real.log (2103 / 2500) ≤ (43231459 / 250000000) := by
  have h := checkLog_sound (w := (397 / 4603)) (n := 12)
    (lo := (34585167 / 200000000)) (hi := (43231459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2103) = 1/(2103 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1190 : Bounds (-43231459 / 250000000) (-34585167 / 200000000) (Real.log (2103 / 2500)) := by
  have h := reflection_log_1190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1191_neg : (158787 / 1000000000) ≤ -Real.log (2500000 / 2500397) ∧
    -Real.log (2500000 / 2500397) ≤ (39697 / 250000000) := by
  have h := checkLog_sound (w := (397 / 5000397)) (n := 12)
    (lo := (158787 / 1000000000)) (hi := (39697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500397 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500397 / 2500000) = 1/(2500000 / 2500397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1191 : Bounds (158787 / 1000000000) (39697 / 250000000) (Real.log (2500397 / 2500000)) := by
  have h := reflection_log_1191_neg
  have he : Real.log (2500397 / 2500000) = -Real.log (2500000 / 2500397) := by
    rw [show ((2500397 / 2500000) : ℝ) = ((2500000 / 2500397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1192_neg : (39703 / 250000000) ≤ -Real.log (2499603 / 2500000) ∧
    -Real.log (2499603 / 2500000) ≤ (158813 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 4999603)) (n := 12)
    (lo := (39703 / 250000000)) (hi := (158813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499603) = 1/(2499603 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1192 : Bounds (-158813 / 1000000000) (-39703 / 250000000) (Real.log (2499603 / 2500000)) := by
  have h := reflection_log_1192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1193_neg : (38311047 / 500000000) ≤ -Real.log (500000 / 539817) ∧
    -Real.log (500000 / 539817) ≤ (15324419 / 200000000) := by
  have h := checkLog_sound (w := (39817 / 1039817)) (n := 12)
    (lo := (38311047 / 500000000)) (hi := (15324419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539817 / 500000) = 1/(500000 / 539817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1193 : Bounds (38311047 / 500000000) (15324419 / 200000000) (Real.log (539817 / 500000)) := by
  have h := reflection_log_1193_neg
  have he : Real.log (539817 / 500000) = -Real.log (500000 / 539817) := by
    rw [show ((539817 / 500000) : ℝ) = ((500000 / 539817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1194_neg : (82983861 / 1000000000) ≤ -Real.log (460183 / 500000) ∧
    -Real.log (460183 / 500000) ≤ (41491931 / 500000000) := by
  have h := checkLog_sound (w := (39817 / 960183)) (n := 12)
    (lo := (82983861 / 1000000000)) (hi := (41491931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460183) = 1/(460183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1194 : Bounds (-41491931 / 500000000) (-82983861 / 1000000000) (Real.log (460183 / 500000)) := by
  have h := reflection_log_1194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1195_neg : (3840783 / 50000000) ≤ -Real.log (1000000 / 1079843) ∧
    -Real.log (1000000 / 1079843) ≤ (76815661 / 1000000000) := by
  have h := checkLog_sound (w := (79843 / 2079843)) (n := 12)
    (lo := (3840783 / 50000000)) (hi := (76815661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079843 / 1000000) = 1/(1000000 / 1079843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1195 : Bounds (3840783 / 50000000) (76815661 / 1000000000) (Real.log (1079843 / 1000000)) := by
  have h := reflection_log_1195_neg
  have he : Real.log (1079843 / 1000000) = -Real.log (1000000 / 1079843) := by
    rw [show ((1079843 / 1000000) : ℝ) = ((1000000 / 1079843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1196_neg : (83210971 / 1000000000) ≤ -Real.log (920157 / 1000000) ∧
    -Real.log (920157 / 1000000) ≤ (20802743 / 250000000) := by
  have h := checkLog_sound (w := (79843 / 1920157)) (n := 12)
    (lo := (83210971 / 1000000000)) (hi := (20802743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920157) = 1/(920157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1196 : Bounds (-20802743 / 250000000) (-83210971 / 1000000000) (Real.log (920157 / 1000000)) := by
  have h := reflection_log_1196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1197_neg : (6395311 / 1000000000) ≤ -Real.log (993625095351 / 1000000000000) ∧
    -Real.log (993625095351 / 1000000000000) ≤ (399707 / 62500000) := by
  have h := checkLog_sound (w := (6374904649 / 1993625095351)) (n := 12)
    (lo := (6395311 / 1000000000)) (hi := (399707 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993625095351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993625095351) = 1/(993625095351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1197 : Bounds (-399707 / 62500000) (-6395311 / 1000000000) (Real.log (993625095351 / 1000000000000)) := by
  have h := reflection_log_1197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1198_neg : (6361767 / 1000000000) ≤ -Real.log (248414606511 / 250000000000) ∧
    -Real.log (248414606511 / 250000000000) ≤ (795221 / 125000000) := by
  have h := checkLog_sound (w := (1585393489 / 498414606511)) (n := 12)
    (lo := (6361767 / 1000000000)) (hi := (795221 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248414606511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248414606511) = 1/(248414606511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1198 : Bounds (-795221 / 125000000) (-6361767 / 1000000000) (Real.log (248414606511 / 250000000000)) := by
  have h := reflection_log_1198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1199_neg : (39901489 / 250000000) ≤ -Real.log (250000000000 / 293262137019) ∧
    -Real.log (250000000000 / 293262137019) ≤ (159605957 / 1000000000) := by
  have h := checkLog_sound (w := (43262137019 / 543262137019)) (n := 12)
    (lo := (39901489 / 250000000)) (hi := (159605957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293262137019 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293262137019 / 250000000000) = 1/(250000000000 / 293262137019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1199 : Bounds (39901489 / 250000000) (159605957 / 1000000000) (Real.log (293262137019 / 250000000000)) := by
  have h := reflection_log_1199_neg
  have he : Real.log (293262137019 / 250000000000) = -Real.log (250000000000 / 293262137019) := by
    rw [show ((293262137019 / 250000000000) : ℝ) = ((250000000000 / 293262137019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1200_neg : (160026631 / 1000000000) ≤ -Real.log (100000000000 / 117354212379) ∧
    -Real.log (100000000000 / 117354212379) ≤ (20003329 / 125000000) := by
  have h := checkLog_sound (w := (17354212379 / 217354212379)) (n := 12)
    (lo := (160026631 / 1000000000)) (hi := (20003329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117354212379 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117354212379 / 100000000000) = 1/(100000000000 / 117354212379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1200 : Bounds (160026631 / 1000000000) (20003329 / 125000000) (Real.log (117354212379 / 100000000000)) := by
  have h := reflection_log_1200_neg
  have he : Real.log (117354212379 / 100000000000) = -Real.log (100000000000 / 117354212379) := by
    rw [show ((117354212379 / 100000000000) : ℝ) = ((100000000000 / 117354212379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1201_neg : (320105651 / 1000000000) ≤ -Real.log (500000000000 / 688636633781) ∧
    -Real.log (500000000000 / 688636633781) ≤ (80026413 / 250000000) := by
  have h := checkLog_sound (w := (188636633781 / 1188636633781)) (n := 12)
    (lo := (320105651 / 1000000000)) (hi := (80026413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688636633781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688636633781 / 500000000000) = 1/(500000000000 / 688636633781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1201 : Bounds (320105651 / 1000000000) (80026413 / 250000000) (Real.log (688636633781 / 500000000000)) := by
  have h := reflection_log_1201_neg
  have he : Real.log (688636633781 / 500000000000) = -Real.log (500000000000 / 688636633781) := by
    rw [show ((688636633781 / 500000000000) : ℝ) = ((500000000000 / 688636633781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1202_neg : (160155411 / 500000000) ≤ -Real.log (250000000000 / 344388968141) ∧
    -Real.log (250000000000 / 344388968141) ≤ (320310823 / 1000000000) := by
  have h := checkLog_sound (w := (94388968141 / 594388968141)) (n := 12)
    (lo := (160155411 / 500000000)) (hi := (320310823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344388968141 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344388968141 / 250000000000) = 1/(250000000000 / 344388968141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1202 : Bounds (160155411 / 500000000) (320310823 / 1000000000) (Real.log (344388968141 / 250000000000)) := by
  have h := reflection_log_1202_neg
  have he : Real.log (344388968141 / 250000000000) = -Real.log (250000000000 / 344388968141) := by
    rw [show ((344388968141 / 250000000000) : ℝ) = ((250000000000 / 344388968141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1203_neg : (147471279 / 1000000000) ≤ -Real.log (10000 / 11589) ∧
    -Real.log (10000 / 11589) ≤ (1843391 / 12500000) := by
  have h := checkLog_sound (w := (1589 / 21589)) (n := 12)
    (lo := (147471279 / 1000000000)) (hi := (1843391 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11589 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11589 / 10000) = 1/(10000 / 11589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1203 : Bounds (147471279 / 1000000000) (1843391 / 12500000) (Real.log (11589 / 10000)) := by
  have h := reflection_log_1203_neg
  have he : Real.log (11589 / 10000) = -Real.log (10000 / 11589) := by
    rw [show ((11589 / 10000) : ℝ) = ((10000 / 11589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1204_neg : (2163059 / 12500000) ≤ -Real.log (8411 / 10000) ∧
    -Real.log (8411 / 10000) ≤ (173044721 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 18411)) (n := 12)
    (lo := (2163059 / 12500000)) (hi := (173044721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8411) = 1/(8411 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1204 : Bounds (-173044721 / 1000000000) (-2163059 / 12500000) (Real.log (8411 / 10000)) := by
  have h := reflection_log_1204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1205_neg : (158887 / 1000000000) ≤ -Real.log (10000000 / 10001589) ∧
    -Real.log (10000000 / 10001589) ≤ (19861 / 125000000) := by
  have h := checkLog_sound (w := (1589 / 20001589)) (n := 12)
    (lo := (158887 / 1000000000)) (hi := (19861 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001589 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001589 / 10000000) = 1/(10000000 / 10001589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1205 : Bounds (158887 / 1000000000) (19861 / 125000000) (Real.log (10001589 / 10000000)) := by
  have h := reflection_log_1205_neg
  have he : Real.log (10001589 / 10000000) = -Real.log (10000000 / 10001589) := by
    rw [show ((10001589 / 10000000) : ℝ) = ((10000000 / 10001589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1206_neg : (2483 / 15625000) ≤ -Real.log (9998411 / 10000000) ∧
    -Real.log (9998411 / 10000000) ≤ (158913 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 19998411)) (n := 12)
    (lo := (2483 / 15625000)) (hi := (158913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998411) = 1/(9998411 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1206 : Bounds (-158913 / 1000000000) (-2483 / 15625000) (Real.log (9998411 / 10000000)) := by
  have h := reflection_log_1206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1207_neg : (15333681 / 200000000) ≤ -Real.log (250000 / 269921) ∧
    -Real.log (250000 / 269921) ≤ (38334203 / 500000000) := by
  have h := checkLog_sound (w := (19921 / 519921)) (n := 12)
    (lo := (15333681 / 200000000)) (hi := (38334203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269921 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269921 / 250000) = 1/(250000 / 269921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1207 : Bounds (15333681 / 200000000) (38334203 / 500000000) (Real.log (269921 / 250000)) := by
  have h := reflection_log_1207_neg
  have he : Real.log (269921 / 250000) = -Real.log (250000 / 269921) := by
    rw [show ((269921 / 250000) : ℝ) = ((250000 / 269921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1208_neg : (83038189 / 1000000000) ≤ -Real.log (230079 / 250000) ∧
    -Real.log (230079 / 250000) ≤ (8303819 / 100000000) := by
  have h := checkLog_sound (w := (19921 / 480079)) (n := 12)
    (lo := (83038189 / 1000000000)) (hi := (8303819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230079) = 1/(230079 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1208 : Bounds (-8303819 / 100000000) (-83038189 / 1000000000) (Real.log (230079 / 250000)) := by
  have h := reflection_log_1208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1209_neg : (9607861 / 125000000) ≤ -Real.log (500000 / 539947) ∧
    -Real.log (500000 / 539947) ≤ (76862889 / 1000000000) := by
  have h := checkLog_sound (w := (39947 / 1039947)) (n := 12)
    (lo := (9607861 / 125000000)) (hi := (76862889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539947 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539947 / 500000) = 1/(500000 / 539947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1209 : Bounds (9607861 / 125000000) (76862889 / 1000000000) (Real.log (539947 / 500000)) := by
  have h := reflection_log_1209_neg
  have he : Real.log (539947 / 500000) = -Real.log (500000 / 539947) := by
    rw [show ((539947 / 500000) : ℝ) = ((500000 / 539947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1210_neg : (41633199 / 500000000) ≤ -Real.log (460053 / 500000) ∧
    -Real.log (460053 / 500000) ≤ (83266399 / 1000000000) := by
  have h := checkLog_sound (w := (39947 / 960053)) (n := 12)
    (lo := (41633199 / 500000000)) (hi := (83266399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460053) = 1/(460053 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1210 : Bounds (-83266399 / 1000000000) (-41633199 / 500000000) (Real.log (460053 / 500000)) := by
  have h := reflection_log_1210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1211_neg : (640351 / 100000000) ≤ -Real.log (248404237191 / 250000000000) ∧
    -Real.log (248404237191 / 250000000000) ≤ (6403511 / 1000000000) := by
  have h := checkLog_sound (w := (1595762809 / 498404237191)) (n := 12)
    (lo := (640351 / 100000000)) (hi := (6403511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248404237191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248404237191) = 1/(248404237191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1211 : Bounds (-6403511 / 1000000000) (-640351 / 100000000) (Real.log (248404237191 / 250000000000)) := by
  have h := reflection_log_1211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1212_neg : (6369783 / 1000000000) ≤ -Real.log (62103153759 / 62500000000) ∧
    -Real.log (62103153759 / 62500000000) ≤ (796223 / 125000000) := by
  have h := checkLog_sound (w := (396846241 / 124603153759)) (n := 12)
    (lo := (6369783 / 1000000000)) (hi := (796223 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62103153759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62103153759) = 1/(62103153759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1212 : Bounds (-796223 / 125000000) (-6369783 / 1000000000) (Real.log (62103153759 / 62500000000)) := by
  have h := reflection_log_1212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1213_neg : (31941319 / 200000000) ≤ -Real.log (100000000000 / 117316660799) ∧
    -Real.log (100000000000 / 117316660799) ≤ (39926649 / 250000000) := by
  have h := checkLog_sound (w := (17316660799 / 217316660799)) (n := 12)
    (lo := (31941319 / 200000000)) (hi := (39926649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117316660799 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117316660799 / 100000000000) = 1/(100000000000 / 117316660799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1213 : Bounds (31941319 / 200000000) (39926649 / 250000000) (Real.log (117316660799 / 100000000000)) := by
  have h := reflection_log_1213_neg
  have he : Real.log (117316660799 / 100000000000) = -Real.log (100000000000 / 117316660799) := by
    rw [show ((117316660799 / 100000000000) : ℝ) = ((100000000000 / 117316660799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1214_neg : (80064643 / 500000000) ≤ -Real.log (15625000000 / 18338478121) ∧
    -Real.log (15625000000 / 18338478121) ≤ (160129287 / 1000000000) := by
  have h := checkLog_sound (w := (2713478121 / 33963478121)) (n := 12)
    (lo := (80064643 / 500000000)) (hi := (160129287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18338478121 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18338478121 / 15625000000) = 1/(15625000000 / 18338478121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1214 : Bounds (80064643 / 500000000) (160129287 / 1000000000) (Real.log (18338478121 / 15625000000)) := by
  have h := reflection_log_1214_neg
  have he : Real.log (18338478121 / 15625000000) = -Real.log (15625000000 / 18338478121) := by
    rw [show ((18338478121 / 15625000000) : ℝ) = ((15625000000 / 18338478121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1215_neg : (160155411 / 500000000) ≤ -Real.log (500000000000 / 688777936281) ∧
    -Real.log (500000000000 / 688777936281) ≤ (320310823 / 1000000000) := by
  have h := checkLog_sound (w := (188777936281 / 1188777936281)) (n := 12)
    (lo := (160155411 / 500000000)) (hi := (320310823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688777936281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688777936281 / 500000000000) = 1/(500000000000 / 688777936281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1215 : Bounds (160155411 / 500000000) (320310823 / 1000000000) (Real.log (688777936281 / 500000000000)) := by
  have h := reflection_log_1215_neg
  have he : Real.log (688777936281 / 500000000000) = -Real.log (500000000000 / 688777936281) := by
    rw [show ((688777936281 / 500000000000) : ℝ) = ((500000000000 / 688777936281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0019 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1216_neg : (320515999 / 1000000000) ≤ -Real.log (250000000000 / 344459636191) ∧
    -Real.log (250000000000 / 344459636191) ≤ (80129 / 250000) := by
  have h := checkLog_sound (w := (94459636191 / 594459636191)) (n := 12)
    (lo := (320515999 / 1000000000)) (hi := (80129 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344459636191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344459636191 / 250000000000) = 1/(250000000000 / 344459636191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1216 : Bounds (320515999 / 1000000000) (80129 / 250000) (Real.log (344459636191 / 250000000000)) := by
  have h := reflection_log_1216_neg
  have he : Real.log (344459636191 / 250000000000) = -Real.log (250000000000 / 344459636191) := by
    rw [show ((344459636191 / 250000000000) : ℝ) = ((250000000000 / 344459636191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1217_neg : (36889391 / 250000000) ≤ -Real.log (1000 / 1159) ∧
    -Real.log (1000 / 1159) ≤ (29511513 / 200000000) := by
  have h := checkLog_sound (w := (159 / 2159)) (n := 12)
    (lo := (36889391 / 250000000)) (hi := (29511513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159 / 1000) = 1/(1000 / 1159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1217 : Bounds (36889391 / 250000000) (29511513 / 200000000) (Real.log (1159 / 1000)) := by
  have h := reflection_log_1217_neg
  have he : Real.log (1159 / 1000) = -Real.log (1000 / 1159) := by
    rw [show ((1159 / 1000) : ℝ) = ((1000 / 1159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1218_neg : (173163619 / 1000000000) ≤ -Real.log (841 / 1000) ∧
    -Real.log (841 / 1000) ≤ (8658181 / 50000000) := by
  have h := checkLog_sound (w := (159 / 1841)) (n := 12)
    (lo := (173163619 / 1000000000)) (hi := (8658181 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 841) = 1/(841 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1218 : Bounds (-8658181 / 50000000) (-173163619 / 1000000000) (Real.log (841 / 1000)) := by
  have h := reflection_log_1218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1219_neg : (158987 / 1000000000) ≤ -Real.log (1000000 / 1000159) ∧
    -Real.log (1000000 / 1000159) ≤ (39747 / 250000000) := by
  have h := checkLog_sound (w := (159 / 2000159)) (n := 12)
    (lo := (158987 / 1000000000)) (hi := (39747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000159 / 1000000) = 1/(1000000 / 1000159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1219 : Bounds (158987 / 1000000000) (39747 / 250000000) (Real.log (1000159 / 1000000)) := by
  have h := reflection_log_1219_neg
  have he : Real.log (1000159 / 1000000) = -Real.log (1000000 / 1000159) := by
    rw [show ((1000159 / 1000000) : ℝ) = ((1000000 / 1000159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1220_neg : (39753 / 250000000) ≤ -Real.log (999841 / 1000000) ∧
    -Real.log (999841 / 1000000) ≤ (159013 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1999841)) (n := 12)
    (lo := (39753 / 250000000)) (hi := (159013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999841) = 1/(999841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1220 : Bounds (-159013 / 1000000000) (-39753 / 250000000) (Real.log (999841 / 1000000)) := by
  have h := reflection_log_1220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1221_neg : (1917891 / 25000000) ≤ -Real.log (200000 / 215947) ∧
    -Real.log (200000 / 215947) ≤ (76715641 / 1000000000) := by
  have h := checkLog_sound (w := (15947 / 415947)) (n := 12)
    (lo := (1917891 / 25000000)) (hi := (76715641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215947 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215947 / 200000) = 1/(200000 / 215947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1221 : Bounds (1917891 / 25000000) (76715641 / 1000000000) (Real.log (215947 / 200000)) := by
  have h := reflection_log_1221_neg
  have he : Real.log (215947 / 200000) = -Real.log (200000 / 215947) := by
    rw [show ((215947 / 200000) : ℝ) = ((200000 / 215947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1222_neg : (41546803 / 500000000) ≤ -Real.log (184053 / 200000) ∧
    -Real.log (184053 / 200000) ≤ (83093607 / 1000000000) := by
  have h := checkLog_sound (w := (15947 / 384053)) (n := 12)
    (lo := (41546803 / 500000000)) (hi := (83093607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184053) = 1/(184053 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1222 : Bounds (-83093607 / 1000000000) (-41546803 / 500000000) (Real.log (184053 / 200000)) := by
  have h := reflection_log_1222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1223_neg : (76910113 / 1000000000) ≤ -Real.log (200000 / 215989) ∧
    -Real.log (200000 / 215989) ≤ (38455057 / 500000000) := by
  have h := checkLog_sound (w := (15989 / 415989)) (n := 12)
    (lo := (76910113 / 1000000000)) (hi := (38455057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215989 / 200000) = 1/(200000 / 215989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1223 : Bounds (76910113 / 1000000000) (38455057 / 500000000) (Real.log (215989 / 200000)) := by
  have h := reflection_log_1223_neg
  have he : Real.log (215989 / 200000) = -Real.log (200000 / 215989) := by
    rw [show ((215989 / 200000) : ℝ) = ((200000 / 215989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1224_neg : (20830457 / 250000000) ≤ -Real.log (184011 / 200000) ∧
    -Real.log (184011 / 200000) ≤ (83321829 / 1000000000) := by
  have h := checkLog_sound (w := (15989 / 384011)) (n := 12)
    (lo := (20830457 / 250000000)) (hi := (83321829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184011) = 1/(184011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1224 : Bounds (-83321829 / 1000000000) (-20830457 / 250000000) (Real.log (184011 / 200000)) := by
  have h := reflection_log_1224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1225_neg : (3205857 / 500000000) ≤ -Real.log (39744351879 / 40000000000) ∧
    -Real.log (39744351879 / 40000000000) ≤ (1282343 / 200000000) := by
  have h := checkLog_sound (w := (255648121 / 79744351879)) (n := 12)
    (lo := (3205857 / 500000000)) (hi := (1282343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39744351879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39744351879) = 1/(39744351879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1225 : Bounds (-1282343 / 200000000) (-3205857 / 500000000) (Real.log (39744351879 / 40000000000)) := by
  have h := reflection_log_1225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1226_neg : (3188983 / 500000000) ≤ -Real.log (39745693191 / 40000000000) ∧
    -Real.log (39745693191 / 40000000000) ≤ (6377967 / 1000000000) := by
  have h := checkLog_sound (w := (254306809 / 79745693191)) (n := 12)
    (lo := (3188983 / 500000000)) (hi := (6377967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39745693191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39745693191) = 1/(39745693191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1226 : Bounds (-6377967 / 1000000000) (-3188983 / 500000000) (Real.log (39745693191 / 40000000000)) := by
  have h := reflection_log_1226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1227_neg : (159809247 / 1000000000) ≤ -Real.log (500000000000 / 586643521159) ∧
    -Real.log (500000000000 / 586643521159) ≤ (4994039 / 31250000) := by
  have h := checkLog_sound (w := (86643521159 / 1086643521159)) (n := 12)
    (lo := (159809247 / 1000000000)) (hi := (4994039 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586643521159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586643521159 / 500000000000) = 1/(500000000000 / 586643521159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1227 : Bounds (159809247 / 1000000000) (4994039 / 31250000) (Real.log (586643521159 / 500000000000)) := by
  have h := reflection_log_1227_neg
  have he : Real.log (586643521159 / 500000000000) = -Real.log (500000000000 / 586643521159) := by
    rw [show ((586643521159 / 500000000000) : ℝ) = ((500000000000 / 586643521159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1228_neg : (80115971 / 500000000) ≤ -Real.log (31250000000 / 36680721533) ∧
    -Real.log (31250000000 / 36680721533) ≤ (160231943 / 1000000000) := by
  have h := checkLog_sound (w := (5430721533 / 67930721533)) (n := 12)
    (lo := (80115971 / 500000000)) (hi := (160231943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36680721533 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36680721533 / 31250000000) = 1/(31250000000 / 36680721533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1228 : Bounds (80115971 / 500000000) (160231943 / 1000000000) (Real.log (36680721533 / 31250000000)) := by
  have h := reflection_log_1228_neg
  have he : Real.log (36680721533 / 31250000000) = -Real.log (31250000000 / 36680721533) := by
    rw [show ((36680721533 / 31250000000) : ℝ) = ((31250000000 / 36680721533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1229_neg : (320515999 / 1000000000) ≤ -Real.log (500000000000 / 688919272381) ∧
    -Real.log (500000000000 / 688919272381) ≤ (80129 / 250000) := by
  have h := checkLog_sound (w := (188919272381 / 1188919272381)) (n := 12)
    (lo := (320515999 / 1000000000)) (hi := (80129 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688919272381 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688919272381 / 500000000000) = 1/(500000000000 / 688919272381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1229 : Bounds (320515999 / 1000000000) (80129 / 250000) (Real.log (688919272381 / 500000000000)) := by
  have h := reflection_log_1229_neg
  have he : Real.log (688919272381 / 500000000000) = -Real.log (500000000000 / 688919272381) := by
    rw [show ((688919272381 / 500000000000) : ℝ) = ((500000000000 / 688919272381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1230_neg : (320721183 / 1000000000) ≤ -Real.log (500000000000 / 689060642093) ∧
    -Real.log (500000000000 / 689060642093) ≤ (10022537 / 31250000) := by
  have h := checkLog_sound (w := (189060642093 / 1189060642093)) (n := 12)
    (lo := (320721183 / 1000000000)) (hi := (10022537 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689060642093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689060642093 / 500000000000) = 1/(500000000000 / 689060642093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1230 : Bounds (320721183 / 1000000000) (10022537 / 31250000) (Real.log (689060642093 / 500000000000)) := by
  have h := reflection_log_1230_neg
  have he : Real.log (689060642093 / 500000000000) = -Real.log (500000000000 / 689060642093) := by
    rw [show ((689060642093 / 500000000000) : ℝ) = ((500000000000 / 689060642093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1231_neg : (147643841 / 1000000000) ≤ -Real.log (10000 / 11591) ∧
    -Real.log (10000 / 11591) ≤ (73821921 / 500000000) := by
  have h := checkLog_sound (w := (1591 / 21591)) (n := 12)
    (lo := (147643841 / 1000000000)) (hi := (73821921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11591 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11591 / 10000) = 1/(10000 / 11591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1231 : Bounds (147643841 / 1000000000) (73821921 / 500000000) (Real.log (11591 / 10000)) := by
  have h := reflection_log_1231_neg
  have he : Real.log (11591 / 10000) = -Real.log (10000 / 11591) := by
    rw [show ((11591 / 10000) : ℝ) = ((10000 / 11591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1232_neg : (43320633 / 250000000) ≤ -Real.log (8409 / 10000) ∧
    -Real.log (8409 / 10000) ≤ (173282533 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 18409)) (n := 12)
    (lo := (43320633 / 250000000)) (hi := (173282533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8409) = 1/(8409 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1232 : Bounds (-173282533 / 1000000000) (-43320633 / 250000000) (Real.log (8409 / 10000)) := by
  have h := reflection_log_1232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1233_neg : (159087 / 1000000000) ≤ -Real.log (10000000 / 10001591) ∧
    -Real.log (10000000 / 10001591) ≤ (9943 / 62500000) := by
  have h := checkLog_sound (w := (1591 / 20001591)) (n := 12)
    (lo := (159087 / 1000000000)) (hi := (9943 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001591 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001591 / 10000000) = 1/(10000000 / 10001591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1233 : Bounds (159087 / 1000000000) (9943 / 62500000) (Real.log (10001591 / 10000000)) := by
  have h := reflection_log_1233_neg
  have he : Real.log (10001591 / 10000000) = -Real.log (10000000 / 10001591) := by
    rw [show ((10001591 / 10000000) : ℝ) = ((10000000 / 10001591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1234_neg : (19889 / 125000000) ≤ -Real.log (9998409 / 10000000) ∧
    -Real.log (9998409 / 10000000) ≤ (159113 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 19998409)) (n := 12)
    (lo := (19889 / 125000000)) (hi := (159113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998409) = 1/(9998409 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1234 : Bounds (-159113 / 1000000000) (-19889 / 125000000) (Real.log (9998409 / 10000000)) := by
  have h := reflection_log_1234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1235_neg : (76762873 / 1000000000) ≤ -Real.log (500000 / 539893) ∧
    -Real.log (500000 / 539893) ≤ (38381437 / 500000000) := by
  have h := checkLog_sound (w := (39893 / 1039893)) (n := 12)
    (lo := (76762873 / 1000000000)) (hi := (38381437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539893 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539893 / 500000) = 1/(500000 / 539893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1235 : Bounds (76762873 / 1000000000) (38381437 / 500000000) (Real.log (539893 / 500000)) := by
  have h := reflection_log_1235_neg
  have he : Real.log (539893 / 500000) = -Real.log (500000 / 539893) := by
    rw [show ((539893 / 500000) : ℝ) = ((500000 / 539893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1236_neg : (83149027 / 1000000000) ≤ -Real.log (460107 / 500000) ∧
    -Real.log (460107 / 500000) ≤ (20787257 / 250000000) := by
  have h := checkLog_sound (w := (39893 / 960107)) (n := 12)
    (lo := (83149027 / 1000000000)) (hi := (20787257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460107) = 1/(460107 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1236 : Bounds (-20787257 / 250000000) (-83149027 / 1000000000) (Real.log (460107 / 500000)) := by
  have h := reflection_log_1236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1237_neg : (76957337 / 1000000000) ≤ -Real.log (250000 / 269999) ∧
    -Real.log (250000 / 269999) ≤ (38478669 / 500000000) := by
  have h := checkLog_sound (w := (19999 / 519999)) (n := 12)
    (lo := (76957337 / 1000000000)) (hi := (38478669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269999 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269999 / 250000) = 1/(250000 / 269999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1237 : Bounds (76957337 / 1000000000) (38478669 / 500000000) (Real.log (269999 / 250000)) := by
  have h := reflection_log_1237_neg
  have he : Real.log (269999 / 250000) = -Real.log (250000 / 269999) := by
    rw [show ((269999 / 250000) : ℝ) = ((250000 / 269999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1238_neg : (83377261 / 1000000000) ≤ -Real.log (230001 / 250000) ∧
    -Real.log (230001 / 250000) ≤ (41688631 / 500000000) := by
  have h := checkLog_sound (w := (19999 / 480001)) (n := 12)
    (lo := (83377261 / 1000000000)) (hi := (41688631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230001) = 1/(230001 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1238 : Bounds (-41688631 / 500000000) (-83377261 / 1000000000) (Real.log (230001 / 250000)) := by
  have h := reflection_log_1238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1239_neg : (6419923 / 1000000000) ≤ -Real.log (62100039999 / 62500000000) ∧
    -Real.log (62100039999 / 62500000000) ≤ (1604981 / 250000000) := by
  have h := checkLog_sound (w := (399960001 / 124600039999)) (n := 12)
    (lo := (6419923 / 1000000000)) (hi := (1604981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62100039999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62100039999) = 1/(62100039999 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1239 : Bounds (-1604981 / 250000000) (-6419923 / 1000000000) (Real.log (62100039999 / 62500000000)) := by
  have h := reflection_log_1239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1240_neg : (6386153 / 1000000000) ≤ -Real.log (248408548551 / 250000000000) ∧
    -Real.log (248408548551 / 250000000000) ≤ (3193077 / 500000000) := by
  have h := checkLog_sound (w := (1591451449 / 498408548551)) (n := 12)
    (lo := (6386153 / 1000000000)) (hi := (3193077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248408548551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248408548551) = 1/(248408548551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1240 : Bounds (-3193077 / 500000000) (-6386153 / 1000000000) (Real.log (248408548551 / 250000000000)) := by
  have h := reflection_log_1240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1241_neg : (1599119 / 10000000) ≤ -Real.log (250000000000 / 293351872499) ∧
    -Real.log (250000000000 / 293351872499) ≤ (159911901 / 1000000000) := by
  have h := checkLog_sound (w := (43351872499 / 543351872499)) (n := 12)
    (lo := (1599119 / 10000000)) (hi := (159911901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293351872499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293351872499 / 250000000000) = 1/(250000000000 / 293351872499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1241 : Bounds (1599119 / 10000000) (159911901 / 1000000000) (Real.log (293351872499 / 250000000000)) := by
  have h := reflection_log_1241_neg
  have he : Real.log (293351872499 / 250000000000) = -Real.log (250000000000 / 293351872499) := by
    rw [show ((293351872499 / 250000000000) : ℝ) = ((250000000000 / 293351872499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1242_neg : (80167299 / 500000000) ≤ -Real.log (250000000000 / 293475897931) ∧
    -Real.log (250000000000 / 293475897931) ≤ (160334599 / 1000000000) := by
  have h := checkLog_sound (w := (43475897931 / 543475897931)) (n := 12)
    (lo := (80167299 / 500000000)) (hi := (160334599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293475897931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293475897931 / 250000000000) = 1/(250000000000 / 293475897931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1242 : Bounds (80167299 / 500000000) (160334599 / 1000000000) (Real.log (293475897931 / 250000000000)) := by
  have h := reflection_log_1242_neg
  have he : Real.log (293475897931 / 250000000000) = -Real.log (250000000000 / 293475897931) := by
    rw [show ((293475897931 / 250000000000) : ℝ) = ((250000000000 / 293475897931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1243_neg : (320721183 / 1000000000) ≤ -Real.log (125000000000 / 172265160523) ∧
    -Real.log (125000000000 / 172265160523) ≤ (10022537 / 31250000) := by
  have h := checkLog_sound (w := (47265160523 / 297265160523)) (n := 12)
    (lo := (320721183 / 1000000000)) (hi := (10022537 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172265160523 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172265160523 / 125000000000) = 1/(125000000000 / 172265160523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1243 : Bounds (320721183 / 1000000000) (10022537 / 31250000) (Real.log (172265160523 / 125000000000)) := by
  have h := reflection_log_1243_neg
  have he : Real.log (172265160523 / 125000000000) = -Real.log (125000000000 / 172265160523) := by
    rw [show ((172265160523 / 125000000000) : ℝ) = ((125000000000 / 172265160523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1244_neg : (160463187 / 500000000) ≤ -Real.log (125000000000 / 172300511357) ∧
    -Real.log (125000000000 / 172300511357) ≤ (2567411 / 8000000) := by
  have h := checkLog_sound (w := (47300511357 / 297300511357)) (n := 12)
    (lo := (160463187 / 500000000)) (hi := (2567411 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172300511357 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172300511357 / 125000000000) = 1/(125000000000 / 172300511357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1244 : Bounds (160463187 / 500000000) (2567411 / 8000000) (Real.log (172300511357 / 125000000000)) := by
  have h := reflection_log_1244_neg
  have he : Real.log (172300511357 / 125000000000) = -Real.log (125000000000 / 172300511357) := by
    rw [show ((172300511357 / 125000000000) : ℝ) = ((125000000000 / 172300511357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1245_neg : (2308283 / 15625000) ≤ -Real.log (1250 / 1449) ∧
    -Real.log (1250 / 1449) ≤ (147730113 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2699)) (n := 12)
    (lo := (2308283 / 15625000)) (hi := (147730113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449 / 1250) = 1/(1250 / 1449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1245 : Bounds (2308283 / 15625000) (147730113 / 1000000000) (Real.log (1449 / 1250)) := by
  have h := reflection_log_1245_neg
  have he : Real.log (1449 / 1250) = -Real.log (1250 / 1449) := by
    rw [show ((1449 / 1250) : ℝ) = ((1250 / 1449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1246_neg : (173401459 / 1000000000) ≤ -Real.log (1051 / 1250) ∧
    -Real.log (1051 / 1250) ≤ (8670073 / 50000000) := by
  have h := checkLog_sound (w := (199 / 2301)) (n := 12)
    (lo := (173401459 / 1000000000)) (hi := (8670073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1051) = 1/(1051 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1246 : Bounds (-8670073 / 50000000) (-173401459 / 1000000000) (Real.log (1051 / 1250)) := by
  have h := reflection_log_1246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1247_neg : (159187 / 1000000000) ≤ -Real.log (1250000 / 1250199) ∧
    -Real.log (1250000 / 1250199) ≤ (39797 / 250000000) := by
  have h := checkLog_sound (w := (199 / 2500199)) (n := 12)
    (lo := (159187 / 1000000000)) (hi := (39797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250199 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250199 / 1250000) = 1/(1250000 / 1250199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1247 : Bounds (159187 / 1000000000) (39797 / 250000000) (Real.log (1250199 / 1250000)) := by
  have h := reflection_log_1247_neg
  have he : Real.log (1250199 / 1250000) = -Real.log (1250000 / 1250199) := by
    rw [show ((1250199 / 1250000) : ℝ) = ((1250000 / 1250199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1248_neg : (39803 / 250000000) ≤ -Real.log (1249801 / 1250000) ∧
    -Real.log (1249801 / 1250000) ≤ (159213 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2499801)) (n := 12)
    (lo := (39803 / 250000000)) (hi := (159213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249801) = 1/(1249801 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1248 : Bounds (-159213 / 1000000000) (-39803 / 250000000) (Real.log (1249801 / 1250000)) := by
  have h := reflection_log_1248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1249_neg : (76809177 / 1000000000) ≤ -Real.log (250000 / 269959) ∧
    -Real.log (250000 / 269959) ≤ (38404589 / 500000000) := by
  have h := checkLog_sound (w := (19959 / 519959)) (n := 12)
    (lo := (76809177 / 1000000000)) (hi := (38404589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269959 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269959 / 250000) = 1/(250000 / 269959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1249 : Bounds (76809177 / 1000000000) (38404589 / 500000000) (Real.log (269959 / 250000)) := by
  have h := reflection_log_1249_neg
  have he : Real.log (269959 / 250000) = -Real.log (250000 / 269959) := by
    rw [show ((269959 / 250000) : ℝ) = ((250000 / 269959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1250_neg : (83203363 / 1000000000) ≤ -Real.log (230041 / 250000) ∧
    -Real.log (230041 / 250000) ≤ (20800841 / 250000000) := by
  have h := checkLog_sound (w := (19959 / 480041)) (n := 12)
    (lo := (83203363 / 1000000000)) (hi := (20800841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230041) = 1/(230041 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1250 : Bounds (-20800841 / 250000000) (-83203363 / 1000000000) (Real.log (230041 / 250000)) := by
  have h := reflection_log_1250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1251_neg : (4812727 / 62500000) ≤ -Real.log (500000 / 540023) ∧
    -Real.log (500000 / 540023) ≤ (77003633 / 1000000000) := by
  have h := checkLog_sound (w := (40023 / 1040023)) (n := 12)
    (lo := (4812727 / 62500000)) (hi := (77003633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540023 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540023 / 500000) = 1/(500000 / 540023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1251 : Bounds (4812727 / 62500000) (77003633 / 1000000000) (Real.log (540023 / 500000)) := by
  have h := reflection_log_1251_neg
  have he : Real.log (540023 / 500000) = -Real.log (500000 / 540023) := by
    rw [show ((540023 / 500000) : ℝ) = ((500000 / 540023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1252_neg : (8343161 / 100000000) ≤ -Real.log (459977 / 500000) ∧
    -Real.log (459977 / 500000) ≤ (83431611 / 1000000000) := by
  have h := checkLog_sound (w := (40023 / 959977)) (n := 12)
    (lo := (8343161 / 100000000)) (hi := (83431611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459977) = 1/(459977 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1252 : Bounds (-83431611 / 1000000000) (-8343161 / 100000000) (Real.log (459977 / 500000)) := by
  have h := reflection_log_1252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1253_neg : (6427977 / 1000000000) ≤ -Real.log (248398159471 / 250000000000) ∧
    -Real.log (248398159471 / 250000000000) ≤ (3213989 / 500000000) := by
  have h := checkLog_sound (w := (1601840529 / 498398159471)) (n := 12)
    (lo := (6427977 / 1000000000)) (hi := (3213989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248398159471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248398159471) = 1/(248398159471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1253 : Bounds (-3213989 / 500000000) (-6427977 / 1000000000) (Real.log (248398159471 / 250000000000)) := by
  have h := reflection_log_1253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1254_neg : (3197093 / 500000000) ≤ -Real.log (62101638319 / 62500000000) ∧
    -Real.log (62101638319 / 62500000000) ≤ (6394187 / 1000000000) := by
  have h := checkLog_sound (w := (398361681 / 124601638319)) (n := 12)
    (lo := (3197093 / 500000000)) (hi := (6394187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62101638319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62101638319) = 1/(62101638319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1254 : Bounds (-6394187 / 1000000000) (-3197093 / 500000000) (Real.log (62101638319 / 62500000000)) := by
  have h := reflection_log_1254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1255_neg : (160012541 / 1000000000) ≤ -Real.log (250000000000 / 293381397229) ∧
    -Real.log (250000000000 / 293381397229) ≤ (80006271 / 500000000) := by
  have h := checkLog_sound (w := (43381397229 / 543381397229)) (n := 12)
    (lo := (160012541 / 1000000000)) (hi := (80006271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293381397229 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293381397229 / 250000000000) = 1/(250000000000 / 293381397229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1255 : Bounds (160012541 / 1000000000) (80006271 / 500000000) (Real.log (293381397229 / 250000000000)) := by
  have h := reflection_log_1255_neg
  have he : Real.log (293381397229 / 250000000000) = -Real.log (250000000000 / 293381397229) := by
    rw [show ((293381397229 / 250000000000) : ℝ) = ((250000000000 / 293381397229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1256_neg : (160435243 / 1000000000) ≤ -Real.log (500000000000 / 587010872283) ∧
    -Real.log (500000000000 / 587010872283) ≤ (40108811 / 250000000) := by
  have h := checkLog_sound (w := (87010872283 / 1087010872283)) (n := 12)
    (lo := (160435243 / 1000000000)) (hi := (40108811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587010872283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587010872283 / 500000000000) = 1/(500000000000 / 587010872283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1256 : Bounds (160435243 / 1000000000) (40108811 / 250000000) (Real.log (587010872283 / 500000000000)) := by
  have h := reflection_log_1256_neg
  have he : Real.log (587010872283 / 500000000000) = -Real.log (500000000000 / 587010872283) := by
    rw [show ((587010872283 / 500000000000) : ℝ) = ((500000000000 / 587010872283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1257_neg : (160463187 / 500000000) ≤ -Real.log (500000000000 / 689202045427) ∧
    -Real.log (500000000000 / 689202045427) ≤ (2567411 / 8000000) := by
  have h := checkLog_sound (w := (189202045427 / 1189202045427)) (n := 12)
    (lo := (160463187 / 500000000)) (hi := (2567411 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689202045427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689202045427 / 500000000000) = 1/(500000000000 / 689202045427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1257 : Bounds (160463187 / 500000000) (2567411 / 8000000) (Real.log (689202045427 / 500000000000)) := by
  have h := reflection_log_1257_neg
  have he : Real.log (689202045427 / 500000000000) = -Real.log (500000000000 / 689202045427) := by
    rw [show ((689202045427 / 500000000000) : ℝ) = ((500000000000 / 689202045427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1258_neg : (321131571 / 1000000000) ≤ -Real.log (250000000000 / 344671741199) ∧
    -Real.log (250000000000 / 344671741199) ≤ (80282893 / 250000000) := by
  have h := checkLog_sound (w := (94671741199 / 594671741199)) (n := 12)
    (lo := (321131571 / 1000000000)) (hi := (80282893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344671741199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344671741199 / 250000000000) = 1/(250000000000 / 344671741199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1258 : Bounds (321131571 / 1000000000) (80282893 / 250000000) (Real.log (344671741199 / 250000000000)) := by
  have h := reflection_log_1258_neg
  have he : Real.log (344671741199 / 250000000000) = -Real.log (250000000000 / 344671741199) := by
    rw [show ((344671741199 / 250000000000) : ℝ) = ((250000000000 / 344671741199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1259_neg : (73908187 / 500000000) ≤ -Real.log (10000 / 11593) ∧
    -Real.log (10000 / 11593) ≤ (1182531 / 8000000) := by
  have h := checkLog_sound (w := (1593 / 21593)) (n := 12)
    (lo := (73908187 / 500000000)) (hi := (1182531 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11593 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11593 / 10000) = 1/(10000 / 11593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1259 : Bounds (73908187 / 500000000) (1182531 / 8000000) (Real.log (11593 / 10000)) := by
  have h := reflection_log_1259_neg
  have he : Real.log (11593 / 10000) = -Real.log (10000 / 11593) := by
    rw [show ((11593 / 10000) : ℝ) = ((10000 / 11593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1260_neg : (433801 / 2500000) ≤ -Real.log (8407 / 10000) ∧
    -Real.log (8407 / 10000) ≤ (173520401 / 1000000000) := by
  have h := checkLog_sound (w := (1593 / 18407)) (n := 12)
    (lo := (433801 / 2500000)) (hi := (173520401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8407) = 1/(8407 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1260 : Bounds (-173520401 / 1000000000) (-433801 / 2500000) (Real.log (8407 / 10000)) := by
  have h := reflection_log_1260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1261_neg : (159287 / 1000000000) ≤ -Real.log (10000000 / 10001593) ∧
    -Real.log (10000000 / 10001593) ≤ (19911 / 125000000) := by
  have h := checkLog_sound (w := (1593 / 20001593)) (n := 12)
    (lo := (159287 / 1000000000)) (hi := (19911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001593 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001593 / 10000000) = 1/(10000000 / 10001593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1261 : Bounds (159287 / 1000000000) (19911 / 125000000) (Real.log (10001593 / 10000000)) := by
  have h := reflection_log_1261_neg
  have he : Real.log (10001593 / 10000000) = -Real.log (10000000 / 10001593) := by
    rw [show ((10001593 / 10000000) : ℝ) = ((10000000 / 10001593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1262_neg : (9957 / 62500000) ≤ -Real.log (9998407 / 10000000) ∧
    -Real.log (9998407 / 10000000) ≤ (159313 / 1000000000) := by
  have h := checkLog_sound (w := (1593 / 19998407)) (n := 12)
    (lo := (9957 / 62500000)) (hi := (159313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998407) = 1/(9998407 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1262 : Bounds (-159313 / 1000000000) (-9957 / 62500000) (Real.log (9998407 / 10000000)) := by
  have h := reflection_log_1262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1263_neg : (38428203 / 500000000) ≤ -Real.log (1000000 / 1079887) ∧
    -Real.log (1000000 / 1079887) ≤ (76856407 / 1000000000) := by
  have h := checkLog_sound (w := (79887 / 2079887)) (n := 12)
    (lo := (38428203 / 500000000)) (hi := (76856407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079887 / 1000000) = 1/(1000000 / 1079887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1263 : Bounds (38428203 / 500000000) (76856407 / 1000000000) (Real.log (1079887 / 1000000)) := by
  have h := reflection_log_1263_neg
  have he : Real.log (1079887 / 1000000) = -Real.log (1000000 / 1079887) := by
    rw [show ((1079887 / 1000000) : ℝ) = ((1000000 / 1079887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1264_neg : (8325879 / 100000000) ≤ -Real.log (920113 / 1000000) ∧
    -Real.log (920113 / 1000000) ≤ (83258791 / 1000000000) := by
  have h := checkLog_sound (w := (79887 / 1920113)) (n := 12)
    (lo := (8325879 / 100000000)) (hi := (83258791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920113) = 1/(920113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1264 : Bounds (-83258791 / 1000000000) (-8325879 / 100000000) (Real.log (920113 / 1000000)) := by
  have h := reflection_log_1264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1265_neg : (77050851 / 1000000000) ≤ -Real.log (1000000 / 1080097) ∧
    -Real.log (1000000 / 1080097) ≤ (19262713 / 250000000) := by
  have h := checkLog_sound (w := (80097 / 2080097)) (n := 12)
    (lo := (77050851 / 1000000000)) (hi := (19262713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080097 / 1000000) = 1/(1000000 / 1080097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1265 : Bounds (77050851 / 1000000000) (19262713 / 250000000) (Real.log (1080097 / 1000000)) := by
  have h := reflection_log_1265_neg
  have he : Real.log (1080097 / 1000000) = -Real.log (1000000 / 1080097) := by
    rw [show ((1080097 / 1000000) : ℝ) = ((1000000 / 1080097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1266_neg : (83487049 / 1000000000) ≤ -Real.log (919903 / 1000000) ∧
    -Real.log (919903 / 1000000) ≤ (1669741 / 20000000) := by
  have h := checkLog_sound (w := (80097 / 1919903)) (n := 12)
    (lo := (83487049 / 1000000000)) (hi := (1669741 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919903) = 1/(919903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1266 : Bounds (-1669741 / 20000000) (-83487049 / 1000000000) (Real.log (919903 / 1000000)) := by
  have h := reflection_log_1266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1267_neg : (6436197 / 1000000000) ≤ -Real.log (993584470591 / 1000000000000) ∧
    -Real.log (993584470591 / 1000000000000) ≤ (3218099 / 500000000) := by
  have h := checkLog_sound (w := (6415529409 / 1993584470591)) (n := 12)
    (lo := (6436197 / 1000000000)) (hi := (3218099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993584470591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993584470591) = 1/(993584470591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1267 : Bounds (-3218099 / 500000000) (-6436197 / 1000000000) (Real.log (993584470591 / 1000000000000)) := by
  have h := reflection_log_1267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1268_neg : (400149 / 62500000) ≤ -Real.log (993618067231 / 1000000000000) ∧
    -Real.log (993618067231 / 1000000000000) ≤ (1280477 / 200000000) := by
  have h := checkLog_sound (w := (6381932769 / 1993618067231)) (n := 12)
    (lo := (400149 / 62500000)) (hi := (1280477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993618067231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993618067231) = 1/(993618067231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1268 : Bounds (-1280477 / 200000000) (-400149 / 62500000) (Real.log (993618067231 / 1000000000000)) := by
  have h := reflection_log_1268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1269_neg : (40028799 / 250000000) ≤ -Real.log (250000000000 / 293411515759) ∧
    -Real.log (250000000000 / 293411515759) ≤ (160115197 / 1000000000) := by
  have h := checkLog_sound (w := (43411515759 / 543411515759)) (n := 12)
    (lo := (40028799 / 250000000)) (hi := (160115197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293411515759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293411515759 / 250000000000) = 1/(250000000000 / 293411515759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1269 : Bounds (40028799 / 250000000) (160115197 / 1000000000) (Real.log (293411515759 / 250000000000)) := by
  have h := reflection_log_1269_neg
  have he : Real.log (293411515759 / 250000000000) = -Real.log (250000000000 / 293411515759) := by
    rw [show ((293411515759 / 250000000000) : ℝ) = ((250000000000 / 293411515759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1270_neg : (160537901 / 1000000000) ≤ -Real.log (500000000000 / 587071136849) ∧
    -Real.log (500000000000 / 587071136849) ≤ (80268951 / 500000000) := by
  have h := checkLog_sound (w := (87071136849 / 1087071136849)) (n := 12)
    (lo := (160537901 / 1000000000)) (hi := (80268951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587071136849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587071136849 / 500000000000) = 1/(500000000000 / 587071136849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1270 : Bounds (160537901 / 1000000000) (80268951 / 500000000) (Real.log (587071136849 / 500000000000)) := by
  have h := reflection_log_1270_neg
  have he : Real.log (587071136849 / 500000000000) = -Real.log (500000000000 / 587071136849) := by
    rw [show ((587071136849 / 500000000000) : ℝ) = ((500000000000 / 587071136849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1271_neg : (321131571 / 1000000000) ≤ -Real.log (500000000000 / 689343482397) ∧
    -Real.log (500000000000 / 689343482397) ≤ (80282893 / 250000000) := by
  have h := checkLog_sound (w := (189343482397 / 1189343482397)) (n := 12)
    (lo := (321131571 / 1000000000)) (hi := (80282893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689343482397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689343482397 / 500000000000) = 1/(500000000000 / 689343482397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1271 : Bounds (321131571 / 1000000000) (80282893 / 250000000) (Real.log (689343482397 / 500000000000)) := by
  have h := reflection_log_1271_neg
  have he : Real.log (689343482397 / 500000000000) = -Real.log (500000000000 / 689343482397) := by
    rw [show ((689343482397 / 500000000000) : ℝ) = ((500000000000 / 689343482397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1272_neg : (12853471 / 40000000) ≤ -Real.log (62500000000 / 86185619127) ∧
    -Real.log (62500000000 / 86185619127) ≤ (40167097 / 125000000) := by
  have h := checkLog_sound (w := (23685619127 / 148685619127)) (n := 12)
    (lo := (12853471 / 40000000)) (hi := (40167097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86185619127 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86185619127 / 62500000000) = 1/(62500000000 / 86185619127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1272 : Bounds (12853471 / 40000000) (40167097 / 125000000) (Real.log (86185619127 / 62500000000)) := by
  have h := reflection_log_1272_neg
  have he : Real.log (86185619127 / 62500000000) = -Real.log (62500000000 / 86185619127) := by
    rw [show ((86185619127 / 62500000000) : ℝ) = ((62500000000 / 86185619127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1273_neg : (147902629 / 1000000000) ≤ -Real.log (5000 / 5797) ∧
    -Real.log (5000 / 5797) ≤ (14790263 / 100000000) := by
  have h := checkLog_sound (w := (797 / 10797)) (n := 12)
    (lo := (147902629 / 1000000000)) (hi := (14790263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5797 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5797 / 5000) = 1/(5000 / 5797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1273 : Bounds (147902629 / 1000000000) (14790263 / 100000000) (Real.log (5797 / 5000)) := by
  have h := reflection_log_1273_neg
  have he : Real.log (5797 / 5000) = -Real.log (5000 / 5797) := by
    rw [show ((5797 / 5000) : ℝ) = ((5000 / 5797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1274_neg : (43409839 / 250000000) ≤ -Real.log (4203 / 5000) ∧
    -Real.log (4203 / 5000) ≤ (173639357 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 9203)) (n := 12)
    (lo := (43409839 / 250000000)) (hi := (173639357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4203) = 1/(4203 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1274 : Bounds (-173639357 / 1000000000) (-43409839 / 250000000) (Real.log (4203 / 5000)) := by
  have h := reflection_log_1274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1275_neg : (159387 / 1000000000) ≤ -Real.log (5000000 / 5000797) ∧
    -Real.log (5000000 / 5000797) ≤ (39847 / 250000000) := by
  have h := checkLog_sound (w := (797 / 10000797)) (n := 12)
    (lo := (159387 / 1000000000)) (hi := (39847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000797 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000797 / 5000000) = 1/(5000000 / 5000797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1275 : Bounds (159387 / 1000000000) (39847 / 250000000) (Real.log (5000797 / 5000000)) := by
  have h := reflection_log_1275_neg
  have he : Real.log (5000797 / 5000000) = -Real.log (5000000 / 5000797) := by
    rw [show ((5000797 / 5000000) : ℝ) = ((5000000 / 5000797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1276_neg : (39853 / 250000000) ≤ -Real.log (4999203 / 5000000) ∧
    -Real.log (4999203 / 5000000) ≤ (159413 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 9999203)) (n := 12)
    (lo := (39853 / 250000000)) (hi := (159413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999203) = 1/(4999203 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1276 : Bounds (-159413 / 1000000000) (-39853 / 250000000) (Real.log (4999203 / 5000000)) := by
  have h := reflection_log_1276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1277_neg : (38451353 / 500000000) ≤ -Real.log (1000000 / 1079937) ∧
    -Real.log (1000000 / 1079937) ≤ (76902707 / 1000000000) := by
  have h := checkLog_sound (w := (79937 / 2079937)) (n := 12)
    (lo := (38451353 / 500000000)) (hi := (76902707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079937 / 1000000) = 1/(1000000 / 1079937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1277 : Bounds (38451353 / 500000000) (76902707 / 1000000000) (Real.log (1079937 / 1000000)) := by
  have h := reflection_log_1277_neg
  have he : Real.log (1079937 / 1000000) = -Real.log (1000000 / 1079937) := by
    rw [show ((1079937 / 1000000) : ℝ) = ((1000000 / 1079937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1278_neg : (83313133 / 1000000000) ≤ -Real.log (920063 / 1000000) ∧
    -Real.log (920063 / 1000000) ≤ (41656567 / 500000000) := by
  have h := checkLog_sound (w := (79937 / 1920063)) (n := 12)
    (lo := (83313133 / 1000000000)) (hi := (41656567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920063) = 1/(920063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1278 : Bounds (-41656567 / 500000000) (-83313133 / 1000000000) (Real.log (920063 / 1000000)) := by
  have h := reflection_log_1278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1279_neg : (19274517 / 250000000) ≤ -Real.log (250000 / 270037) ∧
    -Real.log (250000 / 270037) ≤ (77098069 / 1000000000) := by
  have h := checkLog_sound (w := (20037 / 520037)) (n := 12)
    (lo := (19274517 / 250000000)) (hi := (77098069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270037 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270037 / 250000) = 1/(250000 / 270037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1279 : Bounds (19274517 / 250000000) (77098069 / 1000000000) (Real.log (270037 / 250000)) := by
  have h := reflection_log_1279_neg
  have he : Real.log (270037 / 250000) = -Real.log (250000 / 270037) := by
    rw [show ((270037 / 250000) : ℝ) = ((250000 / 270037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


