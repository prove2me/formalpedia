-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0318Logs__6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0318Logs__6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:29:04.538727+00:00
-- url     : https://prove2.me/theorems/49090f9c-43d9-4260-882b-1917db8cf974
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0318Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0319Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0318Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0319Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0320Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0321Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0322Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0323Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0318Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0319Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0320Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0321Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0322Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0323Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0318Logs (+5 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0319Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0320Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0321Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0322Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0323Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0318Logs (+5 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0319Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0320Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0321Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0322Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0323Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0318Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0318
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

theorem reflection_log_1_neg : (219700129 / 1000000000) ≤ -Real.log (2560 / 3189) ∧
    -Real.log (2560 / 3189) ≤ (21970013 / 100000000) := by
  have h := checkLog_sound (w := (629 / 5749)) (n := 12)
    (lo := (219700129 / 1000000000)) (hi := (21970013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3189 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3189 / 2560) = 1/(2560 / 3189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (219700129 / 1000000000) (21970013 / 100000000) (Real.log (3189 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3189 / 2560) = -Real.log (2560 / 3189) := by
    rw [show ((3189 / 2560) : ℝ) = ((2560 / 3189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56393851 / 200000000) ≤ -Real.log (1931 / 2560) ∧
    -Real.log (1931 / 2560) ≤ (35246157 / 125000000) := by
  have h := checkLog_sound (w := (629 / 4491)) (n := 12)
    (lo := (56393851 / 200000000)) (hi := (35246157 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1931) = 1/(1931 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-35246157 / 125000000) (-56393851 / 200000000) (Real.log (1931 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (109732459 / 500000000) ≤ -Real.log (10240 / 12753) ∧
    -Real.log (10240 / 12753) ≤ (219464919 / 1000000000) := by
  have h := checkLog_sound (w := (2513 / 22993)) (n := 12)
    (lo := (109732459 / 500000000)) (hi := (219464919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12753 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12753 / 10240) = 1/(10240 / 12753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (109732459 / 500000000) (219464919 / 1000000000) (Real.log (12753 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12753 / 10240) = -Real.log (10240 / 12753) := by
    rw [show ((12753 / 10240) : ℝ) = ((10240 / 12753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (28158093 / 100000000) ≤ -Real.log (7727 / 10240) ∧
    -Real.log (7727 / 10240) ≤ (281580931 / 1000000000) := by
  have h := checkLog_sound (w := (2513 / 17967)) (n := 12)
    (lo := (28158093 / 100000000)) (hi := (281580931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7727) = 1/(7727 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-281580931 / 1000000000) (-28158093 / 100000000) (Real.log (7727 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (199859733 / 500000000) ≤ -Real.log (1280 / 1909) ∧
    -Real.log (1280 / 1909) ≤ (399719467 / 1000000000) := by
  have h := checkLog_sound (w := (629 / 3189)) (n := 12)
    (lo := (199859733 / 500000000)) (hi := (399719467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1909 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1909 / 1280) = 1/(1280 / 1909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (199859733 / 500000000) (399719467 / 1000000000) (Real.log (1909 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1909 / 1280) = -Real.log (1280 / 1909) := by
    rw [show ((1909 / 1280) : ℝ) = ((1280 / 1909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (338052857 / 500000000) ≤ -Real.log (651 / 1280) ∧
    -Real.log (651 / 1280) ≤ (135221143 / 200000000) := by
  have h := checkLog_sound (w := (629 / 1931)) (n := 12)
    (lo := (338052857 / 500000000)) (hi := (135221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 651) = 1/(651 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-135221143 / 200000000) (-338052857 / 500000000) (Real.log (651 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (399326513 / 1000000000) ≤ -Real.log (5120 / 7633) ∧
    -Real.log (5120 / 7633) ≤ (199663257 / 500000000) := by
  have h := checkLog_sound (w := (2513 / 12753)) (n := 12)
    (lo := (399326513 / 1000000000)) (hi := (199663257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7633 / 5120) = 1/(5120 / 7633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (399326513 / 1000000000) (199663257 / 500000000) (Real.log (7633 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7633 / 5120) = -Real.log (5120 / 7633) := by
    rw [show ((7633 / 5120) : ℝ) = ((5120 / 7633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10546161 / 15625000) ≤ -Real.log (2607 / 5120) ∧
    -Real.log (2607 / 5120) ≤ (134990861 / 200000000) := by
  have h := checkLog_sound (w := (2513 / 7727)) (n := 12)
    (lo := (10546161 / 15625000)) (hi := (134990861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2607) = 1/(2607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-134990861 / 200000000) (-10546161 / 15625000) (Real.log (2607 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75201457 / 250000000) ≤ -Real.log (1000000 / 1350947) ∧
    -Real.log (1000000 / 1350947) ≤ (300805829 / 1000000000) := by
  have h := checkLog_sound (w := (350947 / 2350947)) (n := 12)
    (lo := (75201457 / 250000000)) (hi := (300805829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350947 / 1000000) = 1/(1000000 / 1350947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75201457 / 250000000) (300805829 / 1000000000) (Real.log (1350947 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1350947 / 1000000) = -Real.log (1000000 / 1350947) := by
    rw [show ((1350947 / 1000000) : ℝ) = ((1000000 / 1350947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (432240901 / 1000000000) ≤ -Real.log (649053 / 1000000) ∧
    -Real.log (649053 / 1000000) ≤ (216120451 / 500000000) := by
  have h := checkLog_sound (w := (350947 / 1649053)) (n := 12)
    (lo := (432240901 / 1000000000)) (hi := (216120451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649053) = 1/(649053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-216120451 / 500000000) (-432240901 / 1000000000) (Real.log (649053 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37640509 / 125000000) ≤ -Real.log (1000000 / 1351377) ∧
    -Real.log (1000000 / 1351377) ≤ (301124073 / 1000000000) := by
  have h := checkLog_sound (w := (351377 / 2351377)) (n := 12)
    (lo := (37640509 / 125000000)) (hi := (301124073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351377 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351377 / 1000000) = 1/(1000000 / 1351377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37640509 / 125000000) (301124073 / 1000000000) (Real.log (1351377 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1351377 / 1000000) = -Real.log (1000000 / 1351377) := by
    rw [show ((1351377 / 1000000) : ℝ) = ((1000000 / 1351377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (54112953 / 125000000) ≤ -Real.log (648623 / 1000000) ∧
    -Real.log (648623 / 1000000) ≤ (3463229 / 8000000) := by
  have h := checkLog_sound (w := (351377 / 1648623)) (n := 12)
    (lo := (54112953 / 125000000)) (hi := (3463229 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648623) = 1/(648623 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3463229 / 8000000) (-54112953 / 125000000) (Real.log (648623 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (228657919 / 1000000000) ≤ -Real.log (62500 / 78557) ∧
    -Real.log (62500 / 78557) ≤ (178639 / 781250) := by
  have h := checkLog_sound (w := (16057 / 141057)) (n := 12)
    (lo := (228657919 / 1000000000)) (hi := (178639 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78557 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78557 / 62500) = 1/(62500 / 78557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (228657919 / 1000000000) (178639 / 781250) (Real.log (78557 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (78557 / 62500) = -Real.log (62500 / 78557) := by
    rw [show ((78557 / 62500) : ℝ) = ((62500 / 78557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (148470401 / 500000000) ≤ -Real.log (46443 / 62500) ∧
    -Real.log (46443 / 62500) ≤ (296940803 / 1000000000) := by
  have h := checkLog_sound (w := (16057 / 108943)) (n := 12)
    (lo := (148470401 / 500000000)) (hi := (296940803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46443) = 1/(46443 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-296940803 / 1000000000) (-148470401 / 500000000) (Real.log (46443 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (114463 / 500000) ≤ -Real.log (1000000 / 1257249) ∧
    -Real.log (1000000 / 1257249) ≤ (228926001 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 2257249)) (n := 12)
    (lo := (114463 / 500000)) (hi := (228926001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257249 / 1000000) = 1/(1000000 / 1257249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114463 / 500000) (228926001 / 1000000000) (Real.log (1257249 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1257249 / 1000000) = -Real.log (1000000 / 1257249) := by
    rw [show ((1257249 / 1000000) : ℝ) = ((1000000 / 1257249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (148697209 / 500000000) ≤ -Real.log (742751 / 1000000) ∧
    -Real.log (742751 / 1000000) ≤ (297394419 / 1000000000) := by
  have h := checkLog_sound (w := (257249 / 1742751)) (n := 12)
    (lo := (148697209 / 500000000)) (hi := (297394419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 742751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 742751) = 1/(742751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-297394419 / 1000000000) (-148697209 / 500000000) (Real.log (742751 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (91630841 / 125000000) ≤ -Real.log (500000000000 / 1040706228921) ∧
    -Real.log (500000000000 / 1040706228921) ≤ (73304673 / 100000000) := by
  have h := checkLog_sound (w := (40706228921 / 2040706228921)) (n := 12)
    (lo := (9974887 / 250000000)) (hi := (39899549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040706228921 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040706228921 / 1000000000000) = 1/(500000000000 / 1040706228921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (91630841 / 125000000) (73304673 / 100000000) (Real.log (1040706228921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1040706228921 / 500000000000) = -Real.log (500000000000 / 1040706228921) := by
    rw [show ((1040706228921 / 500000000000) : ℝ) = ((500000000000 / 1040706228921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (45876731 / 62500000) ≤ -Real.log (500000000000 / 1041727629147) ∧
    -Real.log (500000000000 / 1041727629147) ≤ (367013849 / 500000000) := by
  have h := checkLog_sound (w := (41727629147 / 2041727629147)) (n := 12)
    (lo := (10220129 / 250000000)) (hi := (40880517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1041727629147 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1041727629147 / 1000000000000) = 1/(500000000000 / 1041727629147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (45876731 / 62500000) (367013849 / 500000000) (Real.log (1041727629147 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1041727629147 / 500000000000) = -Real.log (500000000000 / 1041727629147) := by
    rw [show ((1041727629147 / 500000000000) : ℝ) = ((500000000000 / 1041727629147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (525598721 / 1000000000) ≤ -Real.log (250000000000 / 422867816463) ∧
    -Real.log (250000000000 / 422867816463) ≤ (262799361 / 500000000) := by
  have h := checkLog_sound (w := (172867816463 / 672867816463)) (n := 12)
    (lo := (525598721 / 1000000000)) (hi := (262799361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422867816463 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422867816463 / 250000000000) = 1/(250000000000 / 422867816463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (525598721 / 1000000000) (262799361 / 500000000) (Real.log (422867816463 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (422867816463 / 250000000000) = -Real.log (250000000000 / 422867816463) := by
    rw [show ((422867816463 / 250000000000) : ℝ) = ((250000000000 / 422867816463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (263160209 / 500000000) ≤ -Real.log (125000000000 / 211586554579) ∧
    -Real.log (125000000000 / 211586554579) ≤ (526320419 / 1000000000) := by
  have h := checkLog_sound (w := (86586554579 / 336586554579)) (n := 12)
    (lo := (263160209 / 500000000)) (hi := (526320419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211586554579 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211586554579 / 125000000000) = 1/(125000000000 / 211586554579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (263160209 / 500000000) (526320419 / 1000000000) (Real.log (211586554579 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (211586554579 / 125000000000) = -Real.log (125000000000 / 211586554579) := by
    rw [show ((211586554579 / 125000000000) : ℝ) = ((125000000000 / 211586554579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0318

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0319Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0319
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

theorem reflection_log_1_neg : (109732459 / 500000000) ≤ -Real.log (10240 / 12753) ∧
    -Real.log (10240 / 12753) ≤ (219464919 / 1000000000) := by
  have h := checkLog_sound (w := (2513 / 22993)) (n := 12)
    (lo := (109732459 / 500000000)) (hi := (219464919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12753 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12753 / 10240) = 1/(10240 / 12753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (109732459 / 500000000) (219464919 / 1000000000) (Real.log (12753 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12753 / 10240) = -Real.log (10240 / 12753) := by
    rw [show ((12753 / 10240) : ℝ) = ((10240 / 12753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28158093 / 100000000) ≤ -Real.log (7727 / 10240) ∧
    -Real.log (7727 / 10240) ≤ (281580931 / 1000000000) := by
  have h := checkLog_sound (w := (2513 / 17967)) (n := 12)
    (lo := (28158093 / 100000000)) (hi := (281580931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7727) = 1/(7727 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-281580931 / 1000000000) (-28158093 / 100000000) (Real.log (7727 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (219229651 / 1000000000) ≤ -Real.log (1024 / 1275) ∧
    -Real.log (1024 / 1275) ≤ (54807413 / 250000000) := by
  have h := checkLog_sound (w := (251 / 2299)) (n := 12)
    (lo := (219229651 / 1000000000)) (hi := (54807413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275 / 1024) = 1/(1024 / 1275) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (219229651 / 1000000000) (54807413 / 250000000) (Real.log (1275 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1275 / 1024) = -Real.log (1024 / 1275) := by
    rw [show ((1275 / 1024) : ℝ) = ((1024 / 1275) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (281192757 / 1000000000) ≤ -Real.log (773 / 1024) ∧
    -Real.log (773 / 1024) ≤ (140596379 / 500000000) := by
  have h := checkLog_sound (w := (251 / 1797)) (n := 12)
    (lo := (281192757 / 1000000000)) (hi := (140596379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 773) = 1/(773 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140596379 / 500000000) (-281192757 / 1000000000) (Real.log (773 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (399326513 / 1000000000) ≤ -Real.log (5120 / 7633) ∧
    -Real.log (5120 / 7633) ≤ (199663257 / 500000000) := by
  have h := checkLog_sound (w := (2513 / 12753)) (n := 12)
    (lo := (399326513 / 1000000000)) (hi := (199663257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7633 / 5120) = 1/(5120 / 7633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (399326513 / 1000000000) (199663257 / 500000000) (Real.log (7633 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7633 / 5120) = -Real.log (5120 / 7633) := by
    rw [show ((7633 / 5120) : ℝ) = ((5120 / 7633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10546161 / 15625000) ≤ -Real.log (2607 / 5120) ∧
    -Real.log (2607 / 5120) ≤ (134990861 / 200000000) := by
  have h := checkLog_sound (w := (2513 / 7727)) (n := 12)
    (lo := (10546161 / 15625000)) (hi := (134990861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2607) = 1/(2607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-134990861 / 200000000) (-10546161 / 15625000) (Real.log (2607 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (199466703 / 500000000) ≤ -Real.log (512 / 763) ∧
    -Real.log (512 / 763) ≤ (398933407 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1275)) (n := 12)
    (lo := (199466703 / 500000000)) (hi := (398933407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763 / 512) = 1/(512 / 763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (199466703 / 500000000) (398933407 / 1000000000) (Real.log (763 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (763 / 512) = -Real.log (512 / 763) := by
    rw [show ((763 / 512) : ℝ) = ((512 / 763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (673804217 / 1000000000) ≤ -Real.log (261 / 512) ∧
    -Real.log (261 / 512) ≤ (336902109 / 500000000) := by
  have h := checkLog_sound (w := (251 / 773)) (n := 12)
    (lo := (673804217 / 1000000000)) (hi := (336902109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 261) = 1/(261 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-336902109 / 500000000) (-673804217 / 1000000000) (Real.log (261 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (150243741 / 500000000) ≤ -Real.log (1000000 / 1350517) ∧
    -Real.log (1000000 / 1350517) ≤ (300487483 / 1000000000) := by
  have h := checkLog_sound (w := (350517 / 2350517)) (n := 12)
    (lo := (150243741 / 500000000)) (hi := (300487483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350517 / 1000000) = 1/(1000000 / 1350517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (150243741 / 500000000) (300487483 / 1000000000) (Real.log (1350517 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1350517 / 1000000) = -Real.log (1000000 / 1350517) := by
    rw [show ((1350517 / 1000000) : ℝ) = ((1000000 / 1350517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (431578617 / 1000000000) ≤ -Real.log (649483 / 1000000) ∧
    -Real.log (649483 / 1000000) ≤ (215789309 / 500000000) := by
  have h := checkLog_sound (w := (350517 / 1649483)) (n := 12)
    (lo := (431578617 / 1000000000)) (hi := (215789309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649483) = 1/(649483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-215789309 / 500000000) (-431578617 / 1000000000) (Real.log (649483 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37600821 / 125000000) ≤ -Real.log (250000 / 337737) ∧
    -Real.log (250000 / 337737) ≤ (300806569 / 1000000000) := by
  have h := checkLog_sound (w := (87737 / 587737)) (n := 12)
    (lo := (37600821 / 125000000)) (hi := (300806569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337737 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337737 / 250000) = 1/(250000 / 337737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37600821 / 125000000) (300806569 / 1000000000) (Real.log (337737 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (337737 / 250000) = -Real.log (250000 / 337737) := by
    rw [show ((337737 / 250000) : ℝ) = ((250000 / 337737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (216121221 / 500000000) ≤ -Real.log (162263 / 250000) ∧
    -Real.log (162263 / 250000) ≤ (432242443 / 1000000000) := by
  have h := checkLog_sound (w := (87737 / 412263)) (n := 12)
    (lo := (216121221 / 500000000)) (hi := (432242443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162263) = 1/(162263 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-432242443 / 1000000000) (-216121221 / 500000000) (Real.log (162263 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45677953 / 200000000) ≤ -Real.log (40000 / 50263) ∧
    -Real.log (40000 / 50263) ≤ (114194883 / 500000000) := by
  have h := checkLog_sound (w := (10263 / 90263)) (n := 12)
    (lo := (45677953 / 200000000)) (hi := (114194883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50263 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50263 / 40000) = 1/(40000 / 50263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45677953 / 200000000) (114194883 / 500000000) (Real.log (50263 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (50263 / 40000) = -Real.log (40000 / 50263) := by
    rw [show ((50263 / 40000) : ℝ) = ((40000 / 50263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9265231 / 31250000) ≤ -Real.log (29737 / 40000) ∧
    -Real.log (29737 / 40000) ≤ (296487393 / 1000000000) := by
  have h := checkLog_sound (w := (10263 / 69737)) (n := 12)
    (lo := (9265231 / 31250000)) (hi := (296487393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29737) = 1/(29737 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-296487393 / 1000000000) (-9265231 / 31250000) (Real.log (29737 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (114329357 / 500000000) ≤ -Real.log (1000000 / 1256913) ∧
    -Real.log (1000000 / 1256913) ≤ (45731743 / 200000000) := by
  have h := checkLog_sound (w := (256913 / 2256913)) (n := 12)
    (lo := (114329357 / 500000000)) (hi := (45731743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256913 / 1000000) = 1/(1000000 / 1256913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114329357 / 500000000) (45731743 / 200000000) (Real.log (1256913 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1256913 / 1000000) = -Real.log (1000000 / 1256913) := by
    rw [show ((1256913 / 1000000) : ℝ) = ((1000000 / 1256913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (74235537 / 250000000) ≤ -Real.log (743087 / 1000000) ∧
    -Real.log (743087 / 1000000) ≤ (296942149 / 1000000000) := by
  have h := checkLog_sound (w := (256913 / 1743087)) (n := 12)
    (lo := (74235537 / 250000000)) (hi := (296942149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743087) = 1/(743087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-296942149 / 1000000000) (-74235537 / 250000000) (Real.log (743087 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (366033049 / 500000000) ≤ -Real.log (250000000000 / 519843090581) ∧
    -Real.log (250000000000 / 519843090581) ≤ (7320661 / 10000000) := by
  have h := checkLog_sound (w := (19843090581 / 1019843090581)) (n := 12)
    (lo := (19459459 / 500000000)) (hi := (38918919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519843090581 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(519843090581 / 500000000000) = 1/(250000000000 / 519843090581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (366033049 / 500000000) (7320661 / 10000000) (Real.log (519843090581 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (519843090581 / 250000000000) = -Real.log (250000000000 / 519843090581) := by
    rw [show ((519843090581 / 250000000000) : ℝ) = ((250000000000 / 519843090581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (733049009 / 1000000000) ≤ -Real.log (500000000000 / 1040708602701) ∧
    -Real.log (500000000000 / 1040708602701) ≤ (733049011 / 1000000000) := by
  have h := checkLog_sound (w := (40708602701 / 2040708602701)) (n := 12)
    (lo := (39901829 / 1000000000)) (hi := (3990183 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040708602701 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040708602701 / 1000000000000) = 1/(500000000000 / 1040708602701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (733049009 / 1000000000) (733049011 / 1000000000) (Real.log (1040708602701 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1040708602701 / 500000000000) = -Real.log (500000000000 / 1040708602701) := by
    rw [show ((1040708602701 / 500000000000) : ℝ) = ((500000000000 / 1040708602701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (262438579 / 500000000) ≤ -Real.log (500000000000 / 845125601103) ∧
    -Real.log (500000000000 / 845125601103) ≤ (524877159 / 1000000000) := by
  have h := checkLog_sound (w := (345125601103 / 1345125601103)) (n := 12)
    (lo := (262438579 / 500000000)) (hi := (524877159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845125601103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845125601103 / 500000000000) = 1/(500000000000 / 845125601103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (262438579 / 500000000) (524877159 / 1000000000) (Real.log (845125601103 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (845125601103 / 500000000000) = -Real.log (500000000000 / 845125601103) := by
    rw [show ((845125601103 / 500000000000) : ℝ) = ((500000000000 / 845125601103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (525600863 / 1000000000) ≤ -Real.log (250000000000 / 422868721967) ∧
    -Real.log (250000000000 / 422868721967) ≤ (16425027 / 31250000) := by
  have h := checkLog_sound (w := (172868721967 / 672868721967)) (n := 12)
    (lo := (525600863 / 1000000000)) (hi := (16425027 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422868721967 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422868721967 / 250000000000) = 1/(250000000000 / 422868721967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (525600863 / 1000000000) (16425027 / 31250000) (Real.log (422868721967 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (422868721967 / 250000000000) = -Real.log (250000000000 / 422868721967) := by
    rw [show ((422868721967 / 250000000000) : ℝ) = ((250000000000 / 422868721967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0319

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0320Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0320
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

theorem reflection_log_1_neg : (219229651 / 1000000000) ≤ -Real.log (1024 / 1275) ∧
    -Real.log (1024 / 1275) ≤ (54807413 / 250000000) := by
  have h := checkLog_sound (w := (251 / 2299)) (n := 12)
    (lo := (219229651 / 1000000000)) (hi := (54807413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275 / 1024) = 1/(1024 / 1275) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (219229651 / 1000000000) (54807413 / 250000000) (Real.log (1275 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1275 / 1024) = -Real.log (1024 / 1275) := by
    rw [show ((1275 / 1024) : ℝ) = ((1024 / 1275) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (281192757 / 1000000000) ≤ -Real.log (773 / 1024) ∧
    -Real.log (773 / 1024) ≤ (140596379 / 500000000) := by
  have h := checkLog_sound (w := (251 / 1797)) (n := 12)
    (lo := (281192757 / 1000000000)) (hi := (140596379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 773) = 1/(773 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140596379 / 500000000) (-281192757 / 1000000000) (Real.log (773 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21899433 / 100000000) ≤ -Real.log (10240 / 12747) ∧
    -Real.log (10240 / 12747) ≤ (218994331 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 22987)) (n := 12)
    (lo := (21899433 / 100000000)) (hi := (218994331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12747 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12747 / 10240) = 1/(10240 / 12747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21899433 / 100000000) (218994331 / 1000000000) (Real.log (12747 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12747 / 10240) = -Real.log (10240 / 12747) := by
    rw [show ((12747 / 10240) : ℝ) = ((10240 / 12747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280804733 / 1000000000) ≤ -Real.log (7733 / 10240) ∧
    -Real.log (7733 / 10240) ≤ (140402367 / 500000000) := by
  have h := checkLog_sound (w := (2507 / 17973)) (n := 12)
    (lo := (280804733 / 1000000000)) (hi := (140402367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7733) = 1/(7733 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140402367 / 500000000) (-280804733 / 1000000000) (Real.log (7733 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (199466703 / 500000000) ≤ -Real.log (512 / 763) ∧
    -Real.log (512 / 763) ≤ (398933407 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1275)) (n := 12)
    (lo := (199466703 / 500000000)) (hi := (398933407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763 / 512) = 1/(512 / 763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (199466703 / 500000000) (398933407 / 1000000000) (Real.log (763 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (763 / 512) = -Real.log (512 / 763) := by
    rw [show ((763 / 512) : ℝ) = ((512 / 763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (673804217 / 1000000000) ≤ -Real.log (261 / 512) ∧
    -Real.log (261 / 512) ≤ (336902109 / 500000000) := by
  have h := checkLog_sound (w := (251 / 773)) (n := 12)
    (lo := (673804217 / 1000000000)) (hi := (336902109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 261) = 1/(261 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-336902109 / 500000000) (-673804217 / 1000000000) (Real.log (261 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24908759 / 62500000) ≤ -Real.log (5120 / 7627) ∧
    -Real.log (5120 / 7627) ≤ (79708029 / 200000000) := by
  have h := checkLog_sound (w := (2507 / 12747)) (n := 12)
    (lo := (24908759 / 62500000)) (hi := (79708029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7627 / 5120) = 1/(5120 / 7627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24908759 / 62500000) (79708029 / 200000000) (Real.log (7627 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7627 / 5120) = -Real.log (5120 / 7627) := by
    rw [show ((7627 / 5120) : ℝ) = ((5120 / 7627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (168163863 / 250000000) ≤ -Real.log (2613 / 5120) ∧
    -Real.log (2613 / 5120) ≤ (672655453 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 7733)) (n := 12)
    (lo := (168163863 / 250000000)) (hi := (672655453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2613) = 1/(2613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-672655453 / 1000000000) (-168163863 / 250000000) (Real.log (2613 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12006791 / 40000000) ≤ -Real.log (125000 / 168761) ∧
    -Real.log (125000 / 168761) ≤ (18760611 / 62500000) := by
  have h := checkLog_sound (w := (43761 / 293761)) (n := 12)
    (lo := (12006791 / 40000000)) (hi := (18760611 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168761 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168761 / 125000) = 1/(125000 / 168761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12006791 / 40000000) (18760611 / 62500000) (Real.log (168761 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (168761 / 125000) = -Real.log (125000 / 168761) := by
    rw [show ((168761 / 125000) : ℝ) = ((125000 / 168761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (430918309 / 1000000000) ≤ -Real.log (81239 / 125000) ∧
    -Real.log (81239 / 125000) ≤ (43091831 / 100000000) := by
  have h := checkLog_sound (w := (43761 / 206239)) (n := 12)
    (lo := (430918309 / 1000000000)) (hi := (43091831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 81239) = 1/(81239 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43091831 / 100000000) (-430918309 / 1000000000) (Real.log (81239 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (300488963 / 1000000000) ≤ -Real.log (1000000 / 1350519) ∧
    -Real.log (1000000 / 1350519) ≤ (75122241 / 250000000) := by
  have h := checkLog_sound (w := (350519 / 2350519)) (n := 12)
    (lo := (300488963 / 1000000000)) (hi := (75122241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350519 / 1000000) = 1/(1000000 / 1350519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (300488963 / 1000000000) (75122241 / 250000000) (Real.log (1350519 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1350519 / 1000000) = -Real.log (1000000 / 1350519) := by
    rw [show ((1350519 / 1000000) : ℝ) = ((1000000 / 1350519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (842933 / 1953125) ≤ -Real.log (649481 / 1000000) ∧
    -Real.log (649481 / 1000000) ≤ (431581697 / 1000000000) := by
  have h := checkLog_sound (w := (350519 / 1649481)) (n := 12)
    (lo := (842933 / 1953125)) (hi := (431581697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649481) = 1/(649481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-431581697 / 1000000000) (-842933 / 1953125) (Real.log (649481 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7128823 / 31250000) ≤ -Real.log (1000000 / 1256239) ∧
    -Real.log (1000000 / 1256239) ≤ (228122337 / 1000000000) := by
  have h := checkLog_sound (w := (256239 / 2256239)) (n := 12)
    (lo := (7128823 / 31250000)) (hi := (228122337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256239 / 1000000) = 1/(1000000 / 1256239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7128823 / 31250000) (228122337 / 1000000000) (Real.log (1256239 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1256239 / 1000000) = -Real.log (1000000 / 1256239) := by
    rw [show ((1256239 / 1000000) : ℝ) = ((1000000 / 1256239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (74008883 / 250000000) ≤ -Real.log (743761 / 1000000) ∧
    -Real.log (743761 / 1000000) ≤ (296035533 / 1000000000) := by
  have h := checkLog_sound (w := (256239 / 1743761)) (n := 12)
    (lo := (74008883 / 250000000)) (hi := (296035533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743761) = 1/(743761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-296035533 / 1000000000) (-74008883 / 250000000) (Real.log (743761 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (228390561 / 1000000000) ≤ -Real.log (15625 / 19634) ∧
    -Real.log (15625 / 19634) ≤ (114195281 / 500000000) := by
  have h := checkLog_sound (w := (4009 / 35259)) (n := 12)
    (lo := (228390561 / 1000000000)) (hi := (114195281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19634 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19634 / 15625) = 1/(15625 / 19634) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (228390561 / 1000000000) (114195281 / 500000000) (Real.log (19634 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19634 / 15625) = -Real.log (15625 / 19634) := by
    rw [show ((19634 / 15625) : ℝ) = ((15625 / 19634) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (296488737 / 1000000000) ≤ -Real.log (11616 / 15625) ∧
    -Real.log (11616 / 15625) ≤ (148244369 / 500000000) := by
  have h := checkLog_sound (w := (4009 / 27241)) (n := 12)
    (lo := (296488737 / 1000000000)) (hi := (148244369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11616) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11616) = 1/(11616 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-148244369 / 500000000) (-296488737 / 1000000000) (Real.log (11616 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (182772021 / 250000000) ≤ -Real.log (500000000000 / 1038669850687) ∧
    -Real.log (500000000000 / 1038669850687) ≤ (365544043 / 500000000) := by
  have h := checkLog_sound (w := (38669850687 / 2038669850687)) (n := 12)
    (lo := (4742613 / 125000000)) (hi := (7588181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1038669850687 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1038669850687 / 1000000000000) = 1/(500000000000 / 1038669850687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (182772021 / 250000000) (365544043 / 500000000) (Real.log (1038669850687 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1038669850687 / 500000000000) = -Real.log (500000000000 / 1038669850687) := by
    rw [show ((1038669850687 / 500000000000) : ℝ) = ((500000000000 / 1038669850687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (732070659 / 1000000000) ≤ -Real.log (100000000000 / 207938184489) ∧
    -Real.log (100000000000 / 207938184489) ≤ (732070661 / 1000000000) := by
  have h := checkLog_sound (w := (7938184489 / 407938184489)) (n := 12)
    (lo := (38923479 / 1000000000)) (hi := (973087 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207938184489 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207938184489 / 200000000000) = 1/(100000000000 / 207938184489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (732070659 / 1000000000) (732070661 / 1000000000) (Real.log (207938184489 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (207938184489 / 100000000000) = -Real.log (100000000000 / 207938184489) := by
    rw [show ((207938184489 / 100000000000) : ℝ) = ((100000000000 / 207938184489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (131039467 / 250000000) ≤ -Real.log (250000000000 / 422258964909) ∧
    -Real.log (250000000000 / 422258964909) ≤ (524157869 / 1000000000) := by
  have h := checkLog_sound (w := (172258964909 / 672258964909)) (n := 12)
    (lo := (131039467 / 250000000)) (hi := (524157869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422258964909 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422258964909 / 250000000000) = 1/(250000000000 / 422258964909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (131039467 / 250000000) (524157869 / 1000000000) (Real.log (422258964909 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (422258964909 / 250000000000) = -Real.log (250000000000 / 422258964909) := by
    rw [show ((422258964909 / 250000000000) : ℝ) = ((250000000000 / 422258964909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (524879299 / 1000000000) ≤ -Real.log (500000000000 / 845127410469) ∧
    -Real.log (500000000000 / 845127410469) ≤ (5248793 / 10000000) := by
  have h := checkLog_sound (w := (345127410469 / 1345127410469)) (n := 12)
    (lo := (524879299 / 1000000000)) (hi := (5248793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845127410469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845127410469 / 500000000000) = 1/(500000000000 / 845127410469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (524879299 / 1000000000) (5248793 / 10000000) (Real.log (845127410469 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (845127410469 / 500000000000) = -Real.log (500000000000 / 845127410469) := by
    rw [show ((845127410469 / 500000000000) : ℝ) = ((500000000000 / 845127410469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0320

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0321Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0321
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

theorem reflection_log_1_neg : (21899433 / 100000000) ≤ -Real.log (10240 / 12747) ∧
    -Real.log (10240 / 12747) ≤ (218994331 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 22987)) (n := 12)
    (lo := (21899433 / 100000000)) (hi := (218994331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12747 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12747 / 10240) = 1/(10240 / 12747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21899433 / 100000000) (218994331 / 1000000000) (Real.log (12747 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12747 / 10240) = -Real.log (10240 / 12747) := by
    rw [show ((12747 / 10240) : ℝ) = ((10240 / 12747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280804733 / 1000000000) ≤ -Real.log (7733 / 10240) ∧
    -Real.log (7733 / 10240) ≤ (140402367 / 500000000) := by
  have h := checkLog_sound (w := (2507 / 17973)) (n := 12)
    (lo := (280804733 / 1000000000)) (hi := (140402367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7733) = 1/(7733 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140402367 / 500000000) (-280804733 / 1000000000) (Real.log (7733 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27344869 / 125000000) ≤ -Real.log (1280 / 1593) ∧
    -Real.log (1280 / 1593) ≤ (218758953 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 2873)) (n := 12)
    (lo := (27344869 / 125000000)) (hi := (218758953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593 / 1280) = 1/(1280 / 1593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27344869 / 125000000) (218758953 / 1000000000) (Real.log (1593 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1593 / 1280) = -Real.log (1280 / 1593) := by
    rw [show ((1593 / 1280) : ℝ) = ((1280 / 1593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280416861 / 1000000000) ≤ -Real.log (967 / 1280) ∧
    -Real.log (967 / 1280) ≤ (140208431 / 500000000) := by
  have h := checkLog_sound (w := (313 / 2247)) (n := 12)
    (lo := (280416861 / 1000000000)) (hi := (140208431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 967) = 1/(967 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140208431 / 500000000) (-280416861 / 1000000000) (Real.log (967 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24908759 / 62500000) ≤ -Real.log (5120 / 7627) ∧
    -Real.log (5120 / 7627) ≤ (79708029 / 200000000) := by
  have h := checkLog_sound (w := (2507 / 12747)) (n := 12)
    (lo := (24908759 / 62500000)) (hi := (79708029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7627 / 5120) = 1/(5120 / 7627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24908759 / 62500000) (79708029 / 200000000) (Real.log (7627 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7627 / 5120) = -Real.log (5120 / 7627) := by
    rw [show ((7627 / 5120) : ℝ) = ((5120 / 7627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (168163863 / 250000000) ≤ -Real.log (2613 / 5120) ∧
    -Real.log (2613 / 5120) ≤ (672655453 / 1000000000) := by
  have h := checkLog_sound (w := (2507 / 7733)) (n := 12)
    (lo := (168163863 / 250000000)) (hi := (672655453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2613) = 1/(2613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-672655453 / 1000000000) (-168163863 / 250000000) (Real.log (2613 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (398146727 / 1000000000) ≤ -Real.log (640 / 953) ∧
    -Real.log (640 / 953) ≤ (49768341 / 125000000) := by
  have h := checkLog_sound (w := (313 / 1593)) (n := 12)
    (lo := (398146727 / 1000000000)) (hi := (49768341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953 / 640) = 1/(640 / 953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (398146727 / 1000000000) (49768341 / 125000000) (Real.log (953 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (953 / 640) = -Real.log (640 / 953) := by
    rw [show ((953 / 640) : ℝ) = ((640 / 953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (134301601 / 200000000) ≤ -Real.log (327 / 640) ∧
    -Real.log (327 / 640) ≤ (335754003 / 500000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 327) = 1/(327 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-335754003 / 500000000) (-134301601 / 200000000) (Real.log (327 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (299851967 / 1000000000) ≤ -Real.log (1000000 / 1349659) ∧
    -Real.log (1000000 / 1349659) ≤ (4685187 / 15625000) := by
  have h := checkLog_sound (w := (349659 / 2349659)) (n := 12)
    (lo := (299851967 / 1000000000)) (hi := (4685187 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349659 / 1000000) = 1/(1000000 / 1349659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (299851967 / 1000000000) (4685187 / 15625000) (Real.log (1349659 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1349659 / 1000000) = -Real.log (1000000 / 1349659) := by
    rw [show ((1349659 / 1000000) : ℝ) = ((1000000 / 1349659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (215129219 / 500000000) ≤ -Real.log (650341 / 1000000) ∧
    -Real.log (650341 / 1000000) ≤ (430258439 / 1000000000) := by
  have h := checkLog_sound (w := (349659 / 1650341)) (n := 12)
    (lo := (215129219 / 500000000)) (hi := (430258439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 650341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 650341) = 1/(650341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-430258439 / 1000000000) (-215129219 / 500000000) (Real.log (650341 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75042629 / 250000000) ≤ -Real.log (1000000 / 1350089) ∧
    -Real.log (1000000 / 1350089) ≤ (300170517 / 1000000000) := by
  have h := checkLog_sound (w := (350089 / 2350089)) (n := 12)
    (lo := (75042629 / 250000000)) (hi := (300170517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350089 / 1000000) = 1/(1000000 / 1350089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75042629 / 250000000) (300170517 / 1000000000) (Real.log (1350089 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1350089 / 1000000) = -Real.log (1000000 / 1350089) := by
    rw [show ((1350089 / 1000000) : ℝ) = ((1000000 / 1350089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53864981 / 125000000) ≤ -Real.log (649911 / 1000000) ∧
    -Real.log (649911 / 1000000) ≤ (430919849 / 1000000000) := by
  have h := checkLog_sound (w := (350089 / 1649911)) (n := 12)
    (lo := (53864981 / 125000000)) (hi := (430919849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649911) = 1/(649911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-430919849 / 1000000000) (-53864981 / 125000000) (Real.log (649911 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45570967 / 200000000) ≤ -Real.log (1000000 / 1255903) ∧
    -Real.log (1000000 / 1255903) ≤ (56963709 / 250000000) := by
  have h := checkLog_sound (w := (255903 / 2255903)) (n := 12)
    (lo := (45570967 / 200000000)) (hi := (56963709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255903 / 1000000) = 1/(1000000 / 1255903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45570967 / 200000000) (56963709 / 250000000) (Real.log (1255903 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1255903 / 1000000) = -Real.log (1000000 / 1255903) := by
    rw [show ((1255903 / 1000000) : ℝ) = ((1000000 / 1255903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (73895969 / 250000000) ≤ -Real.log (744097 / 1000000) ∧
    -Real.log (744097 / 1000000) ≤ (295583877 / 1000000000) := by
  have h := checkLog_sound (w := (255903 / 1744097)) (n := 12)
    (lo := (73895969 / 250000000)) (hi := (295583877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744097) = 1/(744097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-295583877 / 1000000000) (-73895969 / 250000000) (Real.log (744097 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (57030783 / 250000000) ≤ -Real.log (12500 / 15703) ∧
    -Real.log (12500 / 15703) ≤ (228123133 / 1000000000) := by
  have h := checkLog_sound (w := (3203 / 28203)) (n := 12)
    (lo := (57030783 / 250000000)) (hi := (228123133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15703 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15703 / 12500) = 1/(12500 / 15703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (57030783 / 250000000) (228123133 / 1000000000) (Real.log (15703 / 12500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (15703 / 12500) = -Real.log (12500 / 15703) := by
    rw [show ((15703 / 12500) : ℝ) = ((12500 / 15703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (74009219 / 250000000) ≤ -Real.log (9297 / 12500) ∧
    -Real.log (9297 / 12500) ≤ (296036877 / 1000000000) := by
  have h := checkLog_sound (w := (3203 / 21797)) (n := 12)
    (lo := (74009219 / 250000000)) (hi := (296036877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9297) = 1/(9297 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-296036877 / 1000000000) (-74009219 / 250000000) (Real.log (9297 / 12500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (146022081 / 200000000) ≤ -Real.log (100000000000 / 207530972213) ∧
    -Real.log (100000000000 / 207530972213) ≤ (730110407 / 1000000000) := by
  have h := checkLog_sound (w := (7530972213 / 407530972213)) (n := 12)
    (lo := (1478529 / 40000000)) (hi := (18481613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207530972213 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207530972213 / 200000000000) = 1/(100000000000 / 207530972213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (146022081 / 200000000) (730110407 / 1000000000) (Real.log (207530972213 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (207530972213 / 100000000000) = -Real.log (100000000000 / 207530972213) := by
    rw [show ((207530972213 / 100000000000) : ℝ) = ((100000000000 / 207530972213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182772591 / 250000000) ≤ -Real.log (500000000000 / 1038672218197) ∧
    -Real.log (500000000000 / 1038672218197) ≤ (365545183 / 500000000) := by
  have h := checkLog_sound (w := (38672218197 / 2038672218197)) (n := 12)
    (lo := (2371449 / 62500000)) (hi := (7588637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1038672218197 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1038672218197 / 1000000000000) = 1/(500000000000 / 1038672218197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182772591 / 250000000) (365545183 / 500000000) (Real.log (1038672218197 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1038672218197 / 500000000000) = -Real.log (500000000000 / 1038672218197) := by
    rw [show ((1038672218197 / 500000000000) : ℝ) = ((500000000000 / 1038672218197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (65429839 / 125000000) ≤ -Real.log (500000000000 / 843910807327) ∧
    -Real.log (500000000000 / 843910807327) ≤ (523438713 / 1000000000) := by
  have h := checkLog_sound (w := (343910807327 / 1343910807327)) (n := 12)
    (lo := (65429839 / 125000000)) (hi := (523438713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843910807327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843910807327 / 500000000000) = 1/(500000000000 / 843910807327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (65429839 / 125000000) (523438713 / 1000000000) (Real.log (843910807327 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (843910807327 / 500000000000) = -Real.log (500000000000 / 843910807327) := by
    rw [show ((843910807327 / 500000000000) : ℝ) = ((500000000000 / 843910807327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (524160009 / 1000000000) ≤ -Real.log (10000000000 / 16890394751) ∧
    -Real.log (10000000000 / 16890394751) ≤ (52416001 / 100000000) := by
  have h := checkLog_sound (w := (6890394751 / 26890394751)) (n := 12)
    (lo := (524160009 / 1000000000)) (hi := (52416001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16890394751 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16890394751 / 10000000000) = 1/(10000000000 / 16890394751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (524160009 / 1000000000) (52416001 / 100000000) (Real.log (16890394751 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16890394751 / 10000000000) = -Real.log (10000000000 / 16890394751) := by
    rw [show ((16890394751 / 10000000000) : ℝ) = ((10000000000 / 16890394751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0321

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0322Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0322
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

theorem reflection_log_1_neg : (27344869 / 125000000) ≤ -Real.log (1280 / 1593) ∧
    -Real.log (1280 / 1593) ≤ (218758953 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 2873)) (n := 12)
    (lo := (27344869 / 125000000)) (hi := (218758953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593 / 1280) = 1/(1280 / 1593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27344869 / 125000000) (218758953 / 1000000000) (Real.log (1593 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1593 / 1280) = -Real.log (1280 / 1593) := by
    rw [show ((1593 / 1280) : ℝ) = ((1280 / 1593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280416861 / 1000000000) ≤ -Real.log (967 / 1280) ∧
    -Real.log (967 / 1280) ≤ (140208431 / 500000000) := by
  have h := checkLog_sound (w := (313 / 2247)) (n := 12)
    (lo := (280416861 / 1000000000)) (hi := (140208431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 967) = 1/(967 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140208431 / 500000000) (-280416861 / 1000000000) (Real.log (967 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341443 / 1562500) ≤ -Real.log (10240 / 12741) ∧
    -Real.log (10240 / 12741) ≤ (218523521 / 1000000000) := by
  have h := checkLog_sound (w := (2501 / 22981)) (n := 12)
    (lo := (341443 / 1562500)) (hi := (218523521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12741 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12741 / 10240) = 1/(10240 / 12741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341443 / 1562500) (218523521 / 1000000000) (Real.log (12741 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12741 / 10240) = -Real.log (10240 / 12741) := by
    rw [show ((12741 / 10240) : ℝ) = ((10240 / 12741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280029139 / 1000000000) ≤ -Real.log (7739 / 10240) ∧
    -Real.log (7739 / 10240) ≤ (14001457 / 50000000) := by
  have h := checkLog_sound (w := (2501 / 17979)) (n := 12)
    (lo := (280029139 / 1000000000)) (hi := (14001457 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7739) = 1/(7739 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14001457 / 50000000) (-280029139 / 1000000000) (Real.log (7739 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (398146727 / 1000000000) ≤ -Real.log (640 / 953) ∧
    -Real.log (640 / 953) ≤ (49768341 / 125000000) := by
  have h := checkLog_sound (w := (313 / 1593)) (n := 12)
    (lo := (398146727 / 1000000000)) (hi := (49768341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953 / 640) = 1/(640 / 953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (398146727 / 1000000000) (49768341 / 125000000) (Real.log (953 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (953 / 640) = -Real.log (640 / 953) := by
    rw [show ((953 / 640) : ℝ) = ((640 / 953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (134301601 / 200000000) ≤ -Real.log (327 / 640) ∧
    -Real.log (327 / 640) ≤ (335754003 / 500000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 327) = 1/(327 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-335754003 / 500000000) (-134301601 / 200000000) (Real.log (327 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (79550631 / 200000000) ≤ -Real.log (5120 / 7621) ∧
    -Real.log (5120 / 7621) ≤ (99438289 / 250000000) := by
  have h := checkLog_sound (w := (2501 / 12741)) (n := 12)
    (lo := (79550631 / 200000000)) (hi := (99438289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7621 / 5120) = 1/(5120 / 7621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (79550631 / 200000000) (99438289 / 250000000) (Real.log (7621 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7621 / 5120) = -Real.log (5120 / 7621) := by
    rw [show ((7621 / 5120) : ℝ) = ((5120 / 7621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (670361873 / 1000000000) ≤ -Real.log (2619 / 5120) ∧
    -Real.log (2619 / 5120) ≤ (335180937 / 500000000) := by
  have h := checkLog_sound (w := (2501 / 7739)) (n := 12)
    (lo := (670361873 / 1000000000)) (hi := (335180937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2619) = 1/(2619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-335180937 / 500000000) (-670361873 / 1000000000) (Real.log (2619 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (299534059 / 1000000000) ≤ -Real.log (100000 / 134923) ∧
    -Real.log (100000 / 134923) ≤ (14976703 / 50000000) := by
  have h := checkLog_sound (w := (34923 / 234923)) (n := 12)
    (lo := (299534059 / 1000000000)) (hi := (14976703 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134923 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134923 / 100000) = 1/(100000 / 134923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (299534059 / 1000000000) (14976703 / 50000000) (Real.log (134923 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (134923 / 100000) = -Real.log (100000 / 134923) := by
    rw [show ((134923 / 100000) : ℝ) = ((100000 / 134923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (429599001 / 1000000000) ≤ -Real.log (65077 / 100000) ∧
    -Real.log (65077 / 100000) ≤ (214799501 / 500000000) := by
  have h := checkLog_sound (w := (34923 / 165077)) (n := 12)
    (lo := (429599001 / 1000000000)) (hi := (214799501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 65077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 65077) = 1/(65077 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214799501 / 500000000) (-429599001 / 1000000000) (Real.log (65077 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (74963177 / 250000000) ≤ -Real.log (50000 / 67483) ∧
    -Real.log (50000 / 67483) ≤ (299852709 / 1000000000) := by
  have h := checkLog_sound (w := (17483 / 117483)) (n := 12)
    (lo := (74963177 / 250000000)) (hi := (299852709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67483 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67483 / 50000) = 1/(50000 / 67483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (74963177 / 250000000) (299852709 / 1000000000) (Real.log (67483 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (67483 / 50000) = -Real.log (50000 / 67483) := by
    rw [show ((67483 / 50000) : ℝ) = ((50000 / 67483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17210399 / 40000000) ≤ -Real.log (32517 / 50000) ∧
    -Real.log (32517 / 50000) ≤ (53782497 / 125000000) := by
  have h := checkLog_sound (w := (17483 / 82517)) (n := 12)
    (lo := (17210399 / 40000000)) (hi := (53782497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32517) = 1/(32517 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-53782497 / 125000000) (-17210399 / 40000000) (Real.log (32517 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (227587263 / 1000000000) ≤ -Real.log (1000000 / 1255567) ∧
    -Real.log (1000000 / 1255567) ≤ (3556051 / 15625000) := by
  have h := checkLog_sound (w := (255567 / 2255567)) (n := 12)
    (lo := (227587263 / 1000000000)) (hi := (3556051 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255567 / 1000000) = 1/(1000000 / 1255567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (227587263 / 1000000000) (3556051 / 15625000) (Real.log (1255567 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1255567 / 1000000) = -Real.log (1000000 / 1255567) := by
    rw [show ((1255567 / 1000000) : ℝ) = ((1000000 / 1255567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (36891553 / 125000000) ≤ -Real.log (744433 / 1000000) ∧
    -Real.log (744433 / 1000000) ≤ (11805297 / 40000000) := by
  have h := checkLog_sound (w := (255567 / 1744433)) (n := 12)
    (lo := (36891553 / 125000000)) (hi := (11805297 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744433) = 1/(744433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11805297 / 40000000) (-36891553 / 125000000) (Real.log (744433 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14240977 / 62500000) ≤ -Real.log (31250 / 39247) ∧
    -Real.log (31250 / 39247) ≤ (227855633 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 70497)) (n := 12)
    (lo := (14240977 / 62500000)) (hi := (227855633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39247 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39247 / 31250) = 1/(31250 / 39247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14240977 / 62500000) (227855633 / 1000000000) (Real.log (39247 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39247 / 31250) = -Real.log (31250 / 39247) := by
    rw [show ((39247 / 31250) : ℝ) = ((31250 / 39247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14779261 / 50000000) ≤ -Real.log (23253 / 31250) ∧
    -Real.log (23253 / 31250) ≤ (295585221 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 54503)) (n := 12)
    (lo := (14779261 / 50000000)) (hi := (295585221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23253) = 1/(23253 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-295585221 / 1000000000) (-14779261 / 50000000) (Real.log (23253 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (36456653 / 50000000) ≤ -Real.log (500000000000 / 1036641209643) ∧
    -Real.log (500000000000 / 1036641209643) ≤ (364566531 / 500000000) := by
  have h := checkLog_sound (w := (36641209643 / 2036641209643)) (n := 12)
    (lo := (899647 / 25000000)) (hi := (35985881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1036641209643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1036641209643 / 1000000000000) = 1/(500000000000 / 1036641209643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36456653 / 50000000) (364566531 / 500000000) (Real.log (1036641209643 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1036641209643 / 500000000000) = -Real.log (500000000000 / 1036641209643) := by
    rw [show ((1036641209643 / 500000000000) : ℝ) = ((500000000000 / 1036641209643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182528171 / 250000000) ≤ -Real.log (125000000000 / 259414306363) ∧
    -Real.log (125000000000 / 259414306363) ≤ (365056343 / 500000000) := by
  have h := checkLog_sound (w := (9414306363 / 509414306363)) (n := 12)
    (lo := (288793 / 7812500)) (hi := (7393101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259414306363 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259414306363 / 250000000000) = 1/(125000000000 / 259414306363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182528171 / 250000000) (365056343 / 500000000) (Real.log (259414306363 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (259414306363 / 125000000000) = -Real.log (125000000000 / 259414306363) := by
    rw [show ((259414306363 / 125000000000) : ℝ) = ((125000000000 / 259414306363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (522719687 / 1000000000) ≤ -Real.log (100000000000 / 168660846577) ∧
    -Real.log (100000000000 / 168660846577) ≤ (65339961 / 125000000) := by
  have h := checkLog_sound (w := (68660846577 / 268660846577)) (n := 12)
    (lo := (522719687 / 1000000000)) (hi := (65339961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168660846577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168660846577 / 100000000000) = 1/(100000000000 / 168660846577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (522719687 / 1000000000) (65339961 / 125000000) (Real.log (168660846577 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (168660846577 / 100000000000) = -Real.log (100000000000 / 168660846577) := by
    rw [show ((168660846577 / 100000000000) : ℝ) = ((100000000000 / 168660846577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (130860213 / 250000000) ≤ -Real.log (500000000000 / 843912613427) ∧
    -Real.log (500000000000 / 843912613427) ≤ (523440853 / 1000000000) := by
  have h := checkLog_sound (w := (343912613427 / 1343912613427)) (n := 12)
    (lo := (130860213 / 250000000)) (hi := (523440853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843912613427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843912613427 / 500000000000) = 1/(500000000000 / 843912613427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (130860213 / 250000000) (523440853 / 1000000000) (Real.log (843912613427 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (843912613427 / 500000000000) = -Real.log (500000000000 / 843912613427) := by
    rw [show ((843912613427 / 500000000000) : ℝ) = ((500000000000 / 843912613427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0322

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0323Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0323
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

theorem reflection_log_1_neg : (341443 / 1562500) ≤ -Real.log (10240 / 12741) ∧
    -Real.log (10240 / 12741) ≤ (218523521 / 1000000000) := by
  have h := checkLog_sound (w := (2501 / 22981)) (n := 12)
    (lo := (341443 / 1562500)) (hi := (218523521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12741 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12741 / 10240) = 1/(10240 / 12741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (341443 / 1562500) (218523521 / 1000000000) (Real.log (12741 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12741 / 10240) = -Real.log (10240 / 12741) := by
    rw [show ((12741 / 10240) : ℝ) = ((10240 / 12741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280029139 / 1000000000) ≤ -Real.log (7739 / 10240) ∧
    -Real.log (7739 / 10240) ≤ (14001457 / 50000000) := by
  have h := checkLog_sound (w := (2501 / 17979)) (n := 12)
    (lo := (280029139 / 1000000000)) (hi := (14001457 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7739) = 1/(7739 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14001457 / 50000000) (-280029139 / 1000000000) (Real.log (7739 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (6821501 / 31250000) ≤ -Real.log (5120 / 6369) ∧
    -Real.log (5120 / 6369) ≤ (218288033 / 1000000000) := by
  have h := checkLog_sound (w := (1249 / 11489)) (n := 12)
    (lo := (6821501 / 31250000)) (hi := (218288033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6369 / 5120) = 1/(5120 / 6369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (6821501 / 31250000) (218288033 / 1000000000) (Real.log (6369 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6369 / 5120) = -Real.log (5120 / 6369) := by
    rw [show ((6369 / 5120) : ℝ) = ((5120 / 6369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (279641567 / 1000000000) ≤ -Real.log (3871 / 5120) ∧
    -Real.log (3871 / 5120) ≤ (8738799 / 31250000) := by
  have h := checkLog_sound (w := (1249 / 8991)) (n := 12)
    (lo := (279641567 / 1000000000)) (hi := (8738799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3871) = 1/(3871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8738799 / 31250000) (-279641567 / 1000000000) (Real.log (3871 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (79550631 / 200000000) ≤ -Real.log (5120 / 7621) ∧
    -Real.log (5120 / 7621) ≤ (99438289 / 250000000) := by
  have h := checkLog_sound (w := (2501 / 12741)) (n := 12)
    (lo := (79550631 / 200000000)) (hi := (99438289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7621 / 5120) = 1/(5120 / 7621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (79550631 / 200000000) (99438289 / 250000000) (Real.log (7621 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7621 / 5120) = -Real.log (5120 / 7621) := by
    rw [show ((7621 / 5120) : ℝ) = ((5120 / 7621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (670361873 / 1000000000) ≤ -Real.log (2619 / 5120) ∧
    -Real.log (2619 / 5120) ≤ (335180937 / 500000000) := by
  have h := checkLog_sound (w := (2501 / 7739)) (n := 12)
    (lo := (670361873 / 1000000000)) (hi := (335180937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2619) = 1/(2619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-335180937 / 500000000) (-670361873 / 1000000000) (Real.log (2619 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (397359429 / 1000000000) ≤ -Real.log (2560 / 3809) ∧
    -Real.log (2560 / 3809) ≤ (39735943 / 100000000) := by
  have h := checkLog_sound (w := (1249 / 6369)) (n := 12)
    (lo := (397359429 / 1000000000)) (hi := (39735943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3809 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3809 / 2560) = 1/(2560 / 3809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (397359429 / 1000000000) (39735943 / 100000000) (Real.log (3809 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3809 / 2560) = -Real.log (2560 / 3809) := by
    rw [show ((3809 / 2560) : ℝ) = ((2560 / 3809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (669217053 / 1000000000) ≤ -Real.log (1311 / 2560) ∧
    -Real.log (1311 / 2560) ≤ (334608527 / 500000000) := by
  have h := checkLog_sound (w := (1249 / 3871)) (n := 12)
    (lo := (669217053 / 1000000000)) (hi := (334608527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1311) = 1/(1311 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-334608527 / 500000000) (-669217053 / 1000000000) (Real.log (1311 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74803827 / 250000000) ≤ -Real.log (625 / 843) ∧
    -Real.log (625 / 843) ≤ (299215309 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 734)) (n := 12)
    (lo := (74803827 / 250000000)) (hi := (299215309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 625) = 1/(625 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74803827 / 250000000) (299215309 / 1000000000) (Real.log (843 / 625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (843 / 625) = -Real.log (625 / 843) := by
    rw [show ((843 / 625) : ℝ) = ((625 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13404327 / 31250000) ≤ -Real.log (407 / 625) ∧
    -Real.log (407 / 625) ≤ (85787693 / 200000000) := by
  have h := checkLog_sound (w := (109 / 516)) (n := 12)
    (lo := (13404327 / 31250000)) (hi := (85787693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 407) = 1/(407 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-85787693 / 200000000) (-13404327 / 31250000) (Real.log (407 / 625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (748837 / 2500000) ≤ -Real.log (1000000 / 1349231) ∧
    -Real.log (1000000 / 1349231) ≤ (299534801 / 1000000000) := by
  have h := checkLog_sound (w := (349231 / 2349231)) (n := 12)
    (lo := (748837 / 2500000)) (hi := (299534801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349231 / 1000000) = 1/(1000000 / 1349231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (748837 / 2500000) (299534801 / 1000000000) (Real.log (1349231 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1349231 / 1000000) = -Real.log (1000000 / 1349231) := by
    rw [show ((1349231 / 1000000) : ℝ) = ((1000000 / 1349231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (214800269 / 500000000) ≤ -Real.log (650769 / 1000000) ∧
    -Real.log (650769 / 1000000) ≤ (429600539 / 1000000000) := by
  have h := checkLog_sound (w := (349231 / 1650769)) (n := 12)
    (lo := (214800269 / 500000000)) (hi := (429600539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 650769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 650769) = 1/(650769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-429600539 / 1000000000) (-214800269 / 500000000) (Real.log (650769 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (227319619 / 1000000000) ≤ -Real.log (1000000 / 1255231) ∧
    -Real.log (1000000 / 1255231) ≤ (11365981 / 50000000) := by
  have h := checkLog_sound (w := (255231 / 2255231)) (n := 12)
    (lo := (227319619 / 1000000000)) (hi := (11365981 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255231 / 1000000) = 1/(1000000 / 1255231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (227319619 / 1000000000) (11365981 / 50000000) (Real.log (1255231 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1255231 / 1000000) = -Real.log (1000000 / 1255231) := by
    rw [show ((1255231 / 1000000) : ℝ) = ((1000000 / 1255231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (11787247 / 40000000) ≤ -Real.log (744769 / 1000000) ∧
    -Real.log (744769 / 1000000) ≤ (36835147 / 125000000) := by
  have h := checkLog_sound (w := (255231 / 1744769)) (n := 12)
    (lo := (11787247 / 40000000)) (hi := (36835147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744769) = 1/(744769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-36835147 / 125000000) (-11787247 / 40000000) (Real.log (744769 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (227588059 / 1000000000) ≤ -Real.log (62500 / 78473) ∧
    -Real.log (62500 / 78473) ≤ (11379403 / 50000000) := by
  have h := checkLog_sound (w := (15973 / 140973)) (n := 12)
    (lo := (227588059 / 1000000000)) (hi := (11379403 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78473 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78473 / 62500) = 1/(62500 / 78473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (227588059 / 1000000000) (11379403 / 50000000) (Real.log (78473 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78473 / 62500) = -Real.log (62500 / 78473) := by
    rw [show ((78473 / 62500) : ℝ) = ((62500 / 78473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (295133767 / 1000000000) ≤ -Real.log (46527 / 62500) ∧
    -Real.log (46527 / 62500) ≤ (36891721 / 125000000) := by
  have h := checkLog_sound (w := (15973 / 109027)) (n := 12)
    (lo := (295133767 / 1000000000)) (hi := (36891721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46527) = 1/(46527 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-36891721 / 125000000) (-295133767 / 1000000000) (Real.log (46527 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (728153771 / 1000000000) ≤ -Real.log (250000000000 / 517813267813) ∧
    -Real.log (250000000000 / 517813267813) ≤ (728153773 / 1000000000) := by
  have h := checkLog_sound (w := (17813267813 / 1017813267813)) (n := 12)
    (lo := (35006591 / 1000000000)) (hi := (273489 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517813267813 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(517813267813 / 500000000000) = 1/(250000000000 / 517813267813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (728153771 / 1000000000) (728153773 / 1000000000) (Real.log (517813267813 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (517813267813 / 250000000000) = -Real.log (250000000000 / 517813267813) := by
    rw [show ((517813267813 / 250000000000) : ℝ) = ((250000000000 / 517813267813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (364567669 / 500000000) ≤ -Real.log (250000000000 / 518321785457) ∧
    -Real.log (250000000000 / 518321785457) ≤ (36456767 / 50000000) := by
  have h := checkLog_sound (w := (18321785457 / 1018321785457)) (n := 12)
    (lo := (17994079 / 500000000)) (hi := (35988159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518321785457 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518321785457 / 500000000000) = 1/(250000000000 / 518321785457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (364567669 / 500000000) (36456767 / 50000000) (Real.log (518321785457 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (518321785457 / 250000000000) = -Real.log (250000000000 / 518321785457) := by
    rw [show ((518321785457 / 250000000000) : ℝ) = ((250000000000 / 518321785457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (104400159 / 200000000) ≤ -Real.log (62500000000 / 105337275719) ∧
    -Real.log (62500000000 / 105337275719) ≤ (130500199 / 250000000) := by
  have h := checkLog_sound (w := (42837275719 / 167837275719)) (n := 12)
    (lo := (104400159 / 200000000)) (hi := (130500199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105337275719 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105337275719 / 62500000000) = 1/(62500000000 / 105337275719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (104400159 / 200000000) (130500199 / 250000000) (Real.log (105337275719 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (105337275719 / 62500000000) = -Real.log (62500000000 / 105337275719) := by
    rw [show ((105337275719 / 62500000000) : ℝ) = ((62500000000 / 105337275719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (522721827 / 1000000000) ≤ -Real.log (100000000000 / 168661207471) ∧
    -Real.log (100000000000 / 168661207471) ≤ (130680457 / 250000000) := by
  have h := checkLog_sound (w := (68661207471 / 268661207471)) (n := 12)
    (lo := (522721827 / 1000000000)) (hi := (130680457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168661207471 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168661207471 / 100000000000) = 1/(100000000000 / 168661207471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (522721827 / 1000000000) (130680457 / 250000000) (Real.log (168661207471 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (168661207471 / 100000000000) = -Real.log (100000000000 / 168661207471) := by
    rw [show ((168661207471 / 100000000000) : ℝ) = ((100000000000 / 168661207471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0323

end


